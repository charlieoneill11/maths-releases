#!/usr/bin/env python3
"""Export queried prefix triples from the release's upper113 exact join."""
from argparse import ArgumentParser
from pathlib import Path
import os
import subprocess
import sys

from generate import PROFILES


def run(args):
    subprocess.run([str(x) for x in args], check=True)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("code", type=Path, help="released code directory containing round25 and round26")
    parser.add_argument("work", type=Path, help="scratch directory for binaries, records and output")
    parser.add_argument("--profiles", nargs="+", choices=PROFILES, default=PROFILES)
    args = parser.parse_args()
    if sys.byteorder != "little":
        parser.error("the release writes host-order binary records and the bitmap reads little-endian records")
    code, work = args.code.resolve(), args.work.resolve()
    work.mkdir(exist_ok=True, parents=True)
    src = code / "round26/upper113"
    atlas = code / "round25/multiplicities/atlas/atlas.tsv"
    join = (src / "join_bands.cpp").read_text()
    hook = '  cerr << "distinct domains "'
    if join.count(hook) != 1 or join.count("argc != 6") != 1:
        parser.error("the join driver does not match the release's extraction points")
    # domainIndex keys store the three individual, disjoint height planes.
    # Reconstruct the two cuts used by BandJoin.Prefix and retain the shared plane.
    dump = '''  ofstream hints(argv[6], ios::binary);
  for (const auto &entry : domainIndex) {
    const auto &k = entry.first;
    Mask out[3] = {k[0] | k[1], k[1] | k[2], k[1]};
    hints.write(reinterpret_cast<const char*>(out), sizeof out);
  }
  hints.close();
  if (!hints) throw runtime_error("could not write prefix hints");
'''
    export = work / "export_prefix.cpp"
    export.write_text(join.replace("argc != 6", "argc != 7").replace(hook, dump + hook))
    for name, source in [("pair_supports", src / "pair_supports.cpp"),
                         ("filter_contacts", src / "filter_contacts.cpp"),
                         ("middle_layers", src / "middle_layers.cpp"),
                         ("export_prefix", export)]:
        run(["c++", "-O3", "-std=c++17", "-march=native", "-I", src, source, "-o", work / name])
    pairs = work / "pairs.bin"
    run([work / "pair_supports", atlas, 33, pairs])
    for profile in args.profiles:
        folder = work / profile
        folder.mkdir(exist_ok=True)
        contacts, middles = work / "contacts.bin", work / "middles.bin"
        run([work / "filter_contacts", atlas, pairs, contacts, profile[1:]])
        run([work / "middle_layers", atlas, contacts, middles])
        run([work / "export_prefix", atlas, middles, os.devnull, 16, 33, folder / "hints.bin"])


if __name__ == "__main__":
    main()
