"""Check the 48/5 tripod obstruction, including a positive control."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations, combinations_with_replacement, permutations
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


def schedules():
    """Rotate a deficient five-slot window to the origin."""
    for a, b in combinations_with_replacement(range(48), 2):
        defects = (0, a, b)
        canonical = min(tuple(sorted((x - z) % 48 for x in defects)) for z in defects)
        if defects != canonical:
            continue
        windows = [6 - defects.count(i) for i in range(48)]
        sizes = [0] * 48
        for i in range(47):
            j = (5 * i) % 48
            sizes[(j + 5) % 48] = sizes[j] + windows[(j + 1) % 48] - windows[j]
        offset, remainder = divmod(57 - sum(sizes), 48)
        sizes = [n + offset for n in sizes]
        if remainder or min(sizes) < 0:
            continue
        assert all(sum(sizes[(i+k) % 48] for k in range(5)) == windows[i] for i in range(48))
        missing = {i for i, n in enumerate(sizes) if not n}
        if fits_star(missing):
            yield defects, sizes, missing


def gaps(colours, period):
    ordered = sorted(colours)
    if len(ordered) == 1:
        return (period,)
    return tuple((b-a) % period for a, b in zip(ordered, ordered[1:] + ordered[:1]))


def fits_star(colours):
    """Each arc of h slots supports at most floor(h/5) star gaps."""
    if not colours:
        return True
    lengths = gaps(colours, 48)
    return min(lengths) >= 5 and sum(h // 5 for h in lengths) >= 9


def explicit_hub_palettes():
    palettes = set()
    for extras in combinations_with_replacement(range(9), 3):
        marked = [0]
        for i in range(8):
            marked.append(marked[-1] + 5 + extras.count(i))
        for shift in range(48):
            palettes.add(frozenset((c + shift) % 48 for c in marked))
    assert len(palettes) == 880
    return palettes


def terminal_jobs(sizes, missing, triples):
    transforms = [(sign, shift) for sign in (1, -1) for shift in range(48)
                  if all(sizes[i] == sizes[(sign*i + shift) % 48] for i in range(48))]
    for triple in triples:
        if missing and not fits_star(missing.union(triple)):
            continue
        for z in missing.difference(triple):
            image = [19*((c-z) % 48)//48 for c in triple]
            if sorted(gaps(image, 19)) not in ([5, 7, 7], [6, 6, 7]):
                break
        else:
            for placement in permutations(triple):
                orbit = (tuple((sign*c+shift) % 48 for c in ordering)
                         for sign, shift in transforms
                         for ordering in (placement, placement[::-1]))
                if placement == min(orbit):
                    yield placement


def read_core(file):
    data = json.loads(file.read_text())
    roots = data['roots']
    edges = {tuple(e) for row in data['classes'] for e in row}
    flip = [7,6,5,4,3,2,1,0,12,9,10,11,8]
    assert sorted(flip) == list(range(13))
    assert {tuple(sorted((flip[v],flip[w]))) for v,w in edges} == edges
    assert [flip[v] for v in roots] == roots[::-1]
    assert len(edges) == 57
    return roots, sorted(edges), data['classes']


def write_jobs(directory, corefile, workers, cross_check=False):
    roots, edges, classes = read_core(corefile)
    graph = directory / 'core.txt'
    graph.write_text('0 ' + ' '.join(map(str, roots)) + '\n' +
                     ''.join(f'{v} {w}\n' for v,w in edges))
    triples = [t for t in combinations(range(48), 3) if fits_star(t) and max(gaps(t,48)) >= 20]
    palettes = explicit_hub_palettes() if cross_check else None
    rows = list(schedules())
    assert len(rows) == 154
    schedule_file = directory / 'schedules.txt'
    positive = [0]*48
    for fine, row in enumerate(classes):
        positive[48*fine//19] = len(row)
    positive_defects = [i for i in range(48)
                        for _ in range(6-sum(positive[(i+k)%48] for k in range(5)))]
    assert len(positive_defects) == 3
    control = directory / 'control.txt'
    control.write_text(' '.join(map(str,positive_defects + positive))+'\n')
    inputs = [directory / f'cases-{i}.txt' for i in range(workers)]
    streams = [path.open('w') for path in inputs]
    counts = Counter()
    case_digest = sha256()
    try:
        with schedule_file.open('w') as out:
            for j, (defects, sizes, missing) in enumerate(rows):
                print(*defects, *sizes, file=out)
                if palettes is not None:
                    by_palette = {tuple(sorted(t)) for star in palettes if missing <= star
                                  for t in combinations(star, 3) if max(gaps(t,48)) >= 20}
                    by_gaps = {t for t in triples if fits_star(missing.union(t))}
                    assert by_palette == by_gaps
                for n,t in enumerate(terminal_jobs(sizes, missing, triples)):
                    line = " ".join(map(str, (j, *t))) + "\n"
                    case_digest.update(line.encode("ascii"))
                    streams[(j+n) % workers].write(line)
                    counts[(j+n) % workers] += 1
    finally:
        for stream in streams:
            stream.close()
    assert sum(counts.values()) == 221975
    assert case_digest.hexdigest() == "478751878fdc7ac88c8a0cdd9bf084668286089a43485417b9d67564e398563c"
    assert sha256(schedule_file.read_bytes()).hexdigest() == "b20fccb297f501979097a8401fa432ce926e21bd34f8ecc1ada2d75c454585cc"
    return graph, schedule_file, control, inputs, counts


def run(checker, graph, schedule, data, expected):
    result = subprocess.run([checker,graph,schedule],stdin=data,capture_output=True,
                            text=True,check=True)
    last = result.stdout.splitlines()[-1].split()
    if last[:4] != ['checked',str(expected),'feasible','0']:
        raise RuntimeError(result.stdout)
    return int(last[-1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    parser.add_argument('--cross-check-cases', action='store_true',
                        help='also exhaust the 880 hub palettes for every schedule')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--emit', type=Path, help='retain the generated instance and case files')
    parser.add_argument('--core', type=Path, default=Path(__file__).with_name('tripod.json'))
    args = parser.parse_args()
    if args.jobs < 1 or not (args.checker or args.emit):
        parser.error('use --checker or --emit and a positive worker count')
    with TemporaryDirectory() as tmp:
        directory = args.emit or Path(tmp)
        directory.mkdir(parents=True,exist_ok=True)
        graph, schedules, control, inputs, counts = write_jobs(directory,args.core,args.jobs,args.cross_check_cases)
        print(f'154 schedules, {sum(counts.values())} terminal placements.',flush=True)
        if args.checker:
            checker = args.checker.resolve()
            check = subprocess.run([checker,graph,control],input='0 0 15 30\n',text=True,
                                   check=True,capture_output=True)
            assert 'checked 1 feasible 1' in check.stdout
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                def check_file(i):
                    with inputs[i].open() as stream:
                        return run(checker,graph,schedules,stream,counts[i])
                leaves = sum(pool.map(check_file,range(args.jobs)))
            print(f'Positive control passed. All 221975 bad placements excluded. '
                  f'{leaves} complete palette assignments required edge checking.')


if __name__ == '__main__':
    main()
