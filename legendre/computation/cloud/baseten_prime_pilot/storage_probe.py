"""Measure an authenticated HTTPS object PUT and a checksum-verified retrieval."""
import argparse
import hashlib
from http.client import HTTPException
import json
import os
import tempfile
import time
from pathlib import Path
from urllib import error, parse, request


def make_fixture(sample, output, desired_bytes):
    size = sample.stat().st_size
    if size == 0:
        raise ValueError("Empty sample file")
    with sample.open("rb") as source, output.open("wb") as target:
        remaining = desired_bytes
        while remaining:
            data = source.read(min(1 << 20, remaining))
            if not data:
                source.seek(0)
                continue
            target.write(data)
            remaining -= len(data)


def checksum(stream):
    digest = hashlib.sha256()
    size = 0
    while chunk := stream.read(1 << 20):
        size += len(chunk)
        digest.update(chunk)
    return size, digest.hexdigest()


def measure(path, put_url, get_url, opener=request.urlopen):
    if any(parse.urlsplit(url).scheme != "https" for url in (put_url, get_url)):
        raise ValueError("Both object URLs must use HTTPS")
    with path.open("rb") as data:
        size, expected = checksum(data)
        data.seek(0)
        put = request.Request(put_url, method="PUT", data=data,
                              headers={"Content-Length":str(size)})
        start = time.perf_counter()
        with opener(put, timeout=300) as reply:
            if not 200 <= reply.status < 300:
                raise ValueError("Object store rejected the upload")
            reply.read()
        upload = time.perf_counter() - start
    start = time.perf_counter()
    with opener(request.Request(get_url, method="GET"), timeout=300) as reply:
        if reply.status != 200:
            raise ValueError("Object store did not return the full object")
        returned = checksum(reply)
    retrieval = time.perf_counter() - start
    if returned != (size, expected):
        raise ValueError("Object size or recovered SHA-256 does not match")
    return dict(bytes=size, sha256=expected, put_seconds=upload, get_verify_seconds=retrieval,
                put_MB_s=size/1e6/upload, get_verify_MB_s=size/1e6/retrieval)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sample", type=Path)
    parser.add_argument("--mib", type=int, default=64)
    args = parser.parse_args()
    if not 1 <= args.mib <= 1024:
        parser.error("Choose a fixture size of 1 to 1024 MiB")
    try:
        put_url = os.environ["PILOT_PUT_URL"]
        get_url = os.environ["PILOT_GET_URL"]
        with tempfile.TemporaryDirectory(dir=os.environ.get("BT_SCRATCH_DIR")) as work:
            fixture = Path(work) / "fixture"
            make_fixture(args.sample, fixture, args.mib << 20)
            print(json.dumps(measure(fixture, put_url, get_url), indent=2))
    except error.HTTPError as exc:
        parser.exit(1, f"Object store returned HTTP {exc.code}\n")
    except error.URLError:
        parser.exit(1, "Object store connection failed\n")
    except KeyError:
        parser.exit(1, "Supply both signed URLs through the environment\n")
    except (HTTPException, OSError, ValueError):
        parser.exit(1, "Object store probe or checksum verification failed\n")
