"""Combine repeated exact joins over the same sets of compressed row types."""
from collections import defaultdict
from itertools import product

import numpy as np


class Buckets:
    def __init__(self, units):
        self.units = units
        self.parts = []
        self.index = {}
        self.sizes = []
        self.expanded = {}

    def intern(self, indices):
        key = tuple(sorted(indices))
        if key not in self.index:
            self.index[key] = len(self.parts)
            self.parts.append(key)
            self.sizes.append(sum(len(self.units[i][1]) for i in key))
        return self.index[key]

    def data(self, key):
        if key not in self.expanded:
            self.expanded[key] = np.concatenate([self.units[i][1] for i in self.parts[key]])
        return self.expanded[key]

    def by_power(self, tables, needed):
        reverse = []
        for table, keys in zip(tables, needed):
            by_type = defaultdict(list)
            for key in keys:
                for row_type in table[key]:
                    by_type[row_type].append(key)
            reverse.append(by_type)
        by_pair = defaultdict(list)
        for i, (kind, _) in enumerate(self.units):
            for pair in product(reverse[0].get(kind[:3], ()), reverse[1].get(kind[3:], ())):
                by_pair[pair].append(i)
        return {pair: self.intern(parts) for pair, parts in by_pair.items()}


def pair_work(job, buckets):
    a, b, c, d = sorted(column.sizes[key] for column, key in zip(buckets, job))
    return a*d + b*c


def combine(jobs, buckets):
    # Holding three coordinates fixed lets us replace all fourth-coordinate
    # lists by their union without adding or dropping any ordered quadruple.
    previous = len(jobs) + 1
    while len(jobs) < previous:
        previous = len(jobs)
        for i, column in enumerate(buckets):
            groups = defaultdict(list)
            for job in jobs:
                groups[job[:i] + job[i+1:]].append(job[i])
            merged = set()
            for fixed, options in groups.items():
                if len(options) == 1:
                    key = options[0]
                else:
                    key = column.intern(set().union(*(column.parts[k] for k in options)))
                merged.add(fixed[:i] + (key,) + fixed[i:])
            jobs = merged
    return jobs


def build(units, plans):
    buckets = [Buckets(column) for column in units]
    jobs = set()
    raw = repeats = 0
    for by_prime, viable in plans:
        columns = []
        for i, column in enumerate(buckets):
            used = [{x[i] for x in patterns} for patterns in viable]
            columns.append(column.by_power([g[i] for g in by_prime], used))
        for a, b in product(*viable):
            job = tuple(columns[i].get(pair) for i, pair in enumerate(zip(a, b)))
            if None in job:
                continue
            raw += pair_work(job, buckets)
            repeats += 1
            jobs.add(job)
    original = len(jobs)
    jobs = combine(jobs, buckets)
    work = sum(pair_work(job, buckets) for job in jobs)
    print(f"{repeats} projected combinations, {original} distinct jobs, {len(jobs)} after unions; "
          f"{raw} raw pair entries, {work} after unions", flush=True)
    return buckets, sorted(jobs), work
