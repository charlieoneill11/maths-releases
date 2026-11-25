"""List scalar subgroups on K and make exact integral tests for their orbit shapes."""
import argparse
from pathlib import Path


def closure(gens):
    group = {(1, 1)}
    frontier = list(group)
    while frontier:
        a, b = frontier.pop()
        for u, v in gens:
            pair = a*u % 7, b*v % 19
            if pair not in group:
                frontier.append(pair)
                group.add(pair)
    return frozenset(group)


def subgroups():
    units = [(a,b) for a in range(1,7) for b in range(1,19)]
    identity = closure([])
    groups = {identity: ()}
    frontier = [identity]
    while frontier:
        group = frontier.pop()
        for u in units:
            if u in group:
                continue
            gen = groups[group] + (u,)
            larger = closure(gen)
            if larger not in groups:
                groups[larger] = gen
                frontier.append(larger)
    return groups


def orbits(group):
    labels = [-1]*133
    partition = []
    for g in range(133):
        if labels[g] >= 0:
            continue
        i, j = divmod(g, 19)
        orbit = sorted({(i*a%7)*19+(j*b%19) for a,b in group})
        for k in orbit:
            labels[k] = len(partition)
        partition.append(orbit)
    return labels, partition


def shapes(max_orbits):
    result = []
    for group, generators in subgroups().items():
        labels, partition = orbits(group)
        if len(partition) > max_orbits:
            continue
        # If a coordinate can be multiplied transitively while all other
        # coordinates stay fixed, a nontrivial axial Fourier slice has
        # magnitude at most two per fibre. Its required energy is too high.
        if sum(b == 1 for a,b in group) == 6 or sum(a == 1 for a,b in group) == 18:
            continue
        result.append((len(partition), sorted(group), generators, labels, partition))
    return sorted(result)


def prepare(shape):
    import numpy as np
    from rayleigh import coefficients
    n, group, generators, labels, partition = shape
    unit_orbits = {o[0]: i for i,o in enumerate(partition)}
    reps = []
    for g in unit_orbits:
        i,j = divmod(g,19)
        other = labels[(-i%7)*19 + (-j%19)]
        if labels[g] <= other:
            reps.append(g)

    # A rounded character merely selects an integer test vector w. For a
    # convolution operator C, |w* C w|^2 <= ||C||^2 (w* w)^2 exactly.
    # The proof holds for any integer vector chosen by this initial rounding.
    real,imaginary,norms=coefficients(np.array(labels).reshape(7,19),[divmod(g,19) for g in reps[1:]])
    tests=[[int(norms[i])]+real[:,i].tolist()+imaginary[:,i].tolist() for i in range(len(norms))]

    matrices = []
    for g in reps:
        x,y = divmod(g,19)
        matrix = [0]*(n*n)
        for i in range(7):
            for j in range(19):
                u = labels[19*i+j]
                v = labels[19*((i+x)%7)+(j+y)%19]
                matrix[n*u+v] += 1
        matrices.append(matrix)
    return [[n,len(reps)],labels,[len(q) for q in partition],reps] + tests + matrices


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-orbits", type=int, default=12)
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    for index,shape in enumerate(shapes(args.max_orbits)):
        n, group, generators, labels, partition = shape
        print(index,n,len(group),generators)
        if args.directory:
            args.directory.mkdir(parents=True, exist_ok=True)
            data = prepare(shape)
            (args.directory/f"k-{index}.txt").write_text(
                "".join(" ".join(map(str,line))+"\n" for line in data))


if __name__ == "__main__":
    main()
