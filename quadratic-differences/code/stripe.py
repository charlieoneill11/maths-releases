"""Check the forcing data for a 57-row square-difference stripe."""

from itertools import chain

HEIGHT = 57
COLOURS = set(range(4))


def neighbours(height):
    return [{row + sign * d * d
             for sign in (-1, 1) for d in range(1, 8)
             if 0 <= row + sign * d * d < height}
            for row in range(height)]


def square_words(height=HEIGHT):
    # Rows 0 and 1 are adjacent. Normalize their colours and also normalize
    # the two remaining names by their first occurrence in the completed word.
    adjacent = neighbours(height)
    assigned = [-1] * height
    assigned[:2] = [0, 1]

    def visit(left):
        if not left:
            names = list(dict.fromkeys(assigned))
            yield tuple(names.index(colour) for colour in assigned)
            return
        domains = {v: COLOURS - {assigned[h] for h in adjacent[v]} for v in left}
        v = min(left, key=lambda i: (len(domains[i]), -len(adjacent[i]), i))
        for colour in domains[v]:
            assigned[v] = colour
            yield from visit(left - {v})
        assigned[v] = -1

    return set(visit(set(range(2, height))))


def main():
    words = square_words()
    allowed = [set(row) for row in zip(*words)]
    if len(words) != 4 or len(allowed) != HEIGHT:
        raise ValueError("unexpected normalized pure-square words")
    variable = {i for i in range(HEIGHT) if len(allowed[i]) > 1}
    if variable != {19, 28, 37}:
        raise ValueError("unexpected variable rows")
    adjacent = neighbours(HEIGHT)
    for i in range(HEIGHT):
        forced_neighbours = set(chain.from_iterable(
            allowed[j] for j in adjacent[i] if len(allowed[j]) == 1))
        if not COLOURS - forced_neighbours <= allowed[i]:
            raise ValueError(f"forward induction fails at row {i}")
    bottom = [allowed[d * d - 1] for d in range(1, 8)]
    if any(len(s) != 1 for s in bottom) or set.union(*bottom) != COLOURS:
        raise ValueError("new lower row could be coloured")
    print("4 normalized words; 54 forced rows; all four colours at the new lower row")


if __name__ == "__main__":
    main()
