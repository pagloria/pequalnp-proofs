"""Search an explicit neighborhood of the star-cover upper bound for L-meta-1884."""

from collections import Counter
from itertools import combinations, product
from math import comb


EDGES = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
MASKS = [sum(((row >> bit) & 1) << row for row in range(1024)) for bit in range(10)]
MASKS.append(((1 << 1024) - 1) ^ MASKS[0])
TARGET = 0
for left, right in EDGES:
    TARGET |= MASKS[left] & MASKS[right]


def minimum_covers():
    for size in range(11):
        covers = [set(xs) for xs in combinations(range(10), size)
                  if all(left in xs or right in xs for left, right in EDGES)]
        if covers:
            return size, covers


def templates(cover):
    choices = [tuple(v for v in e if v in cover) for e in EDGES]
    for owners in product(*choices):
        groups = {v: [] for v in sorted(cover)}
        for (left, right), owner in zip(EDGES, owners):
            groups[owner].append(right if owner == left else left)
        gates = []

        def gate(kind, left, right):
            gates.append((kind, left, right))
            return len(MASKS) + len(gates) - 1

        def disjoin(wires):
            result, *rest = wires
            for wire in rest:
                result = gate("or", result, wire)
            return result

        stars = [gate("and", center, disjoin(sorted(neighbors)))
                 for center, neighbors in groups.items()]
        disjoin(stars)
        yield gates


def evaluate_gate(g, wires):
    kind, left, right = g
    if kind == "and":
        return wires[left] & wires[right]
    return wires[left] | wires[right]


def search(gates):
    # Replacing a gate by an earlier wire removes one gate, with all fan-outs
    # redirected. The extra uncharged wire carries NOT of input zero.
    original = MASKS.copy()
    for g in gates:
        original.append(evaluate_gate(g, original))
    assert len(gates) == 20 and original[-1] == TARGET
    counts = Counter()
    best = [1025, 1025]
    for first in range(len(gates)):
        first_index = len(MASKS) + first
        for src1 in range(first_index):
            changed = original[:first_index]
            changed.append(changed[src1])
            for g in gates[first + 1:]:
                changed.append(evaluate_gate(g, changed))
            dist = (TARGET ^ changed[-1]).bit_count()
            counts[1] += 1
            best[0] = min(best[0], dist)
            for second in range(first + 1, len(gates)):
                second_index = len(MASKS) + second
                for src2 in range(second_index):
                    # The first bypass wire is an alias. Keep its original name
                    # too, so the search count has a simple independent check.
                    candidate = changed[:second_index]
                    candidate.append(candidate[src2])
                    for g in gates[second + 1:]:
                        candidate.append(evaluate_gate(g, candidate))
                    dist = (TARGET ^ candidate[-1]).bit_count()
                    counts[2] += 1
                    best[1] = min(best[1], dist)
                    if dist == 0:
                        print("18-gate witness", gates, first, src1, second, src2, flush=True)
                        return counts, best
    starts = range(len(MASKS), len(MASKS) + len(gates))
    assert counts[1] == sum(starts)
    assert counts[2] == sum(x * y for x, y in combinations(starts, 2))
    return counts, best


def main():
    size, covers = minimum_covers()
    assert len(EDGES) == 15 and size == 6 and len(covers) == 5
    assert sum(comb(10, k) for k in range(11)) == 1024
    print(f"Minimum vertex cover: {size}; {len(covers)} such covers; 15 edges", flush=True)
    total = Counter()
    best = [1025, 1025]
    num_templates = 0
    for cover in covers:
        for gates in templates(cover):
            n, errors = search(gates)
            total.update(n)
            num_templates += 1
            best = list(map(min, best, errors))
            if best[1] == 0:
                return
    print(f"Templates: {num_templates}; one bypass: {total[1]}; two bypasses: {total[2]}")
    print(f"Smallest numbers of errors over 1024 rows: {best}", flush=True)


if __name__ == "__main__":
    main()
