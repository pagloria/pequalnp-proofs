# Petersen edge detection at 18 gates

These calculations concern the [P vs NP desk task L-meta-1884](https://pequalnp.com/desk/step?gap=L-meta-1884). The target is true exactly when two selected vertices form an edge of the Petersen graph. The task allows ten reindexed inputs, one extra input carrying a unary Boolean function of vertex zero, and a circuit of at most eighteen gates. The full lower bound for circuits with arbitrary gate sharing and negation remains open.

## Verified with Lean 4.36.0

- **A formula class has exact size 20.** Consider an OR of terms of the form `(OR of A) AND (OR of B)`, with nonempty sets of positive inputs on each side. Each disjunction uses its own binary tree. Since the graph has no four-cycle, each sound term has a singleton on one side. Its edges therefore form a star. Covering the fifteen edges takes at least fifteen leaf occurrences, and the star centers give a vertex cover of size at least six. Combining the terms gives a lower bound of twenty gates. A six-term formula computes the target with exactly twenty. The Lean theorems are `formulaLowerBound`, `exampleCost`, and `exampleCorrect`. [Proof](PetersenStars.lean)
- **Every vertex must be distinguishable at the inputs.** If the ten reindexed positions omit a vertex, it must be vertex zero and the extra unary wire must distinguish false from true. The proof constructs two assignments with the same wires and opposite answers whenever this condition fails. It applies to any decoder, at any gate budget. [Proof](PetersenInput.lean)

## An exhaustive search within a family of rewrites

The search enumerates all five minimum vertex covers and all eight ways per cover of assigning each edge to one of its endpoints in that cover. It builds a twenty-gate formula in a fixed order for each of the forty assignments. A rewrite bypasses one or two gates and redirects all uses to earlier wires. The earlier wires include a free complement of vertex zero. Each candidate is evaluated on all 1,024 input assignments.

| Bypassed gates | Wiring choices tested | Fewest incorrect outputs |
| --- | ---: | ---: |
| One | 16,400 | 9 |
| Two | 3,180,600 | 17 |

The counts include distinct rewrite choices that produce the same circuit. They cover the forty starting formulas and the specified rewrites. [Search program](search_petersen.py)

## Reproduction

The project pins Lean and Mathlib in `lean/`. From that directory, with the pinned dependencies installed, run the following commands. The search requires only the Python standard library.

```sh
lake build +PEqualNP.Defs.CircuitLowerBounds
lake env lean ../notes/petersen-1884/PetersenInput.lean
lake env lean ../notes/petersen-1884/PetersenStars.lean
python ../notes/petersen-1884/search_petersen.py
```
