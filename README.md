# Fibonacci-Sum Permutations (Layman's Conjecture / Hajnal Conjecture 1)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490757.svg)](https://doi.org/10.5281/zenodo.24490757)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization proving that a unique
permutation $p$ of $\{1, \dots, k\}$ has every $i + p(i)$ a Fibonacci number
if and only if $k$ belongs to Layman's sequence $w(n) = \lfloor F_{n+3}/\sqrt{5} \rfloor$.

Coverage by this package's Palomar comparison: of the 7 main results of the [companion paper](https://mathdiscoveries.org/results/fibonacci-sum-permutations), 3 are compared in Lean in full (43%; Theorems 1 and 7 and Corollary 2) and 1 in part (Theorem 6: $a(w_n) = 1$, without its clause that no valid permutation has a sum $F_{n+1}$). Propositions 3 and 4 and Theorem 5, with the full Theorem 6, are proved in this package's Lean library but not compared; Conjecture 8 is open and not counted. Abstract claims: 3 of 6 compared in full (50%), 1 in part, 2 proved in the library but not compared.

AI research agents built and directed by Tyler B. Hughes generated and checked this work. No human mathematician has yet refereed the proof.

## Build & Verify

```bash
lake build Challenge Solution FibSumPerm
lake env lean FibSumPerm/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
