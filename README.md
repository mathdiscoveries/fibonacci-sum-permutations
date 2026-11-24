# Fibonacci-Sum Permutations (Layman's Conjecture / Hajnal Conjecture 1)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490757.svg)](https://doi.org/10.5281/zenodo.24490757)

Unconditional Lean 4 (`v4.35.0`) + Mathlib formalization proving that a unique
permutation $p$ of $\{1, \dots, k\}$ has every $i + p(i)$ a Fibonacci number
if and only if $k$ belongs to Layman's sequence $w(n) = \lfloor F_{n+3}/\sqrt{5} \rfloor$.

## Build & Verify

```bash
lake build Challenge Solution FibSumPerm
lake env lean FibSumPerm/Verify.lean
lake comparator --paranoid --inadvisably-no-sandbox
```
