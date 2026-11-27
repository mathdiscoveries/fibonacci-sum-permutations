module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Palomar Challenge: Uniqueness Characterization of Fibonacci-Sum Permutations (Layman's Conjecture / Hajnal Conjecture 1)

A permutation `p` of `{1, ..., k}` is a Fibonacci-sum permutation when
`i + p(i)` is a positive Fibonacci number for every `i`.

This challenge states the complete characterization: `fibPermCount k = 1` if
and only if `k` belongs to Layman's sequence `w n` (`1, 2, 3, 5, 9, 15, 24,
39, 64, ...`), equivalently Hajnal's `M4` sequence, together with Reshetnikov's
closed-form floor identity `w n = ⌊F_{n+3} / √5⌋`.
-/

@[expose] public section

namespace FibSumPermChallenge

def IsFib (m : ℕ) : Prop :=
  0 < m ∧ ∃ j : ℕ, Nat.fib j = m

def IsValidFibPerm (k : ℕ) (p : Equiv.Perm (Fin k)) : Prop :=
  ∀ i : Fin k, IsFib ((i.1 + 1) + ((p i).1 + 1))

open Classical in
noncomputable def fibPermCount (k : ℕ) : ℕ :=
  Fintype.card { p : Equiv.Perm (Fin k) // IsValidFibPerm k p }

def w : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => Nat.fib (n + 5) - w (n + 1) - 1

def M4 : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => Nat.fib 2
  | 3 => Nat.fib 3
  | k + 4 => Nat.fib (k + 4) + M4 k

theorem layman_unique_if (n : ℕ) (hn : 1 ≤ n) : fibPermCount (w n) = 1 := by
  sorry

theorem hajnal_conjecture_1 (k : ℕ) (hk : 1 ≤ k) :
    fibPermCount k = 1 ↔ ∃ n : ℕ, 1 ≤ n ∧ k = w n := by
  sorry

theorem hajnal_conjecture_1_M4 (k : ℕ) (hk : 1 ≤ k) :
    fibPermCount k = 1 ↔ ∃ l : ℕ, 2 ≤ l ∧ k = M4 l := by
  sorry

theorem w_eq_floor_fib_div_sqrt5 (n : ℕ) (hn : 1 ≤ n) :
    (w n : ℤ) = ⌊(Nat.fib (n + 3) : ℝ) / Real.sqrt 5⌋ := by
  sorry

end FibSumPermChallenge
