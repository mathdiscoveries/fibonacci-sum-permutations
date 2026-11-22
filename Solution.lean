module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import FibSumPerm

@[expose] public section

namespace FibSumPermChallenge

def IsFib (m : ℕ) : Prop :=
  0 < m ∧ ∃ j : ℕ, Nat.fib j = m

def IsValidFibPerm (k : ℕ) (p : Equiv.Perm (Fin k)) : Prop :=
  ∀ i : Fin k, IsFib ((i.1 + 1) + ((p i).1 + 1))

noncomputable def fibPermCount (k : ℕ) : ℕ := by
  classical
  exact Fintype.card { p : Equiv.Perm (Fin k) // IsValidFibPerm k p }

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

private theorem fibPermCount_eq (k : ℕ) : fibPermCount k = FibSumPerm.fibPermCount k := by
  unfold fibPermCount FibSumPerm.fibPermCount
  classical
  exact Fintype.card_congr (Equiv.refl _)

private theorem w_eq (n : ℕ) : w n = FibSumPerm.w n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | m + 3 =>
      simp only [w, FibSumPerm.w]
      rw [ih (m + 1) (by omega)]

private theorem M4_eq (k : ℕ) : M4 k = FibSumPerm.M4 k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | m + 4 =>
      simp only [M4, FibSumPerm.M4]
      rw [ih m (by omega)]

theorem layman_unique_if (n : ℕ) (hn : 1 ≤ n) : fibPermCount (w n) = 1 := by
  rw [fibPermCount_eq, w_eq]
  exact FibSumPerm.layman_unique_if n hn

theorem hajnal_conjecture_1 (k : ℕ) (hk : 1 ≤ k) :
    fibPermCount k = 1 ↔ ∃ n : ℕ, 1 ≤ n ∧ k = w n := by
  rw [fibPermCount_eq]
  simpa [w_eq] using FibSumPerm.hajnal_conjecture_1 k hk

theorem hajnal_conjecture_1_M4 (k : ℕ) (hk : 1 ≤ k) :
    fibPermCount k = 1 ↔ ∃ l : ℕ, 2 ≤ l ∧ k = M4 l := by
  rw [fibPermCount_eq]
  simpa [M4_eq] using FibSumPerm.hajnal_conjecture_1_M4 k hk

theorem w_eq_floor_fib_div_sqrt5 (n : ℕ) (hn : 1 ≤ n) :
    (w n : ℤ) = ⌊(Nat.fib (n + 3) : ℝ) / Real.sqrt 5⌋ := by
  rw [w_eq]
  exact FibSumPerm.w_eq_floor_fib_div_sqrt5 n hn

end FibSumPermChallenge
