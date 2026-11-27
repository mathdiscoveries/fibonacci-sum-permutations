/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Finset.Range

import Mathlib.Tactic

/-!
# Definitions and Fibonacci/Lucas Structure for `FibSumPerm`

Faithful Lean 4 formalization of Fibonacci-sum permutations (Layman 2004 / OEIS A097082,
A097083; Hajnal 2022), Layman's sequence `w`, Hajnal's `M4` sum, exact Fibonacci scale
inequalities for all `n ≥ 1`, and the Lucas/Cassini identities used for Reshetnikov's
floor formula.
-/

@[expose] public section

namespace FibSumPerm

/-- A positive natural number `m` is a Fibonacci number: `m > 0` and `m = Nat.fib j`
for some `j : ℕ`. -/
def IsFib (m : ℕ) : Prop :=
  0 < m ∧ ∃ j : ℕ, Nat.fib j = m

/-- Helper recurrence `Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n`. -/
theorem fib_step (n : ℕ) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  rw [Nat.fib_add_two, Nat.add_comm]

/-- Every Fibonacci number with index `j ≥ 1` is positive. -/
theorem fib_pos_of_pos {j : ℕ} (hj : 1 ≤ j) : 0 < Nat.fib j := by
  cases j with
  | zero => omega
  | succ n => exact Nat.fib_pos.mpr (Nat.succ_pos n)

/-- `Nat.fib j` satisfies `IsFib` whenever `j ≥ 1`. -/
theorem isFib_fib {j : ℕ} (hj : 1 ≤ j) : IsFib (Nat.fib j) :=
  ⟨fib_pos_of_pos hj, j, rfl⟩

/-- Linear lower bound `j - 1 ≤ Nat.fib j` for all `j : ℕ`. -/
theorem fib_ge_sub_one (j : ℕ) : j - 1 ≤ Nat.fib j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => simp
    | 1 => simp
    | 2 => simp [Nat.fib_two]
    | n + 3 =>
      have hstep : Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := fib_step (n + 1)
      have h1 := ih (n + 2) (by omega)
      have hpos : 1 ≤ Nat.fib (n + 1) := fib_pos_of_pos (by omega)
      omega

/-- Bounded characterization of `IsFib` for constructive decidability. -/
theorem isFib_iff_bounded (m : ℕ) :
    IsFib m ↔ 0 < m ∧ ∃ j ∈ Finset.range (m + 2), Nat.fib j = m := by
  constructor
  · rintro ⟨hm, j, rfl⟩
    refine ⟨hm, j, Finset.mem_range.mpr ?_, rfl⟩
    have h := fib_ge_sub_one j
    omega
  · rintro ⟨hm, j, _, hj⟩
    exact ⟨hm, j, hj⟩

instance decidableIsFib (m : ℕ) : Decidable (IsFib m) :=
  decidable_of_iff _ (isFib_iff_bounded m).symm

/-- A permutation `p` of `Fin k` (representing `{1, ..., k}` via `i ↦ i.1 + 1`) is a
valid Fibonacci-sum permutation (Layman permutation) if `(i + 1) + (p i + 1)` is a
positive Fibonacci number for every `i : Fin k`. -/
def IsValidFibPerm (k : ℕ) (p : Equiv.Perm (Fin k)) : Prop :=
  ∀ i : Fin k, IsFib ((i.1 + 1) + ((p i).1 + 1))

instance decidableIsValidFibPerm (k : ℕ) (p : Equiv.Perm (Fin k)) :
    Decidable (IsValidFibPerm k p) :=
  Fintype.decidableForallFintype

/-- Number of valid Fibonacci-sum permutations of `{1, ..., k}` (OEIS A097082). -/
def fibPermCount (k : ℕ) : ℕ :=
  Fintype.card { p : Equiv.Perm (Fin k) // IsValidFibPerm k p }

/-- The inverse of a valid Fibonacci-sum permutation is also valid. -/
theorem IsValidFibPerm.symm {k : ℕ} {p : Equiv.Perm (Fin k)} (hp : IsValidFibPerm k p) :
    IsValidFibPerm k p.symm := by
  intro i
  have h := hp (p.symm i)
  rw [Equiv.apply_symm_apply, Nat.add_comm] at h
  exact h

/-- For `k = 0`, the empty permutation is vacuously valid, so `fibPermCount 0 = 1`. -/
theorem fibPermCount_zero : fibPermCount 0 = 1 := by
  unfold fibPermCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, fun i => Fin.elim0 i⟩, ?_⟩
  rintro ⟨p, _⟩
  ext i
  exact Fin.elim0 i

/-- `Nat.fib` is strictly increasing on indices `≥ 2`. -/
theorem fib_strictMono_from_two {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    Nat.fib a < Nat.fib b := by
  have step : ∀ n, 2 ≤ n → Nat.fib n < Nat.fib (n + 1) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hstep : Nat.fib (2 + m + 1) = Nat.fib (2 + m) + Nat.fib (m + 1) := by
      have := fib_step (m + 1)
      have h1 : m + 1 + 2 = 2 + m + 1 := by omega
      have h2 : m + 1 + 1 = 2 + m := by omega
      rw [h1, h2] at this
      exact this
    have hpos : 0 < Nat.fib (m + 1) := fib_pos_of_pos (by omega)
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ b by omega)
  induction d with
  | zero => simpa using step a ha
  | succ d ih =>
    rw [show a + 1 + (d + 1) = (a + 1 + d) + 1 by omega]
    exact lt_trans (ih (by omega)) (step (a + 1 + d) (by omega))

/-- No Fibonacci number lies strictly between consecutive Fibonacci numbers. -/
theorem not_isFib_between (a m : ℕ) (hm : IsFib m)
    (h1 : Nat.fib a < m) (h2 : m < Nat.fib (a + 1)) : False := by
  rcases hm with ⟨_, j, rfl⟩
  rcases le_or_gt j a with hja | haj
  · have := Nat.fib_mono hja
    omega
  · have hle : a + 1 ≤ j := haj
    have := Nat.fib_mono hle
    omega

/-- Any Fibonacci number strictly between `Nat.fib a` and `Nat.fib (a + 2)` equals
`Nat.fib (a + 1)`. -/
theorem eq_fib_of_isFib_between (a m : ℕ) (hm : IsFib m)
    (h1 : Nat.fib a < m) (h2 : m < Nat.fib (a + 2)) : m = Nat.fib (a + 1) := by
  rcases lt_trichotomy m (Nat.fib (a + 1)) with hlt | heq | hgt
  · exact False.elim (not_isFib_between a m hm h1 hlt)
  · exact heq
  · exact False.elim (not_isFib_between (a + 1) m hm hgt h2)

/-- Every `k ≥ 1` lies in a unique Fibonacci scale `Nat.fib j ≤ 2 * k < Nat.fib (j + 1)`
with `j ≥ 3`. -/
theorem exists_fib_scale {k : ℕ} (hk : 1 ≤ k) :
    ∃ j : ℕ, 3 ≤ j ∧ Nat.fib j ≤ 2 * k ∧ 2 * k < Nat.fib (j + 1) := by
  have hex : ∃ n : ℕ, 2 * k < Nat.fib n := by
    refine ⟨2 * k + 2, ?_⟩
    have h := fib_ge_sub_one (2 * k + 2)
    omega
  set n := Nat.find hex
  have hn_lt : 2 * k < Nat.fib n := Nat.find_spec hex
  have hn_ge4 : 4 ≤ n := by
    by_contra hlt
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · rw [h0] at hn_lt; simp at hn_lt
    · rw [h1] at hn_lt; simp at hn_lt; omega
    · rw [h2] at hn_lt; simp [Nat.fib_two] at hn_lt; omega
    · rw [h3] at hn_lt
      have : Nat.fib 3 = 2 := by decide
      omega
  refine ⟨n - 1, by omega, ?_, ?_⟩
  · have hmin := Nat.find_min hex (show n - 1 < n by omega)
    omega
  · rwa [Nat.sub_add_cancel (by omega)]

/-- Layman's sequence `w` (OEIS A097083): `w 0 = 0`, `w 1 = 1`, `w 2 = 2`,
`w (n + 3) = Nat.fib (n + 5) - w (n + 1) - 1`. -/
def w : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => Nat.fib (n + 5) - w (n + 1) - 1

/-- Hajnal's `M4` sum: `M4 k = F_k + F_{k-4} + ...` for `k ≥ 2` (with `M4 0 = M4 1 = 0`). -/
def M4 : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => Nat.fib 2
  | 3 => Nat.fib 3
  | k + 4 => Nat.fib (k + 4) + M4 k

/-- Core Fibonacci scale inequalities for Layman's sequence `w n` for all `n ≥ 1`. -/
theorem w_bounds (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (n + 1) ≤ w n ∧
    w n + 1 ≤ Nat.fib (n + 2) ∧
    Nat.fib (n + 2) ≤ 2 * w n ∧
    2 * w n < Nat.fib (n + 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 => decide
    | 2 => decide
    | m + 3 =>
      have hm1 : 1 ≤ m + 1 := by omega
      obtain ⟨h1, h2, h3, h4⟩ := ih (m + 1) (by omega) hm1
      simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3 h4 ⊢
      have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 3) + Nat.fib (m + 2) := fib_step (m + 2)
      have hfib5 : Nat.fib (m + 5) = Nat.fib (m + 4) + Nat.fib (m + 3) := fib_step (m + 3)
      have hfib6 : Nat.fib (m + 6) = Nat.fib (m + 5) + Nat.fib (m + 4) := fib_step (m + 4)
      have hpos3 : 1 ≤ Nat.fib (m + 3) := fib_pos_of_pos (by omega)
      have hw : w (m + 3) = Nat.fib (m + 5) - w (m + 1) - 1 := rfl
      omega

/-- Exact recurrence identity `w n + w (n + 2) + 1 = Nat.fib (n + 4)` for all `n : ℕ`. -/
theorem w_add_w_add_one (n : ℕ) : w n + w (n + 2) + 1 = Nat.fib (n + 4) := by
  cases n with
  | zero => decide
  | succ m =>
    have h2 := (w_bounds (m + 1) (by omega)).2.1
    simp only [Nat.add_assoc, Nat.reduceAdd] at h2 ⊢
    have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 3) + Nat.fib (m + 2) := fib_step (m + 2)
    have hfib5 : Nat.fib (m + 5) = Nat.fib (m + 4) + Nat.fib (m + 3) := fib_step (m + 3)
    have hw : w (m + 3) = Nat.fib (m + 5) - w (m + 1) - 1 := rfl
    omega

/-- Period-4 additive identity `w (n + 4) = Nat.fib (n + 5) + w n` for all `n : ℕ`. -/
theorem w_add_four (n : ℕ) : w (n + 4) = Nat.fib (n + 5) + w n := by
  have h1 := w_add_w_add_one n
  have h2 := w_add_w_add_one (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h2
  have hfib : Nat.fib (n + 6) = Nat.fib (n + 5) + Nat.fib (n + 4) := fib_step (n + 4)
  omega

/-- Sharper upper bound `2 * w n + 2 ≤ Nat.fib (n + 3)` for all `n ≥ 3`. -/
theorem two_mul_w_add_two_le (n : ℕ) (hn : 3 ≤ n) : 2 * w n + 2 ≤ Nat.fib (n + 3) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h3 := (w_bounds (m + 1) (by omega)).2.2.1
  have hrec := w_add_w_add_one (m + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h3 hrec
  have hfib5 : Nat.fib (m + 5) = Nat.fib (m + 4) + Nat.fib (m + 3) := fib_step (m + 3)
  have hfib6 : Nat.fib (m + 6) = Nat.fib (m + 5) + Nat.fib (m + 4) := fib_step (m + 4)
  have h1 : 3 + m = m + 3 := by omega
  have h2 : m + 3 + 3 = m + 6 := by omega
  rw [h1, h2]
  omega

/-- Hajnal's `M4 (n + 1)` equals Layman's `w n` for all `n ≥ 1`. -/
theorem M4_eq_w (n : ℕ) (hn : 1 ≤ n) : M4 (n + 1) = w n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | m + 5 =>
      have hM : M4 (m + 6) = Nat.fib (m + 6) + M4 (m + 2) := rfl
      have hih := ih (m + 1) (by omega) (by omega)
      have hw := w_add_four (m + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hih hw ⊢
      rw [hM, hih]
      omega

/-- Lucas numbers `L 0 = 2`, `L 1 = 1`, `L (m + 2) = L (m + 1) + L m`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | m + 2 => lucas (m + 1) + lucas m

/-- Lucas numbers in terms of Fibonacci numbers: `lucas (m + 1) = fib m + fib (m + 2)`. -/
theorem lucas_succ_eq_fib_add_fib (m : ℕ) :
    lucas (m + 1) = Nat.fib m + Nat.fib (m + 2) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      have h1 := ih (k + 1) (by omega)
      have h2 := ih k (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 ⊢
      have hL : lucas (k + 3) = lucas (k + 2) + lucas (k + 1) := rfl
      have hF1 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := fib_step k
      have hF2 : Nat.fib (k + 4) = Nat.fib (k + 3) + Nat.fib (k + 2) := fib_step (k + 2)
      omega

/-- Period-4 Lucas step identity: `lucas (m + 4) = lucas m + 5 * Nat.fib (m + 2)`. -/
theorem lucas_add_four (m : ℕ) : lucas (m + 4) = lucas m + 5 * Nat.fib (m + 2) := by
  cases m with
  | zero => decide
  | succ k =>
    have h1 := lucas_succ_eq_fib_add_fib k
    have h2 := lucas_succ_eq_fib_add_fib (k + 4)
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 ⊢
    have hf2 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := fib_step k
    have hf3 : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := fib_step (k + 1)
    have hf4 : Nat.fib (k + 4) = Nat.fib (k + 3) + Nat.fib (k + 2) := fib_step (k + 2)
    have hf5 : Nat.fib (k + 5) = Nat.fib (k + 4) + Nat.fib (k + 3) := fib_step (k + 3)
    have hf6 : Nat.fib (k + 6) = Nat.fib (k + 5) + Nat.fib (k + 4) := fib_step (k + 4)
    omega

/-- Cassini's identity in `ℤ`: `F_m * F_{m+2} - F_{m+1}^2 = (-1)^(m + 1)`. -/
theorem cassini_identity (m : ℕ) :
    (Nat.fib m : ℤ) * (Nat.fib (m + 2) : ℤ) - (Nat.fib (m + 1) : ℤ) ^ 2 =
      (-1 : ℤ) ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ k ih =>
    have hf2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib k : ℤ) := by
      exact_mod_cast fib_step k
    have hf3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 2) : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast fib_step (k + 1)
    rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega]
    calc
      (Nat.fib (k + 1) : ℤ) * (Nat.fib (k + 3) : ℤ) - (Nat.fib (k + 2) : ℤ) ^ 2
          = -((Nat.fib k : ℤ) * (Nat.fib (k + 2) : ℤ) - (Nat.fib (k + 1) : ℤ) ^ 2) := by
            rw [hf3, hf2]; ring
      _ = -((-1 : ℤ) ^ (k + 1)) := by rw [ih]
      _ = (-1 : ℤ) ^ (k + 2) := by rw [pow_succ]; ring

/-- Lucas–Fibonacci quadratic identity: `L_m^2 - 5 * F_m^2 = 4 * (-1)^m`. -/
theorem lucas_sq_sub_five_fib_sq (m : ℕ) :
    (lucas m : ℤ) ^ 2 - 5 * (Nat.fib m : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ m := by
  cases m with
  | zero => decide
  | succ k =>
    have hL : (lucas (k + 1) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 2) : ℤ) := by
      exact_mod_cast lucas_succ_eq_fib_add_fib k
    have hf2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib k : ℤ) := by
      exact_mod_cast fib_step k
    have hcas := cassini_identity k
    rw [hL]
    nlinarith

/-- Exact residue-class sandwich `5 * w n + 1 ≤ lucas (n + 3) ≤ 5 * w n + 4` for all `n ≥ 1`. -/
theorem lucas_sandwich_w (n : ℕ) (hn : 1 ≤ n) :
    5 * w n + 1 ≤ lucas (n + 3) ∧ lucas (n + 3) ≤ 5 * w n + 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | m + 5 =>
      have hprev := ih (m + 1) (by omega) (by omega)
      have hw := w_add_four (m + 1)
      have hL := lucas_add_four (m + 4)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hprev hw hL ⊢
      omega

end FibSumPerm
