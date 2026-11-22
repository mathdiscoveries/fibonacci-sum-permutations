module

public import FibSumPerm.StepLemma
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-!
# Main Theorems: Hajnal's Conjecture 1 (Layman 2004 / OEIS A097083) & Reshetnikov's Floor Form

Unconditional Lean 4 formalization of:
1. Small hand cases `fibPermCount k` for `k = 1, 2, 3, 4, 5, 6` and witness lower bound
   `2 ≤ fibPermCount 10`.
2. **If direction (`layman_unique_if`)**: `∀ n ≥ 1, fibPermCount (w n) = 1`
   (together with the strengthened invariant `layman_unique_strong` forbidding sum `F_{n+1}`).
3. **Only if direction (`layman_unique_only_if`, Hajnal 2022)**:
   `∀ k ≥ 1, fibPermCount k = 1 → ∃ n ≥ 1, k = w n`.
4. **Full bi-directional theorem (`hajnal_conjecture_1` and `hajnal_conjecture_1_M4`)**:
   `∀ k ≥ 1, fibPermCount k = 1 ↔ ∃ n ≥ 1, k = w n` (and equivalently `∃ l ≥ 2, k = M4 l`).
5. **Reshetnikov's floor formula (`w_eq_floor_fib_div_sqrt5`)**:
   `∀ n ≥ 1, (w n : ℤ) = ⌊(Nat.fib (n + 3) : ℝ) / Real.sqrt 5⌋`, proved via pure integer
   algebra (`w_sq_sandwich` + Lucas/Cassini identities).
-/

@[expose] public section

namespace FibSumPerm

/-! ### Small hand cases (`k = 1, 2, 3, 4, 6` and `k = 10` witness) -/

/-- Exact count for `k = 1`: `fibPermCount 1 = 1` (unique permutation `[1]`). -/
theorem fibPermCount_one : fibPermCount 1 = 1 := by
  unfold fibPermCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, fun i => by fin_cases i; decide⟩, ?_⟩
  rintro ⟨p, _⟩
  apply Subtype.ext
  ext i
  fin_cases i
  have := (p 0).2
  omega

/-- For `k = 2`, every valid permutation equals `Equiv.swap 0 1` (`[2, 1]`). -/
theorem valid_two_eq_swap {p : Equiv.Perm (Fin 2)} (hp : IsValidFibPerm 2 p) :
    p = Equiv.swap 0 1 := by
  have hp1 : p 1 = 0 := by
    have h := hp 1
    have hcases : p 1 = 0 ∨ p 1 = 1 := by omega
    rcases hcases with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at h
      exact (show ¬ IsFib 4 by decide) h
  have hp0 : p 0 = 1 := by
    have hne : p 0 ≠ p 1 := fun heq => by
      have := p.injective heq
      omega
    rw [hp1] at hne
    omega
  ext i
  fin_cases i
  · simp [hp0]
  · simp [hp1]

/-- Exact count for `k = 2`: `fibPermCount 2 = 1` (unique permutation `[2, 1]`). -/
theorem fibPermCount_two : fibPermCount 2 = 1 := by
  unfold fibPermCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨Equiv.swap 0 1, fun i => by fin_cases i <;> decide⟩, ?_⟩
  rintro ⟨p, hp⟩
  exact Subtype.ext (valid_two_eq_swap hp)

/-- No valid permutation of `[2]` uses sum `2 = Nat.fib 3`. -/
theorem no_sum_two_of_valid_two (p : Equiv.Perm (Fin 2)) (hp : IsValidFibPerm 2 p)
    (i : Fin 2) : (i.1 + 1) + ((p i).1 + 1) ≠ Nat.fib 3 := by
  rw [valid_two_eq_swap hp]
  fin_cases i <;> decide

/-- For `k = 3`, every valid permutation equals `Equiv.swap 1 2` (`[1, 3, 2]`). -/
theorem valid_three_eq_swap {p : Equiv.Perm (Fin 3)} (hp : IsValidFibPerm 3 p) :
    p = Equiv.swap 1 2 := by
  have hp2 : p 2 = 1 := by
    have h := hp 2
    have hcases : p 2 = 0 ∨ p 2 = 1 ∨ p 2 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso; rw [h0] at h; exact (show ¬ IsFib 4 by decide) h
    · exact h1
    · exfalso; rw [h2] at h; exact (show ¬ IsFib 6 by decide) h
  have hsym2 : p.symm 2 = 1 := by
    have h := hp.symm 2
    have hcases : p.symm 2 = 0 ∨ p.symm 2 = 1 ∨ p.symm 2 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso; rw [h0] at h; exact (show ¬ IsFib 4 by decide) h
    · exact h1
    · exfalso; rw [h2] at h; exact (show ¬ IsFib 6 by decide) h
  have hp1 : p 1 = 2 := by
    rw [← hsym2, Equiv.apply_symm_apply]
  have hp0 : p 0 = 0 := by
    have hne1 : p 0 ≠ p 1 := fun heq => by have := p.injective heq; omega
    have hne2 : p 0 ≠ p 2 := fun heq => by have := p.injective heq; omega
    rw [hp1] at hne1
    rw [hp2] at hne2
    omega
  apply Equiv.ext; intro i
  fin_cases i
  · exact hp0.trans (by decide)
  · exact hp1.trans (by decide)
  · exact hp2.trans (by decide)

/-- Exact count for `k = 3`: `fibPermCount 3 = 1` (unique permutation `[1, 3, 2]`). -/
theorem fibPermCount_three : fibPermCount 3 = 1 := by
  unfold fibPermCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨Equiv.swap 1 2, fun i => by fin_cases i <;> decide⟩, ?_⟩
  rintro ⟨p, hp⟩
  exact Subtype.ext (valid_three_eq_swap hp)

/-- No valid permutation of `[3]` uses sum `3 = Nat.fib 4`. -/
theorem no_sum_three_of_valid_three (p : Equiv.Perm (Fin 3)) (hp : IsValidFibPerm 3 p)
    (i : Fin 3) : (i.1 + 1) + ((p i).1 + 1) ≠ Nat.fib 4 := by
  rw [valid_three_eq_swap hp]
  fin_cases i <;> decide

/-- Helper reversal involution on `Fin 4`: `[4, 3, 2, 1]`. -/
def rev4 : Equiv.Perm (Fin 4) where
  toFun i := ⟨3 - i.1, by omega⟩
  invFun i := ⟨3 - i.1, by omega⟩
  left_inv i := by ext; dsimp only; omega
  right_inv i := by ext; dsimp only; omega

/-- Exact count for `k = 4`: `fibPermCount 4 = 2` (`[1, 3, 2, 4]` and `[4, 3, 2, 1]`). -/
theorem fibPermCount_four : fibPermCount 4 = 2 := by
  let p₁ : { p : Equiv.Perm (Fin 4) // IsValidFibPerm 4 p } :=
    ⟨Equiv.swap 1 2, fun i => by fin_cases i <;> decide⟩
  let p₂ : { p : Equiv.Perm (Fin 4) // IsValidFibPerm 4 p } :=
    ⟨rev4, fun i => by fin_cases i <;> decide⟩
  have hne : p₁ ≠ p₂ := by
    intro h
    have hv := congrArg (fun x : { p : Equiv.Perm (Fin 4) // IsValidFibPerm 4 p } =>
      (x.1 0).1) h
    have h1 : (p₁.1 0).1 = 0 := by decide
    have h2 : (p₂.1 0).1 = 3 := by decide
    omega
  have hall : ∀ x : { p : Equiv.Perm (Fin 4) // IsValidFibPerm 4 p }, x = p₁ ∨ x = p₂ := by
    rintro ⟨p, hp⟩
    have hp3 : p 3 = 0 ∨ p 3 = 3 := by
      have h := hp 3
      have hcases : p 3 = 0 ∨ p 3 = 1 ∨ p 3 = 2 ∨ p 3 = 3 := by omega
      rcases hcases with h0 | h1 | h2 | h3
      · exact Or.inl h0
      · exfalso; rw [h1] at h; exact (show ¬ IsFib 6 by decide) h
      · exfalso; rw [h2] at h; exact (show ¬ IsFib 7 by decide) h
      · exact Or.inr h3
    rcases hp3 with hp3_0 | hp3_3
    · right
      apply Subtype.ext
      have hp1 : p 1 = 2 := by
        have h := hp 1
        have hne3 : p 1 ≠ p 3 := fun heq => by have := p.injective heq; omega
        rw [hp3_0] at hne3
        have hcases : p 1 = 0 ∨ p 1 = 1 ∨ p 1 = 2 ∨ p 1 = 3 := by omega
        rcases hcases with h0 | h1 | h2 | h3
        · exact absurd h0 hne3
        · exfalso; rw [h1] at h; exact (show ¬ IsFib 4 by decide) h
        · exact h2
        · exfalso; rw [h3] at h; exact (show ¬ IsFib 6 by decide) h
      have hp2 : p 2 = 1 := by
        have h := hp 2
        have hne1 : p 2 ≠ p 1 := fun heq => by have := p.injective heq; omega
        have hne3 : p 2 ≠ p 3 := fun heq => by have := p.injective heq; omega
        rw [hp1] at hne1; rw [hp3_0] at hne3
        have hcases : p 2 = 0 ∨ p 2 = 1 ∨ p 2 = 2 ∨ p 2 = 3 := by omega
        rcases hcases with h0 | h1 | h2 | h3
        · exact absurd h0 hne3
        · exact h1
        · exact absurd h2 hne1
        · exfalso; rw [h3] at h; exact (show ¬ IsFib 7 by decide) h
      have hp0 : p 0 = 3 := by
        have hne1 : p 0 ≠ p 1 := fun heq => by have := p.injective heq; omega
        have hne2 : p 0 ≠ p 2 := fun heq => by have := p.injective heq; omega
        have hne3 : p 0 ≠ p 3 := fun heq => by have := p.injective heq; omega
        rw [hp1] at hne1; rw [hp2] at hne2; rw [hp3_0] at hne3
        omega
      apply Equiv.ext; intro i
      fin_cases i
      · exact hp0.trans (by decide)
      · exact hp1.trans (by decide)
      · exact hp2.trans (by decide)
      · exact hp3_0.trans (by decide)
    · left
      apply Subtype.ext
      have hp2 : p 2 = 1 := by
        have h := hp 2
        have hne3 : p 2 ≠ p 3 := fun heq => by have := p.injective heq; omega
        rw [hp3_3] at hne3
        have hcases : p 2 = 0 ∨ p 2 = 1 ∨ p 2 = 2 ∨ p 2 = 3 := by omega
        rcases hcases with h0 | h1 | h2 | h3
        · exfalso; rw [h0] at h; exact (show ¬ IsFib 4 by decide) h
        · exact h1
        · exfalso; rw [h2] at h; exact (show ¬ IsFib 6 by decide) h
        · exact absurd h3 hne3
      have hp1 : p 1 = 2 := by
        have h := hp 1
        have hne2 : p 1 ≠ p 2 := fun heq => by have := p.injective heq; omega
        have hne3 : p 1 ≠ p 3 := fun heq => by have := p.injective heq; omega
        rw [hp2] at hne2; rw [hp3_3] at hne3
        have hcases : p 1 = 0 ∨ p 1 = 1 ∨ p 1 = 2 ∨ p 1 = 3 := by omega
        rcases hcases with h0 | h1 | h2 | h3
        · exfalso
          have h0_val : p 0 = 2 := by
            have hne01 : p 0 ≠ p 1 := fun heq => by have := p.injective heq; omega
            have hne02 : p 0 ≠ p 2 := fun heq => by have := p.injective heq; omega
            have hne03 : p 0 ≠ p 3 := fun heq => by have := p.injective heq; omega
            rw [h0] at hne01; rw [hp2] at hne02; rw [hp3_3] at hne03
            omega
          have h0valid := hp 0
          rw [h0_val] at h0valid
          exact (show ¬ IsFib 4 by decide) h0valid
        · exact absurd h1 hne2
        · exact h2
        · exact absurd h3 hne3
      have hp0 : p 0 = 0 := by
        have hne1 : p 0 ≠ p 1 := fun heq => by have := p.injective heq; omega
        have hne2 : p 0 ≠ p 2 := fun heq => by have := p.injective heq; omega
        have hne3 : p 0 ≠ p 3 := fun heq => by have := p.injective heq; omega
        rw [hp1] at hne1; rw [hp2] at hne2; rw [hp3_3] at hne3
        omega
      apply Equiv.ext; intro i
      fin_cases i
      · exact hp0.trans (by decide)
      · exact hp1.trans (by decide)
      · exact hp2.trans (by decide)
      · exact hp3_3.trans (by decide)
  unfold fibPermCount
  have huniv : (Finset.univ : Finset { p : Equiv.Perm (Fin 4) // IsValidFibPerm 4 p }) =
      {p₁, p₂} := by
    ext x
    simp [hall x]
  rw [← Finset.card_univ, huniv, Finset.card_pair hne]

/-- First valid permutation on `Fin 6`: `[1, 6, 5, 4, 3, 2]` (sums `2, 8, 8, 8, 8, 8`). -/
def perm6A : Equiv.Perm (Fin 6) where
  toFun i := if h : i.1 = 0 then 0 else ⟨6 - i.1, by omega⟩
  invFun i := if h : i.1 = 0 then 0 else ⟨6 - i.1, by omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Second valid permutation on `Fin 6`: `[4, 6, 5, 1, 3, 2]` (sums `5, 8, 8, 5, 8, 8`). -/
def perm6B : Equiv.Perm (Fin 6) :=
  perm6A.trans (Equiv.swap 0 3)

/-- Exact count for `k = 6`: `fibPermCount 6 = 2` (`[1, 6, 5, 4, 3, 2]` and `[4, 6, 5, 1, 3, 2]`). -/
theorem fibPermCount_six : fibPermCount 6 = 2 := by
  let p₁ : { p : Equiv.Perm (Fin 6) // IsValidFibPerm 6 p } :=
    ⟨perm6A, fun i => by fin_cases i <;> decide⟩
  let p₂ : { p : Equiv.Perm (Fin 6) // IsValidFibPerm 6 p } :=
    ⟨perm6B, fun i => by fin_cases i <;> decide⟩
  have hne : p₁ ≠ p₂ := by
    intro h
    have hv := congrArg (fun x : { p : Equiv.Perm (Fin 6) // IsValidFibPerm 6 p } =>
      (x.1 0).1) h
    have h1 : (p₁.1 0).1 = 0 := by decide
    have h2 : (p₂.1 0).1 = 3 := by decide
    omega
  have hall : ∀ x : { p : Equiv.Perm (Fin 6) // IsValidFibPerm 6 p }, x = p₁ ∨ x = p₂ := by
    rintro ⟨p, hp⟩
    -- Any valid `r` on `Fin 6` satisfies `r 5 = 1` and `r 4 = 2`.
    have hforced : ∀ (r : Equiv.Perm (Fin 6)), IsValidFibPerm 6 r → r 5 = 1 ∧ r 4 = 2 := by
      intro r hr
      have hr5 : r 5 = 1 := by
        have h := hr 5
        have h5v : (5 : Fin 6).1 = 5 := rfl
        have h1v : (1 : Fin 6).1 = 1 := rfl
        have hlt1 : Nat.fib 5 < ((5 : Fin 6).1 + 1) + ((r 5).1 + 1) := by
          have : Nat.fib 5 = 5 := by decide
          omega
        have hlt2 : ((5 : Fin 6).1 + 1) + ((r 5).1 + 1) < Nat.fib 7 := by
          have : Nat.fib 7 = 13 := by decide
          have := (r 5).2
          omega
        have heq := eq_fib_of_isFib_between 5 _ h hlt1 hlt2
        have hF6 : Nat.fib (5 + 1) = 8 := by decide
        ext
        omega
      have hr4 : r 4 = 2 := by
        have h := hr 4
        have h4v : (4 : Fin 6).1 = 4 := rfl
        have h2v : (2 : Fin 6).1 = 2 := rfl
        have hlt1 : Nat.fib 5 < ((4 : Fin 6).1 + 1) + ((r 4).1 + 1) := by
          have : Nat.fib 5 = 5 := by decide
          omega
        have hlt2 : ((4 : Fin 6).1 + 1) + ((r 4).1 + 1) < Nat.fib 7 := by
          have : Nat.fib 7 = 13 := by decide
          have := (r 4).2
          omega
        have heq := eq_fib_of_isFib_between 5 _ h hlt1 hlt2
        have hF6 : Nat.fib (5 + 1) = 8 := by decide
        ext
        omega
      exact ⟨hr5, hr4⟩
    obtain ⟨hp5, hp4⟩ := hforced p hp
    obtain ⟨hsym5, hsym4⟩ := hforced p.symm hp.symm
    have hp1 : p 1 = 5 := by rw [← hsym5, Equiv.apply_symm_apply]
    have hp2 : p 2 = 4 := by rw [← hsym4, Equiv.apply_symm_apply]
    have hp0_cases : p 0 = 0 ∨ p 0 = 3 := by
      have hne1 : p 0 ≠ p 1 := fun heq => by have := p.injective heq; omega
      have hne2 : p 0 ≠ p 2 := fun heq => by have := p.injective heq; omega
      have hne4 : p 0 ≠ p 4 := fun heq => by have := p.injective heq; omega
      have hne5 : p 0 ≠ p 5 := fun heq => by have := p.injective heq; omega
      rw [hp1] at hne1; rw [hp2] at hne2; rw [hp4] at hne4; rw [hp5] at hne5
      omega
    have hp3_cases : p 3 = 0 ∨ p 3 = 3 := by
      have hne1 : p 3 ≠ p 1 := fun heq => by have := p.injective heq; omega
      have hne2 : p 3 ≠ p 2 := fun heq => by have := p.injective heq; omega
      have hne4 : p 3 ≠ p 4 := fun heq => by have := p.injective heq; omega
      have hne5 : p 3 ≠ p 5 := fun heq => by have := p.injective heq; omega
      rw [hp1] at hne1; rw [hp2] at hne2; rw [hp4] at hne4; rw [hp5] at hne5
      omega
    have hp03_ne : p 0 ≠ p 3 := fun heq => by have := p.injective heq; omega
    rcases hp0_cases with hp0_0 | hp0_3
    · left
      apply Subtype.ext
      have hp3_3 : p 3 = 3 := by omega
      apply Equiv.ext; intro i
      fin_cases i
      · exact hp0_0.trans (by decide)
      · exact hp1.trans (by decide)
      · exact hp2.trans (by decide)
      · exact hp3_3.trans (by decide)
      · exact hp4.trans (by decide)
      · exact hp5.trans (by decide)
    · right
      apply Subtype.ext
      have hp3_0 : p 3 = 0 := by omega
      apply Equiv.ext; intro i
      fin_cases i
      · exact hp0_3.trans (by decide)
      · exact hp1.trans (by decide)
      · exact hp2.trans (by decide)
      · exact hp3_0.trans (by decide)
      · exact hp4.trans (by decide)
      · exact hp5.trans (by decide)
  unfold fibPermCount
  have huniv : (Finset.univ : Finset { p : Equiv.Perm (Fin 6) // IsValidFibPerm 6 p }) =
      {p₁, p₂} := by
    ext x
    simp [hall x]
  rw [← Finset.card_univ, huniv, Finset.card_pair hne]

/-- First valid permutation on `Fin 10`: `[2, 1, 10, 9, 8, 7, 6, 5, 4, 3]`
(sums `3, 3, 13, 13, ..., 13`). -/
def perm10A : Equiv.Perm (Fin 10) where
  toFun i := if h : i.1 < 2 then ⟨1 - i.1, by omega⟩ else ⟨11 - i.1, by omega⟩
  invFun i := if h : i.1 < 2 then ⟨1 - i.1, by omega⟩ else ⟨11 - i.1, by omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Second valid permutation on `Fin 10`: `[7, 6, 10, 9, 8, 2, 1, 5, 4, 3]`
(detour swapping `{1, 2}` with `{6, 7}`, sums `8, 8, 13, 13, 13, 8, 8, 13, 13, 13`). -/
def perm10B : Equiv.Perm (Fin 10) :=
  (perm10A.trans (Equiv.swap 0 5)).trans (Equiv.swap 1 6)

/-- Lower bound `2 ≤ fibPermCount 10` witnessed by `perm10A ≠ perm10B`. -/
theorem two_le_fibPermCount_ten : 2 ≤ fibPermCount 10 := by
  let p₁ : { p : Equiv.Perm (Fin 10) // IsValidFibPerm 10 p } :=
    ⟨perm10A, fun i => by fin_cases i <;> decide⟩
  let p₂ : { p : Equiv.Perm (Fin 10) // IsValidFibPerm 10 p } :=
    ⟨perm10B, fun i => by fin_cases i <;> decide⟩
  have hne : p₁ ≠ p₂ := by
    intro h
    have hv := congrArg (fun x : { p : Equiv.Perm (Fin 10) // IsValidFibPerm 10 p } =>
      (x.1 0).1) h
    have h1 : (p₁.1 0).1 = 1 := by decide
    have h2 : (p₂.1 0).1 = 6 := by decide
    omega
  have hlt : 1 < fibPermCount 10 := Fintype.one_lt_card_iff.mpr ⟨p₁, p₂, hne⟩
  omega

/-! ### "If" direction: uniqueness at every Layman number `w n` -/

/-- Strengthened induction invariant `C(n)`: `[w n]` has a unique valid Fibonacci-sum
permutation, and that permutation uses no sum equal to `Nat.fib (n + 1)`. -/
theorem layman_unique_strong (n : ℕ) (hn : 1 ≤ n) :
    fibPermCount (w n) = 1 ∧
      ∀ p : Equiv.Perm (Fin (w n)), IsValidFibPerm (w n) p →
        ∀ i : Fin (w n), (i.1 + 1) + ((p i).1 + 1) ≠ Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 =>
      refine ⟨fibPermCount_one, ?_⟩
      intro p _ i
      have : Nat.fib (1 + 1) = 1 := by decide
      omega
    | 2 =>
      exact ⟨fibPermCount_two, no_sum_two_of_valid_two⟩
    | 3 =>
      exact ⟨fibPermCount_three, no_sum_three_of_valid_three⟩
    | m + 4 =>
      have hprev := ih (m + 2) (by omega) (by omega)
      have hb_cur := w_bounds (m + 4) (by omega)
      have hb_prev := w_bounds (m + 2) (by omega)
      have hrec := w_add_w_add_one (m + 2)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hb_cur hb_prev hrec
      have hF7 : Nat.fib (m + 7) = Nat.fib (m + 6) + Nat.fib (m + 5) := fib_step (m + 5)
      have hpos3 : 1 ≤ Nat.fib (m + 3) := fib_pos_of_pos (by omega)
      have hstep := step_lemma (j := m + 3) (k := w (m + 4)) (t := w (m + 2))
        (by omega)
        (by simpa [Nat.add_assoc, Nat.reduceAdd] using hb_cur.1)
        (by
          have : 2 * w (m + 4) < Nat.fib (m + 6) + Nat.fib (m + 5) := by omega
          simpa [Nat.add_assoc, Nat.reduceAdd] using this)
        (by
          have : w (m + 2) = Nat.fib (m + 6) - 1 - w (m + 4) := by omega
          simpa [Nat.add_assoc, Nat.reduceAdd] using this)
        (by omega)
        (by simpa [Nat.add_assoc, Nat.reduceAdd] using hb_prev.2.2.1)
        (by simpa [Nat.add_assoc, Nat.reduceAdd] using hb_prev.2.2.2)
        hprev.1
        (by
          intro q hq i
          have h := hprev.2 q hq i
          rwa [show m + 2 + 1 = m + 3 by omega] at h)
      refine ⟨hstep.1, ?_⟩
      intro p hp i
      have h := hstep.2 p hp i
      rwa [show m + 3 + 2 = m + 4 + 1 by omega] at h

/-- **"If" direction (the hard direction of Hajnal 2022 Conjecture 1)**:
for every `n ≥ 1`, `[w n]` has a unique valid Fibonacci-sum permutation. -/
theorem layman_unique_if (n : ℕ) (hn : 1 ≤ n) : fibPermCount (w n) = 1 :=
  (layman_unique_strong n hn).1

/-- Exact count for `k = 5`: `fibPermCount 5 = 1` (since `5 = w 4`). -/
theorem fibPermCount_five : fibPermCount 5 = 1 :=
  layman_unique_if 4 (by omega)

/-! ### "Only if" direction (Hajnal 2022) and Full Bi-Directional Theorem -/

/-- **"Only if" direction (Hajnal 2022 Theorem 1/2)**:
if `k ≥ 1` has a unique valid Fibonacci-sum permutation, then `k = w n` for some `n ≥ 1`. -/
theorem layman_unique_only_if (k : ℕ) (hk : 1 ≤ k) (huniq : fibPermCount k = 1) :
    ∃ n : ℕ, 1 ≤ n ∧ k = w n := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨j, hj3, hFj_le, h2k_lt⟩ := exists_fib_scale hk
    -- Handle scales `j = 3` (`k = 1`) and `j = 4` (`k = 2`) directly.
    by_cases hj5 : 5 ≤ j
    · -- General scale `j ≥ 5`.
      have hstep_j1 : Nat.fib (j + 1) = Nat.fib j + Nat.fib (j - 1) := by
        have := fib_step (j - 1)
        have h1 : j - 1 + 2 = j + 1 := by omega
        have h2 : j - 1 + 1 = j := by omega
        rw [h1, h2] at this; exact this
      have hstep_j : Nat.fib j = Nat.fib (j - 1) + Nat.fib (j - 2) := by
        have := fib_step (j - 2)
        have h1 : j - 2 + 2 = j := by omega
        have h2 : j - 2 + 1 = j - 1 := by omega
        rw [h1, h2] at this; exact this
      have hstep_jm2 : Nat.fib (j - 2) = Nat.fib (j - 3) + Nat.fib (j - 4) := by
        have := fib_step (j - 4)
        have h1 : j - 4 + 2 = j - 2 := by omega
        have h2 : j - 4 + 1 = j - 3 := by omega
        rw [h1, h2] at this; exact this
      have hlt_prev : Nat.fib (j - 1) < Nat.fib j :=
        fib_strictMono_from_two (by omega) (by omega)
      have hk_lt_Fj : k < Nat.fib j := by omega
      -- Since `fibPermCount k = 1`, `Nat.fib (j - 1)` cannot exceed `k`.
      have hFjm1_le_k : Nat.fib (j - 1) ≤ k := by
        by_contra hlt
        have h2 := two_le_fibPermCount_of_two_fibs
          (isFib_fib (by omega)) (isFib_fib (by omega)) (by omega) hlt_prev hFj_le
        omega
      -- For `j ≥ 5`, `Nat.fib (j - 2) ≥ 2`, so `t = Nat.fib j - k - 1 ≥ 1`.
      have hFjm2_ge2 : 2 ≤ Nat.fib (j - 2) := by
        have : Nat.fib 3 = 2 := by decide
        have := Nat.fib_mono (show 3 ≤ j - 2 by omega)
        omega
      set t := Nat.fib j - k - 1
      have ht_pos : 1 ≤ t := by omega
      have ht_lt_k : t < k := by omega
      -- By the Extension Lemma, `fibPermCount t = 1`.
      have ht_uniq : fibPermCount t = 1 := by
        have hle : fibPermCount t ≤ fibPermCount k :=
          extension_count_ge (isFib_fib (by omega)) hk_lt_Fj hFj_le
        have hge := fibPermCount_pos t
        omega
      -- By strong induction, `t = w m` for some `m ≥ 1`.
      obtain ⟨m, hm1, htm⟩ := ih t ht_lt_k ht_pos ht_uniq
      have hmb := w_bounds m hm1
      -- Upper bound on `m`: `w m = t < Nat.fib (j - 2)`, so `m ≤ j - 4`.
      have hm_le : m ≤ j - 4 := by
        by_contra hgt
        have hle_fib : Nat.fib (j - 2) ≤ Nat.fib (m + 1) := Nat.fib_mono (by omega)
        omega
      -- Lower bound on `2 * w m`: `Nat.fib (j - 2) - 1 ≤ 2 * w m`.
      have h2t_ge : Nat.fib (j - 2) ≤ 2 * w m + 1 := by omega
      -- Eliminate `m ≤ j - 6`.
      have hm_ge : j - 5 ≤ m := by
        by_contra hlt
        have hle_fib : Nat.fib (m + 3) ≤ Nat.fib (j - 3) := Nat.fib_mono (by omega)
        have hpos_jm4 : 1 ≤ Nat.fib (j - 4) := fib_pos_of_pos (by omega)
        omega
      -- Eliminate `m = j - 5` (`m ≥ 3` by `two_mul_w_add_two_le`; `m = 1` is `k = 6`; `m = 2` is `k = 10`).
      have hm_eq : m = j - 4 := by
        by_contra hne
        have hm_eq5 : m = j - 5 := by omega
        by_cases hm3 : 3 ≤ m
        · have hsharp := two_mul_w_add_two_le m hm3
          have hidx : m + 3 = j - 2 := by omega
          rw [hidx] at hsharp
          omega
        · have hm12 : m = 1 ∨ m = 2 := by omega
          rcases hm12 with rfl | rfl
          · have hj6 : j = 6 := by omega
            have hF6 : Nat.fib j = 8 := by rw [hj6]; decide
            have hw1 : w 1 = 1 := rfl
            have hk6 : k = 6 := by omega
            rw [hk6, fibPermCount_six] at huniq
            omega
          · have hj7 : j = 7 := by omega
            have hF7 : Nat.fib j = 13 := by rw [hj7]; decide
            have hw2 : w 2 = 2 := rfl
            have hk10 : k = 10 := by omega
            have h10 := two_le_fibPermCount_ten
            rw [hk10] at huniq
            omega
      -- Conclude `k = w (j - 2)`.
      refine ⟨j - 2, by omega, ?_⟩
      have hrec := w_add_w_add_one (j - 4)
      have hidx1 : j - 4 + 2 = j - 2 := by omega
      have hidx2 : j - 4 + 4 = j := by omega
      rw [hidx1, hidx2] at hrec
      rw [hm_eq] at htm
      omega
    · have hj34 : j = 3 ∨ j = 4 := by omega
      rcases hj34 with rfl | rfl
      · have h3 : Nat.fib 3 = 2 := by decide
        have h4 : Nat.fib (3 + 1) = 3 := by decide
        exact ⟨1, by omega, by change k = 1; omega⟩
      · have h4 : Nat.fib 4 = 3 := by decide
        have h5 : Nat.fib (4 + 1) = 5 := by decide
        exact ⟨2, by omega, by change k = 2; omega⟩

/-- **Hajnal (2022) Conjecture 1 / Layman (2004) OEIS A097083 (Full Bi-Directional Theorem)**:
for every `k ≥ 1`, `{1, ..., k}` has a unique Fibonacci-sum permutation if and only if
`k = w n` for some `n ≥ 1`. -/
theorem hajnal_conjecture_1 (k : ℕ) (hk : 1 ≤ k) :
    fibPermCount k = 1 ↔ ∃ n : ℕ, 1 ≤ n ∧ k = w n := by
  constructor
  · exact layman_unique_only_if k hk
  · rintro ⟨n, hn, rfl⟩
    exact layman_unique_if n hn

/-- **Hajnal (2022) Conjecture 1 in `M4` notation**:
for every `k ≥ 1`, `fibPermCount k = 1 ↔ ∃ l ≥ 2, k = M4 l`. -/
theorem hajnal_conjecture_1_M4 (k : ℕ) (hk : 1 ≤ k) :
    fibPermCount k = 1 ↔ ∃ l : ℕ, 2 ≤ l ∧ k = M4 l := by
  rw [hajnal_conjecture_1 k hk]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n + 1, by omega, (M4_eq_w n hn).symm⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l - 1, by omega, ?_⟩
    have h := M4_eq_w (l - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at h
    exact h

/-! ### Reshetnikov's Floor Formula (2015, OEIS A097083) -/

/-- Exact integer square sandwich `5 * (w n)^2 < F_{n+3}^2 < 5 * (w n + 1)^2` for all `n ≥ 1`,
proved purely algebraically from Cassini's identity and `5 * w n + 1 ≤ L_{n+3} ≤ 5 * w n + 4`. -/
theorem w_sq_sandwich (n : ℕ) (hn : 1 ≤ n) :
    5 * (w n) ^ 2 < (Nat.fib (n + 3)) ^ 2 ∧
      (Nat.fib (n + 3)) ^ 2 < 5 * (w n + 1) ^ 2 := by
  have hw_pos : 1 ≤ w n := by
    have h1 := (w_bounds n hn).1
    have hpos : 1 ≤ Nat.fib (n + 1) := fib_pos_of_pos (by omega)
    omega
  have hLsand := lucas_sandwich_w n hn
  have hLquad := lucas_sq_sub_five_fib_sq (n + 3)
  have hsign : (-1 : ℤ) ^ (n + 3) = 1 ∨ (-1 : ℤ) ^ (n + 3) = -1 := by
    rcases Nat.even_or_odd (n + 3) with he | ho
    · exact Or.inl he.neg_one_pow
    · exact Or.inr ho.neg_one_pow
  have hLw1 : 5 * (w n : ℤ) + 1 ≤ (lucas (n + 3) : ℤ) := by exact_mod_cast hLsand.1
  have hLw2 : (lucas (n + 3) : ℤ) ≤ 5 * (w n : ℤ) + 4 := by exact_mod_cast hLsand.2
  have hw1z : (1 : ℤ) ≤ (w n : ℤ) := by exact_mod_cast hw_pos
  have hlow_z : 5 * (w n : ℤ) ^ 2 < (Nat.fib (n + 3) : ℤ) ^ 2 := by
    rcases hsign with hs | hs <;> rw [hs] at hLquad <;> nlinarith
  have hhigh_z : (Nat.fib (n + 3) : ℤ) ^ 2 < 5 * ((w n : ℤ) + 1) ^ 2 := by
    rcases hsign with hs | hs <;> rw [hs] at hLquad <;> nlinarith
  exact ⟨by exact_mod_cast hlow_z, by exact_mod_cast hhigh_z⟩

/-- **Reshetnikov's floor formula (OEIS A097083, 2015)**:
for every `n ≥ 1`, `w n = ⌊F_{n+3} / √5⌋`. -/
theorem w_eq_floor_fib_div_sqrt5 (n : ℕ) (hn : 1 ≤ n) :
    (w n : ℤ) = ⌊(Nat.fib (n + 3) : ℝ) / Real.sqrt 5⌋ := by
  symm
  rw [Int.floor_eq_iff]
  have hs5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  obtain ⟨hlow, hhigh⟩ := w_sq_sandwich n hn
  have hlow_r : (5 : ℝ) * (w n : ℝ) ^ 2 < (Nat.fib (n + 3) : ℝ) ^ 2 := by
    exact_mod_cast hlow
  have hhigh_r : (Nat.fib (n + 3) : ℝ) ^ 2 < (5 : ℝ) * ((w n : ℝ) + 1) ^ 2 := by
    exact_mod_cast hhigh
  have hw_nonneg : (0 : ℝ) ≤ (w n : ℝ) := Nat.cast_nonneg _
  have hF_nonneg : (0 : ℝ) ≤ (Nat.fib (n + 3) : ℝ) := Nat.cast_nonneg _
  constructor
  · rw [le_div_iff₀ hs5_pos]
    simp only [Int.cast_natCast]
    nlinarith [mul_nonneg hw_nonneg (le_of_lt hs5_pos)]
  · rw [div_lt_iff₀ hs5_pos]
    simp only [Int.cast_natCast]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (w n : ℝ) + 1 by linarith) (le_of_lt hs5_pos)]

end FibSumPerm
