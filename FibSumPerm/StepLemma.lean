/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FibSumPerm.Defs

import Mathlib.Tactic

/-!
# Extension Lemma, Existence, Two-Fibonacci Lower Bound, and Step Lemma

Formalizes:
1. `extendPerm` and `extension_count_ge` (Wasserman 2007 / Hajnal 2022 Observations 3–4):
   any valid permutation of `[s - k - 1]` extends to `[k]` by reversing `[s - k, k]` with sum `s`.
2. `fibPermCount_pos` (Sun / Hajnal): every `k` has at least one valid Fibonacci-sum permutation.
3. `two_le_fibPermCount_of_two_fibs`: two distinct Fibonacci numbers in `(k, 2 * k]` force
   `2 ≤ fibPermCount k`.
4. `step_lemma`: the key structural induction step forcing
   uniqueness and forbidding sum `G` on `[k]` from uniqueness and forbidding sum `I` on `[t]`.
-/

@[expose] public section

namespace FibSumPerm

/-- Underlying function extending a permutation `q` of `Fin (s - k - 1)` to `Fin k`
by fixing `q` on `[1, s - k - 1]` and reversing `[s - k, k]` via `x ↦ s - x`. -/
def extendPermFun (k s : ℕ) (hks : k < s) (hs2k : s ≤ 2 * k)
    (q : Equiv.Perm (Fin (s - k - 1))) (i : Fin k) : Fin k :=
  if h : i.1 < s - k - 1 then
    ⟨(q ⟨i.1, h⟩).1, by have := (q ⟨i.1, h⟩).2; omega⟩
  else
    ⟨s - 2 - i.1, by omega⟩

/-- Canonical extension permutation on `Fin k` reversing `[s - k, k]` with sum `s`
and acting as `q` on `[1, s - k - 1]`. -/
def extendPerm (k s : ℕ) (hks : k < s) (hs2k : s ≤ 2 * k)
    (q : Equiv.Perm (Fin (s - k - 1))) : Equiv.Perm (Fin k) where
  toFun := extendPermFun k s hks hs2k q
  invFun := extendPermFun k s hks hs2k q.symm
  left_inv := by
    intro i
    dsimp only [extendPermFun]
    split_ifs with h1 h2 h3
    · ext
      simp
    · exfalso
      exact h2 (q ⟨i.1, h1⟩).2
    · exfalso
      dsimp only at h3
      omega
    · ext
      dsimp only
      omega
  right_inv := by
    intro i
    dsimp only [extendPermFun]
    split_ifs with h1 h2 h3
    · ext
      simp
    · exfalso
      exact h2 (q.symm ⟨i.1, h1⟩).2
    · exfalso
      dsimp only at h3
      omega
    · ext
      dsimp only
      omega

/-- The extension sends the top element `k` (index `k - 1`) to `s - k` (index `s - k - 1`). -/
theorem extendPerm_last (k s : ℕ) (hks : k < s) (hs2k : s ≤ 2 * k)
    (q : Equiv.Perm (Fin (s - k - 1))) :
    (extendPerm k s hks hs2k q ⟨k - 1, by omega⟩).1 = s - k - 1 := by
  dsimp only [extendPerm, extendPermFun, Equiv.coe_fn_mk]
  split_ifs with h
  · omega
  · dsimp only; omega

/-- The extension map `q ↦ extendPerm k s hks hs2k q` is injective. -/
theorem extendPerm_injective (k s : ℕ) (hks : k < s) (hs2k : s ≤ 2 * k) :
    Function.Injective (extendPerm k s hks hs2k) := by
  intro q₁ q₂ heq
  ext a
  have hval := congrArg (fun p : Equiv.Perm (Fin k) => (p ⟨a.1, by omega⟩).1) heq
  dsimp only [extendPerm, extendPermFun, Equiv.coe_fn_mk] at hval
  simp [a.2] at hval
  exact hval

/-- Extending a valid permutation of `[s - k - 1]` using a Fibonacci sum `s` produces
a valid permutation of `[k]`. -/
theorem extendPerm_valid {k s : ℕ} (hs : IsFib s) (hks : k < s) (hs2k : s ≤ 2 * k)
    {q : Equiv.Perm (Fin (s - k - 1))} (hq : IsValidFibPerm (s - k - 1) q) :
    IsValidFibPerm k (extendPerm k s hks hs2k q) := by
  intro i
  dsimp only [extendPerm, extendPermFun, Equiv.coe_fn_mk]
  split_ifs with h
  · exact hq ⟨i.1, h⟩
  · dsimp only
    have hsum : (i.1 + 1) + (s - 2 - i.1 + 1) = s := by omega
    rw [hsum]
    exact hs

/-- **Extension Lemma**: for any Fibonacci `s` with `k < s ≤ 2 * k`,
`fibPermCount (s - k - 1) ≤ fibPermCount k`. -/
theorem extension_count_ge {k s : ℕ} (hs : IsFib s) (hks : k < s) (hs2k : s ≤ 2 * k) :
    fibPermCount (s - k - 1) ≤ fibPermCount k := by
  unfold fibPermCount
  refine Fintype.card_le_of_injective
    (fun q => ⟨extendPerm k s hks hs2k q.1, extendPerm_valid hs hks hs2k q.2⟩) ?_
  intro q₁ q₂ h
  apply Subtype.ext
  exact extendPerm_injective k s hks hs2k (congrArg Subtype.val h)

/-- **Existence (Sun / Hajnal)**: every `k : ℕ` has at least one valid Fibonacci-sum
permutation. -/
theorem fibPermCount_pos (k : ℕ) : 1 ≤ fibPermCount k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 =>
      rw [fibPermCount_zero]
    | m + 1 =>
      obtain ⟨j, hj3, hFj_le, h2k_lt⟩ := exists_fib_scale (show 1 ≤ m + 1 by omega)
      have hstep : Nat.fib (j + 1) = Nat.fib j + Nat.fib (j - 1) := by
        have := fib_step (j - 1)
        have h1 : j - 1 + 2 = j + 1 := by omega
        have h2 : j - 1 + 1 = j := by omega
        rw [h1, h2] at this
        exact this
      have hlt_prev : Nat.fib (j - 1) < Nat.fib j :=
        fib_strictMono_from_two (by omega) (by omega)
      have hk_lt_Fj : m + 1 < Nat.fib j := by omega
      have ht_lt : Nat.fib j - (m + 1) - 1 < m + 1 := by omega
      have hih := ih (Nat.fib j - (m + 1) - 1) ht_lt
      have hext := extension_count_ge (isFib_fib (by omega)) hk_lt_Fj hFj_le
      omega

/-- **Two-Fibonacci lower bound**: if two distinct Fibonacci numbers `s₁ < s₂` lie in
`(k, 2 * k]`, then `2 ≤ fibPermCount k`. -/
theorem two_le_fibPermCount_of_two_fibs {k s₁ s₂ : ℕ}
    (hs₁ : IsFib s₁) (hs₂ : IsFib s₂)
    (hk1 : k < s₁) (h12 : s₁ < s₂) (h2k : s₂ ≤ 2 * k) :
    2 ≤ fibPermCount k := by
  have hpos1 : 0 < fibPermCount (s₁ - k - 1) := fibPermCount_pos (s₁ - k - 1)
  have hpos2 : 0 < fibPermCount (s₂ - k - 1) := fibPermCount_pos (s₂ - k - 1)
  rw [fibPermCount, Fintype.card_pos_iff] at hpos1 hpos2
  obtain ⟨⟨q₁, hq₁⟩⟩ := hpos1
  obtain ⟨⟨q₂, hq₂⟩⟩ := hpos2
  let p₁ : { p : Equiv.Perm (Fin k) // IsValidFibPerm k p } :=
    ⟨extendPerm k s₁ hk1 (by omega) q₁, extendPerm_valid hs₁ hk1 (by omega) hq₁⟩
  let p₂ : { p : Equiv.Perm (Fin k) // IsValidFibPerm k p } :=
    ⟨extendPerm k s₂ (by omega) h2k q₂, extendPerm_valid hs₂ (by omega) h2k hq₂⟩
  have hne : p₁ ≠ p₂ := by
    intro heq
    have hval := congrArg (fun x : { p : Equiv.Perm (Fin k) // IsValidFibPerm k p } =>
      (x.1 ⟨k - 1, by omega⟩).1) heq
    rw [extendPerm_last k s₁ hk1 (by omega) q₁,
        extendPerm_last k s₂ (by omega) h2k q₂] at hval
    omega
  have hlt : 1 < fibPermCount k := Fintype.one_lt_card_iff.mpr ⟨p₁, p₂, hne⟩
  omega

/-- **Step Lemma**:
Let `I = F_j`, `H = F_{j+1}`, `G = F_{j+2}`, `F = F_{j+3}` with `j ≥ 3`.
Suppose `G ≤ k`, `2 * k < F + G`, `t = F - 1 - k ≥ 1`, `H ≤ 2 * t < G`, and `[t]` has
a unique valid Fibonacci-sum permutation which uses no sum `I`.
Then `[k]` has a unique valid Fibonacci-sum permutation, and that permutation uses no sum `G`. -/
theorem step_lemma {j k t : ℕ} (hj : 3 ≤ j)
    (hGk : Nat.fib (j + 2) ≤ k)
    (hkFG : 2 * k < Nat.fib (j + 3) + Nat.fib (j + 2))
    (ht : t = Nat.fib (j + 3) - 1 - k)
    (ht1 : 1 ≤ t)
    (_hHt : Nat.fib (j + 1) ≤ 2 * t)
    (htG : 2 * t < Nat.fib (j + 2))
    (huniq : fibPermCount t = 1)
    (hnoI : ∀ q : Equiv.Perm (Fin t), IsValidFibPerm t q →
      ∀ i : Fin t, (i.1 + 1) + ((q i).1 + 1) ≠ Nat.fib j) :
    fibPermCount k = 1 ∧
      ∀ p : Equiv.Perm (Fin k), IsValidFibPerm k p →
        ∀ i : Fin k, (i.1 + 1) + ((p i).1 + 1) ≠ Nat.fib (j + 2) := by
  have ht_sub : t = Nat.fib (j + 3) - k - 1 := by omega
  subst ht_sub
  set I := Nat.fib j
  set H := Nat.fib (j + 1)
  set G := Nat.fib (j + 2)
  set F := Nat.fib (j + 3)
  set t := F - k - 1
  have hG_eq : G = H + I := fib_step j
  have hF_eq : F = G + H := fib_step (j + 1)
  have hF'_eq : Nat.fib (j + 4) = F + G := fib_step (j + 2)
  have hI_ge2 : 2 ≤ I := by
    have : Nat.fib 3 = 2 := by decide
    have := Nat.fib_mono hj
    omega
  have hI_lt_H : I < H := fib_strictMono_from_two (by omega) (by omega)
  have hH_lt_G : H < G := fib_strictMono_from_two (by omega) (by omega)
  have hG_lt_F : G < F := fib_strictMono_from_two (by omega) (by omega)
  have hkF : k < F := by omega
  have hF2k : F ≤ 2 * k := by omega
  have ht_lt_H : t < H := by omega
  have ht_lt_k : t < k := by omega
  -- Extract the unique valid permutation `p₀` on `Fin t`.
  have hcard := huniq
  unfold fibPermCount at hcard
  rw [Fintype.card_eq_one_iff] at hcard
  obtain ⟨⟨p₀, hp₀⟩, hp₀_uniq⟩ := hcard
  -- Canonical valid extension `p_ext` on `Fin k`.
  let p_ext : Equiv.Perm (Fin k) := extendPerm k F hkF hF2k p₀
  have hp_ext_valid : IsValidFibPerm k p_ext :=
    extendPerm_valid (isFib_fib (by omega)) hkF hF2k hp₀
  -- Step (i): rows in `(G, k]` are forced to sum to `F`.
  have h_high : ∀ (r : Equiv.Perm (Fin k)), IsValidFibPerm k r →
      ∀ i : Fin k, G < i.1 + 1 → (i.1 + 1) + ((r i).1 + 1) = F := by
    intro r hr i hi
    have hlt1 : Nat.fib (j + 2) < (i.1 + 1) + ((r i).1 + 1) := by omega
    have hlt2 : (i.1 + 1) + ((r i).1 + 1) < Nat.fib (j + 4) := by
      have hi_le : i.1 + 1 ≤ k := i.2
      have hri_le : (r i).1 + 1 ≤ k := (r i).2
      omega
    exact eq_fib_of_isFib_between (j + 2) _ (hr i) hlt1 hlt2
  -- Step (i) backward: rows in `[t + 1, H - 1]` are forced to sum to `F`.
  have h_low_forced : ∀ (r : Equiv.Perm (Fin k)), IsValidFibPerm k r →
      ∀ i : Fin k, t < i.1 + 1 → i.1 + 1 < H → (i.1 + 1) + ((r i).1 + 1) = F := by
    intro r hr i hi1 hi2
    let m : Fin k := ⟨F - (i.1 + 1) - 1, by omega⟩
    have hm_val : m.1 = F - (i.1 + 1) - 1 := rfl
    have hmG : G < m.1 + 1 := by omega
    have hback := h_high r.symm hr.symm m hmG
    have hsym : r.symm m = i := by
      ext
      omega
    have hfwd : r i = m := by
      rw [← hsym, Equiv.apply_symm_apply]
    rw [hfwd, hm_val]
    omega
  -- Step (i) consequence: `R = L ∪ U` is preserved by any valid permutation `r`.
  have h_mem_R : ∀ (r : Equiv.Perm (Fin k)), IsValidFibPerm k r →
      ∀ i : Fin k, (i.1 + 1 ≤ t ∨ (H ≤ i.1 + 1 ∧ i.1 + 1 ≤ G)) →
        ((r i).1 + 1 ≤ t ∨ (H ≤ (r i).1 + 1 ∧ (r i).1 + 1 ≤ G)) := by
    intro r hr i hi
    by_contra hnot
    have hcases : G < (r i).1 + 1 ∨ (t < (r i).1 + 1 ∧ (r i).1 + 1 < H) := by omega
    rcases hcases with hgt | ⟨hlo, hhi⟩
    · have hsum := h_high r.symm hr.symm (r i) hgt
      rw [Equiv.symm_apply_apply] at hsum
      omega
    · have hsum := h_low_forced r.symm hr.symm (r i) hlo hhi
      rw [Equiv.symm_apply_apply] at hsum
      omega
  -- Step (ii): `U + U` sums to `F`.
  have h_UU : ∀ (r : Equiv.Perm (Fin k)), IsValidFibPerm k r →
      ∀ i : Fin k, H ≤ i.1 + 1 → i.1 + 1 ≤ G →
        H ≤ (r i).1 + 1 → (r i).1 + 1 ≤ G →
          (i.1 + 1) + ((r i).1 + 1) = F := by
    intro r hr i hi1 hi2 hri1 hri2
    have hlt1 : Nat.fib (j + 2) < (i.1 + 1) + ((r i).1 + 1) := by omega
    have hlt2 : (i.1 + 1) + ((r i).1 + 1) < Nat.fib (j + 4) := by omega
    exact eq_fib_of_isFib_between (j + 2) _ (hr i) hlt1 hlt2
  -- Step (ii): `L + U` sums to `G`.
  have h_LU : ∀ (r : Equiv.Perm (Fin k)), IsValidFibPerm k r →
      ∀ i : Fin k, i.1 + 1 ≤ t → H ≤ (r i).1 + 1 → (r i).1 + 1 ≤ G →
        (i.1 + 1) + ((r i).1 + 1) = G := by
    intro r hr i hi1 hri1 hri2
    have hlt1 : Nat.fib (j + 1) < (i.1 + 1) + ((r i).1 + 1) := by omega
    have hlt2 : (i.1 + 1) + ((r i).1 + 1) < Nat.fib (j + 3) := by omega
    exact eq_fib_of_isFib_between (j + 1) _ (hr i) hlt1 hlt2
  -- Step (iii): any detour `y ∈ L ↦ U` forces `I - y ∈ L` hit from `H + y ∈ U`.
  have h_AB : ∀ (r : Equiv.Perm (Fin k)), IsValidFibPerm k r →
      ∀ y : Fin t, H ≤ (r ⟨y.1, by omega⟩).1 + 1 →
        y.1 + 1 < I ∧ I - (y.1 + 1) ≤ t ∧
        (r ⟨H + y.1, by omega⟩).1 + 1 = I - (y.1 + 1) ∧
        H ≤ (r.symm ⟨I - (y.1 + 1) - 1, by omega⟩).1 + 1 := by
    intro r hr y hyH
    have hy_in_R := h_mem_R r hr ⟨y.1, by omega⟩ (Or.inl (by dsimp only; omega))
    have hy_le_G : (r ⟨y.1, by omega⟩).1 + 1 ≤ G := by omega
    have hsum_y : (y.1 + 1) + ((r ⟨y.1, by omega⟩).1 + 1) = G := by
      simpa using h_LU r hr ⟨y.1, by omega⟩ (by dsimp only; omega) hyH hy_le_G
    have hy_le_I : y.1 + 1 ≤ I := by omega
    let u : Fin k := ⟨H + y.1, by omega⟩
    have hu_val : u.1 = H + y.1 := rfl
    have hu_in_R := h_mem_R r hr u (Or.inr ⟨by omega, by omega⟩)
    have hru_le_t : (r u).1 + 1 ≤ t := by
      rcases hu_in_R with hle | ⟨hgeH, hleG⟩
      · exact hle
      · exfalso
        have hsum_u := h_UU r hr u (by omega) (by omega) hgeH hleG
        have heq_img : r u = r ⟨y.1, by omega⟩ := by
          ext
          omega
        have heq_dom : u = ⟨y.1, by omega⟩ := r.injective heq_img
        have hval := congrArg Fin.val heq_dom
        dsimp only at hval
        omega
    have hsum_ru := h_LU r.symm hr.symm (r u) hru_le_t
      (by rw [Equiv.symm_apply_apply]; omega)
      (by rw [Equiv.symm_apply_apply]; omega)
    rw [Equiv.symm_apply_apply] at hsum_ru
    have hru_val : (r u).1 + 1 = I - (y.1 + 1) := by omega
    have hy_lt_I : y.1 + 1 < I := by omega
    have hIy_le_t : I - (y.1 + 1) ≤ t := by omega
    have hru_eq : r u = ⟨I - (y.1 + 1) - 1, by omega⟩ := by
      ext
      dsimp only
      omega
    have hsym_u : r.symm ⟨I - (y.1 + 1) - 1, by omega⟩ = u := by
      rw [← hru_eq, Equiv.symm_apply_apply]
    refine ⟨hy_lt_I, hIy_le_t, hru_val, ?_⟩
    rw [hsym_u, hu_val]
    omega
  -- Main uniqueness claim: every valid permutation `p` of `[k]` equals `p_ext`.
  have h_all_eq : ∀ p : Equiv.Perm (Fin k), IsValidFibPerm k p → p = p_ext := by
    intro p hp
    -- Step (iv): build valid permutation `p'` of `Fin t` closing detours with sum `I`.
    let p'_toFun : Fin t → Fin t := fun y =>
      if h : H ≤ (p ⟨y.1, by omega⟩).1 + 1 then
        ⟨I - (y.1 + 1) - 1, by
          have := h_AB p hp y h
          omega⟩
      else
        ⟨(p ⟨y.1, by omega⟩).1, by
          have := h_mem_R p hp ⟨y.1, by omega⟩ (Or.inl (by dsimp only; omega))
          omega⟩
    let p'_invFun : Fin t → Fin t := fun z =>
      if h : H ≤ (p.symm ⟨z.1, by omega⟩).1 + 1 then
        ⟨I - (z.1 + 1) - 1, by
          have := h_AB p.symm hp.symm z h
          omega⟩
      else
        ⟨(p.symm ⟨z.1, by omega⟩).1, by
          have := h_mem_R p.symm hp.symm ⟨z.1, by omega⟩ (Or.inl (by dsimp only; omega))
          omega⟩
    let p' : Equiv.Perm (Fin t) := {
      toFun := p'_toFun
      invFun := p'_invFun
      left_inv := by
        intro y
        by_cases h1 : H ≤ (p ⟨y.1, by omega⟩).1 + 1
        · have hAB := h_AB p hp y h1
          have h2 : H ≤ (p.symm ⟨I - (y.1 + 1) - 1, by omega⟩).1 + 1 := hAB.2.2.2
          dsimp only [p'_toFun, p'_invFun]
          simp only [h1, ↓reduceDIte]
          simp only [h2, ↓reduceDIte]
          ext
          dsimp only
          omega
        · have hmk : (⟨(p ⟨y.1, by omega⟩).1, by
              have := h_mem_R p hp ⟨y.1, by omega⟩ (Or.inl (by dsimp only; omega))
              omega⟩ : Fin k) = p ⟨y.1, by omega⟩ := by ext; rfl
          have h2 : ¬ H ≤ (p.symm ⟨(p ⟨y.1, by omega⟩).1, by
              have := h_mem_R p hp ⟨y.1, by omega⟩ (Or.inl (by dsimp only; omega))
              omega⟩).1 + 1 := by
            rw [hmk, Equiv.symm_apply_apply]
            dsimp only
            omega
          dsimp only [p'_toFun, p'_invFun]
          simp only [h1, ↓reduceDIte]
          simp only [h2, ↓reduceDIte]
          ext
          dsimp only
          rw [hmk, Equiv.symm_apply_apply]
      right_inv := by
        intro z
        by_cases h1 : H ≤ (p.symm ⟨z.1, by omega⟩).1 + 1
        · have hAB := h_AB p.symm hp.symm z h1
          have h2 : H ≤ (p ⟨I - (z.1 + 1) - 1, by omega⟩).1 + 1 := hAB.2.2.2
          dsimp only [p'_toFun, p'_invFun]
          simp only [h1, ↓reduceDIte]
          simp only [h2, ↓reduceDIte]
          ext
          dsimp only
          omega
        · have hmk : (⟨(p.symm ⟨z.1, by omega⟩).1, by
              have := h_mem_R p.symm hp.symm ⟨z.1, by omega⟩ (Or.inl (by dsimp only; omega))
              omega⟩ : Fin k) = p.symm ⟨z.1, by omega⟩ := by ext; rfl
          have h2 : ¬ H ≤ (p ⟨(p.symm ⟨z.1, by omega⟩).1, by
              have := h_mem_R p.symm hp.symm ⟨z.1, by omega⟩ (Or.inl (by dsimp only; omega))
              omega⟩).1 + 1 := by
            rw [hmk, Equiv.apply_symm_apply]
            dsimp only
            omega
          dsimp only [p'_toFun, p'_invFun]
          simp only [h1, ↓reduceDIte]
          simp only [h2, ↓reduceDIte]
          ext
          dsimp only
          rw [hmk, Equiv.apply_symm_apply]
    }
    have hp'_valid : IsValidFibPerm t p' := by
      intro y
      dsimp only [p', p'_toFun, Equiv.coe_fn_mk]
      split_ifs with h
      · have hAB := h_AB p hp y h
        dsimp only
        have hsum : (y.1 + 1) + (I - (y.1 + 1) - 1 + 1) = I := by omega
        rw [hsum]
        exact isFib_fib (by omega)
      · exact hp ⟨y.1, by omega⟩
    -- No element of `L` can be sent into `U` (`A = ∅`).
    have hA_empty : ∀ y : Fin t, ¬ H ≤ (p ⟨y.1, by omega⟩).1 + 1 := by
      intro y hyH
      have hAB := h_AB p hp y hyH
      have hforb := hnoI p' hp'_valid y
      dsimp only [p', p'_toFun, Equiv.coe_fn_mk] at hforb
      simp only [hyH, ↓reduceDIte] at hforb
      omega
    -- Symmetrically, no element of `L` can be hit from `U` (`B = ∅`).
    have hB_empty : ∀ z : Fin t, ¬ H ≤ (p.symm ⟨z.1, by omega⟩).1 + 1 := by
      intro z hzH
      have hAB := h_AB p.symm hp.symm z hzH
      exact hA_empty ⟨I - (z.1 + 1) - 1, by omega⟩ hAB.2.2.2
    -- Since `p'` is valid on `[t]`, `p' = p₀`.
    have hp'_eq : p' = p₀ := congrArg Subtype.val (hp₀_uniq ⟨p', hp'_valid⟩)
    -- Conclude `p = p_ext` pointwise on `Fin k`.
    ext i
    dsimp only [p_ext, extendPerm, extendPermFun, Equiv.coe_fn_mk]
    split_ifs with hi
    · have hnotH := hA_empty ⟨i.1, hi⟩
      have hval := congrArg (fun q : Equiv.Perm (Fin t) => (q ⟨i.1, hi⟩).1) hp'_eq
      dsimp only [p', p'_toFun, Equiv.coe_fn_mk] at hval
      simp only [hnotH, ↓reduceDIte] at hval
      exact hval
    · dsimp only
      have hcases : (t < i.1 + 1 ∧ i.1 + 1 < H) ∨
          (H ≤ i.1 + 1 ∧ i.1 + 1 ≤ G) ∨ G < i.1 + 1 := by omega
      rcases hcases with ⟨hlo, hhi⟩ | ⟨hgeH, hleG⟩ | hgtG
      · have hsum := h_low_forced p hp i hlo hhi
        omega
      · have hmem := h_mem_R p hp i (Or.inr ⟨hgeH, hleG⟩)
        rcases hmem with hle_t | ⟨hpiH, hpiG⟩
        · exfalso
          have hz := hB_empty ⟨(p i).1, by omega⟩
          have hmk : (⟨(p i).1, by omega⟩ : Fin k) = p i := by ext; rfl
          rw [hmk, Equiv.symm_apply_apply] at hz
          exact hz hgeH
        · have hsum := h_UU p hp i hgeH hleG hpiH hpiG
          omega
      · have hsum := h_high p hp i hgtG
        omega
  -- Package uniqueness (`fibPermCount k = 1`) and absence of sum `G`.
  constructor
  · unfold fibPermCount
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨p_ext, hp_ext_valid⟩, ?_⟩
    rintro ⟨p, hp⟩
    exact Subtype.ext (h_all_eq p hp)
  · intro p hp i
    rw [h_all_eq p hp]
    dsimp only [p_ext, extendPerm, extendPermFun, Equiv.coe_fn_mk]
    split_ifs with hi
    · dsimp only
      have h1 : i.1 + 1 ≤ t := by omega
      have h2 : (p₀ ⟨i.1, hi⟩).1 + 1 ≤ t := (p₀ ⟨i.1, hi⟩).2
      omega
    · dsimp only
      omega

end FibSumPerm
