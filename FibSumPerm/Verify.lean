/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FibSumPerm

/-!
# Axiom Verification Audit for `FibSumPerm`

Prints the Lean 4 kernel axioms used by every formalized theorem, lemma,
proposition, and corollary in `FibSumPerm`. A clean audit must show ONLY
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER
`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom axiom.
-/

-- Definitions, Fibonacci/Lucas structure, and Layman/Hajnal identities (Defs.lean)
#print axioms FibSumPerm.fib_step
#print axioms FibSumPerm.fib_pos_of_pos
#print axioms FibSumPerm.isFib_fib
#print axioms FibSumPerm.fib_ge_sub_one
#print axioms FibSumPerm.isFib_iff_bounded
#print axioms FibSumPerm.IsValidFibPerm.symm
#print axioms FibSumPerm.fibPermCount_zero
#print axioms FibSumPerm.fib_strictMono_from_two
#print axioms FibSumPerm.not_isFib_between
#print axioms FibSumPerm.eq_fib_of_isFib_between
#print axioms FibSumPerm.exists_fib_scale
#print axioms FibSumPerm.w_bounds
#print axioms FibSumPerm.w_add_w_add_one
#print axioms FibSumPerm.w_add_four
#print axioms FibSumPerm.two_mul_w_add_two_le
#print axioms FibSumPerm.M4_eq_w
#print axioms FibSumPerm.lucas_succ_eq_fib_add_fib
#print axioms FibSumPerm.lucas_add_four
#print axioms FibSumPerm.cassini_identity
#print axioms FibSumPerm.lucas_sq_sub_five_fib_sq
#print axioms FibSumPerm.lucas_sandwich_w

-- Extension Lemma, Existence, Two-Fibonacci Lower Bound, and Step Lemma (StepLemma.lean)
#print axioms FibSumPerm.extendPerm_last
#print axioms FibSumPerm.extendPerm_injective
#print axioms FibSumPerm.extendPerm_valid
#print axioms FibSumPerm.extension_count_ge
#print axioms FibSumPerm.fibPermCount_pos
#print axioms FibSumPerm.two_le_fibPermCount_of_two_fibs
#print axioms FibSumPerm.step_lemma

-- Hand cases, Hajnal Conjecture 1 (both directions), and Reshetnikov's floor form (Main.lean)
#print axioms FibSumPerm.fibPermCount_one
#print axioms FibSumPerm.valid_two_eq_swap
#print axioms FibSumPerm.fibPermCount_two
#print axioms FibSumPerm.no_sum_two_of_valid_two
#print axioms FibSumPerm.valid_three_eq_swap
#print axioms FibSumPerm.fibPermCount_three
#print axioms FibSumPerm.no_sum_three_of_valid_three
#print axioms FibSumPerm.fibPermCount_four
#print axioms FibSumPerm.fibPermCount_five
#print axioms FibSumPerm.fibPermCount_six
#print axioms FibSumPerm.two_le_fibPermCount_ten
#print axioms FibSumPerm.layman_unique_strong
#print axioms FibSumPerm.layman_unique_if
#print axioms FibSumPerm.layman_unique_only_if
#print axioms FibSumPerm.hajnal_conjecture_1
#print axioms FibSumPerm.hajnal_conjecture_1_M4
#print axioms FibSumPerm.w_sq_sandwich
#print axioms FibSumPerm.w_eq_floor_fib_div_sqrt5
