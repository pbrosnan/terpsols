/-
Copyright (c) 2026 Patrick Brosnan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Brosnan
-/
import Mathlib.Analysis.Normed.Ring.Lemmas
/-!
    # Herstein Topics in Algebra.  Problem 1.3.1:
    
    # Problem Statement 

    If a ∣ b and b ∣ a, show that a = ± b.
    
    # Solution 
      - Solved in `h3_1`.
-/

open BigOperators


lemma l3_1c (a b : ℤ) (h : a * b = a) (nz : a ≠ 0) : b = 1 := Int.eq_one_of_mul_eq_self_right nz h

lemma l3_1d (a b : ℤ) (h : a * b = 1) : a = b := Int.eq_of_mul_eq_one h

lemma l3_1e (a b : ℤ) (h : a * b = 1) : a = 1 ∨ a = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h

theorem h3_1 (a b : ℤ) (dab : a ∣ b) (dba : b ∣ a) : a = b ∨ a = -b := by
  obtain ⟨k, kab⟩ := dab
  obtain ⟨j, jba⟩ := dba
  have aeq : a = a * (j * k) := by
    nth_rw 1[jba]
    nth_rw 1[kab]
    ring
  have beq : b = b * (j * k) := by
    nth_rw 1[kab]
    nth_rw 1[jba]
    ring
  by_cases bez : b = 0
  · left
    rw [jba]
    rw [bez]
    ring
  · have jk1 : j * k = 1 := l3_1c b (j * k) (id (Eq.symm beq)) bez
    have jeq : j = k :=  l3_1d j k jk1
    have jor : j = 1 ∨ j = -1 := l3_1e j k jk1
    by_cases j1 : j = 1
    · left
      rw [jba]
      rw [j1]
      ring
    · have : j = -1 := by tauto
      right
      rw [jba]
      rw [this]
      ring
