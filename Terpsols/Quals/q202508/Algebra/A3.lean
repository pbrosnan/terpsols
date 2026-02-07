/-
Copyright (c) 2026 Patrick Brosnan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Brosnan
-/
import Mathlib.RingTheory.Jacobson.Ideal
/-!
   # UMD Math Fall 2025 Algebra Qualifying Exam Problem 3

   ## Problem Statement

   Let R be a commutative ring with 1 and let J be the intersection of all the
   maximal ideals of R.

   1. Show that if x ∈ J then 1 + x is a unit in R.
   2. Let I be an ideal of R.  Suppose 1 + y is a unit for each y ∈ I.
      Show that I ⊆ J.

   ## Solution
   - `alg_p3_a` solves Part 1.
   - `alg_p3_b` solve Part 2.
   - `lemma elts_of_J` verifies that J as defined in the definition agrees with J as defined
      in the statement of the problem.
-/

noncomputable section Algebra_P3
open Ideal

variable {R : Type*} [CommRing R]

/- Define J as the infimum of the set of maximal ideals in the lattice of all ideals,
   as is usual in mathlib4. -/
def J : Ideal R := sInf { I : Ideal R | IsMaximal I }

/- Verify that the elements of J are exactly the elements in the intersection
   of all maximal ideals.  As in the statement of the problem. -/
lemma elts_of_J (x : R) : x ∈ J ↔ ∀ I : Ideal R, IsMaximal I → x ∈ I := by
   constructor
   ·  intro xin I Imax
      simp only [J, Submodule.mem_sInf, Set.mem_setOf_eq] at xin
      apply xin
      exact Imax
   ·  intro hyp
      simp only [J, Submodule.mem_sInf, Set.mem_setOf_eq]
      exact hyp

/- Show that J is the Jacobson radical of the bottom ideal, which is the
   language preferred by mathlib4. -/
lemma J_is_jacobson_bot : J = jacobson (⊥ : Ideal R) := by
   simp only [J, jacobson]
   simp

/- Part (a) of the problem. -/
theorem alg_p3_a {x : R} (h : x ∈ J) : IsUnit (1 + x) := by
   rw [J_is_jacobson_bot] at h
   have : (1 + x) - 1 ∈ jacobson (⊥ : Ideal R) := by
      simp only [add_sub_cancel_left]; exact h
   apply isUnit_of_sub_one_mem_jacobson_bot
   exact this

/- Part (b) of the problem. -/
theorem alg_p3_b (I : Ideal R) (hyp : ∀ y ∈ I, IsUnit (1 + y)) : I ≤ J := by
   intro x xI
   rw [J_is_jacobson_bot]
   have hypc : ∀ y ∈ I, IsUnit (y + 1) := by
      intro y yin
      rw [add_comm]
      exact (IsUnit.mem_submonoid_iff (1 + y)).mp (hyp y yin)
   have : ∀ r, x * r ∈ I := fun r ↦ IsTwoSided.mul_mem_of_left r xI
   have : ∀ r, IsUnit (x * r + 1) :=
      (fun r => hypc (x * r) (this r)
      )
   exact mem_jacobson_bot.mpr this

end Algebra_P3
--- We use min_imports to winnow down the needed imports.
--- #min_imports
