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
-/

noncomputable section Algebra_P3
open Ideal

variable {R : Type*} [CommRing R]

def J : Ideal R := sInf { I : Ideal R | IsMaximal I }

lemma elts_of_J (x : R) : x ∈ J ↔ ∀ I : Ideal R, IsMaximal I → x ∈ I := by
   constructor
   ·  intro xin I Imax
      simp only [J, Submodule.mem_sInf, Set.mem_setOf_eq] at xin
      apply xin
      exact Imax
   ·  intro hyp
      simp only [J, Submodule.mem_sInf, Set.mem_setOf_eq]
      exact hyp

lemma J_is_jacobson_bot : J = jacobson (⊥ : Ideal R) := by
   simp only [J, jacobson]
   simp

theorem alg_p3_a {x : R} (h : x ∈ J) : IsUnit (1 + x) := by
   rw [J_is_jacobson_bot] at h
   have : (1 + x) - 1 ∈ jacobson (⊥ : Ideal R) := by
      simp only [add_sub_cancel_left]; exact h
   apply isUnit_of_sub_one_mem_jacobson_bot
   exact this

theorem alg_p3_b (I : Ideal R) (hyp : ∀ y ∈ I, IsUnit (1+y) ) : I ≤ J := by
   intro x xI
   rw [J_is_jacobson_bot]
   have : ∀ r, x * r ∈ I := fun r ↦ IsTwoSided.mul_mem_of_left r xI
   have : ∀ r, IsUnit (x * r + 1) :=










end Algebra_P3
--- #min_imports
