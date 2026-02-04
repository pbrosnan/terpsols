/-
Copyright (c) 2026 Patrick Brosnan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Brosnan
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

/-!
   # UMD Math Fall 2025 Algebra Qualifying Exam Problem 3

   ## Problem Statement

   Let R be a commutative ring with 1 and let J be the intersection of all the
   maximal ideals of R.

   1. Show that if x ∈ J then 1 + x is a unit in R.
   2. Let I be an ideal of R.  Suppose 1 + y is a unit for each y ∈ I.
      Show that I ⊆ J.

   ## Solution
   - Part 1 is solved in `alg_p3_a`
   - Part 2 is solved in `alg_p3_b`
-/
