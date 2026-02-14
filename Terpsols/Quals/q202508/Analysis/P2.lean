/-
Copyright (c) 2026 Patrick Brosnan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Brosnan
-/

import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Tactic

/-!
# UMD Math Fall 2025 Analysis Qualifying Exam Problem 2

## Problem Statement

Let f be a meromorphic function on ℂ.
Suppose there are real numbers C, R > 0 and a positive
integer m such that

  |f(z)| ≤ C|z|^m

whenever |z| > R.
Prove that f is a rational function (i.e., the quotient
of two polynomials.)

## Solution

- `theorem rational_of_poly_bounded` solves Part 1.

-/

section mero_rational

open Topology WithTop Function.FactorizedRational Meromorphic


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]


def ev_poly_bndd (g : 𝕜 → 𝕜) :=
  ∃ C R : ℝ, ∃ m : ℕ, ∀ z : 𝕜, ‖z‖ > R → ‖g z‖  ≤ C * ‖z‖ ^ m

lemma ev_poly_bndd_of_prod {g h : 𝕜 → 𝕜} (bg : ev_poly_bndd g) (bh : ev_poly_bndd h) :
  ev_poly_bndd (fun z ↦ (g z) * (h z)) := by
  simp only [ev_poly_bndd, gt_iff_lt] at bg bh
  simp only [ev_poly_bndd]
  obtain ⟨C1, R1, m1, hyp1⟩ := bg
  obtain ⟨C2, R2, m2, hyp2⟩ := bh
  use C1 * C2
  use (max R1 R2)
  use m1 + m2
  intro z zgt
  have lt1 : ‖g z‖ ≤ C1 * ‖z‖ ^ m1 := by
    apply hyp1
    calc R1
      _≤ max R1 R2 := le_max_left R1 R2
      _< ‖z‖ := zgt
  have lt2 : ‖h z‖ ≤ C2 * ‖z‖ ^ m2 := by
    apply hyp2
    calc R2
      _≤ max R1 R2 := le_max_right R1 R2
      _< ‖z‖ := zgt
  sorry



#check add_le_add

/- An eventually polynomially bounded meromorphic function on 𝕜 which is in normal
   form everywhere is a rational function. -/
theorem rat_of_poly_bndd {f : ℂ → ℂ} (mnf : ∀ z : ℂ,  MeromorphicNFAt f z)
  (epb : ev_poly_bndd f) :
  ∃ d : ℂ → ℤ, f = fun z ↦ ∏ᶠ u, (z - u) ^ d u := by sorry





end mero_rational


#check Meromorphic.meromorphicAt
#check AnalyticAt.meromorphicNFAt
#check meromorphicNFAt_congr
#check MeromorphicNFAt



/-!

## Comments

This is an interesting problem to formalize because
the way Mathlib4 deals with the possible singular
values of meromorphic functions of one-variable
is different from the way most mathaticians deal with them.

In Mathlib4, a function f: U → ℂ from an open set to
ℂ is meromorhic at a point p ∈ U if its restriction
to a punctured neighborhood of p can be written
as (z - p)^n g for some integer n and function g which
is analytic on an open neighborhood of p.
See Mathlib.Analysis.Meromorphic.Basic.

The important point here is that the value of f at
p doesn't matter.

As a consequene of this point, there wind up being
too many distinct functions f: U → ℂ which are meromorphic
at every point in U because, given any such meromorphic
function f and a discrete set of points S ⊆ U,
we can change the values of f at the points of S
at random and get another meromorphic function.

I believe there are two ways to handle this problem
in normal (human) mathematics

1. Define a meromorphic function on U to be an
analytic function f: U → P, where P denotes
the Riemann sphere.  In other words, P = ℂ ∪ {∞}.

2. Define a meromorphic function to be, not a function
on U, but a section of a sheaf over U whose germs
consist of symbols g/h, where g and h are analytic
functions with h not identically zero.

The problem with 1 is that it only works in the
case of a single complex variable.
The problem with 2 is that it is abstract and
complicated.

One other problem with 1 is that the Riemann
sphere is not a ring (or even a group).
So additionand multiplication of meromoprhic functions
has to be define using considerations similar to those
in 2.

The import Mathlib.Analysis.Meromorphic.NormalForm
solve the problem in a different way from 1 and 2
that is more adapted to lean.  The idea is to
declare a meromorphic function f : U → ℂ to be
in normal form if, for all points p ∈ U, f is either
analytic at p, or f is not analytic and f(p) = 0.
Essentially the idea is to replace ∞ in the Riemann
sphere with 0.

So, for example, let f(z) = 1/z.  In the
Riemann sphere picture, we have f(0) = ∞.



-/
