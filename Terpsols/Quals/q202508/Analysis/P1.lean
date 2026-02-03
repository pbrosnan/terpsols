/-
Copyright (c) 2026 Patrick Brosnan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Brosnan
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# UMD Math Fall 2025 Analysis Qualifying Exam Problem 1

## Problem Statement

Let A be a Lebesgue measurable subset of R with 0 < m(A) < ∞,
where m denotes the Lebesgue measure on R.
Prove that, for any positive real number a < m(A), there exists a compact set K ⊂ A
such that m(K) = a.

## Solution 

  -  Solved in in `exists_compact_eq`

## Comment on Problem Statment 

  Note that the statement above, which is the same as the statement
  on the Qualifying Exam, makes
  the unnecessary assumption that 0 < m(A) < ∞.
  The theorem `exists_compact_eq` below proves
  the statement without the unnecessary assumption.
  In other words, theorem exists_compact_eq proves the following:

  Let A be a Lebesgue measurable subset of R,
  where m denotes the Lebesgue measure on R.
  For any positive real number a < m(A), there exists a compact set K ⊂ A
  such that m(K) = a.

## Idea behind solution 

  The mathematical idea behind the solution is that Lebesque
  measure is inner regular.  So, if a < m(A), there always
  exists a compact subset K₁ of A with a < m(K₁).
  Then the function f(r) = m(K₁ ∩ [-r, r]) is continuous
  with f(0) = 0 and f(r) = m(K₁) for r >> 0.
  So, by the Intermediate Value Theorem, we can find an r
  such that f(r) = a.
  Then K := K₁ ∩ [-r, r] is a compact subset of A
  satisfying m(K) = a.

  The main technical challenge in implementing this solution
  is dealing with the volumes of intervals in lean and continuity.
  In particular, for the continuity, mathlib4 seems to want
  to think in terms of edist(r,s), the distance
  between points r and s viewed as points in a metric space.
  On the other hand, volumes are reported as elements of ENNReal,
  the extended nonnegative real numbers: [0, ∞]
  Going back and forth between various notions of distance
  is the reason for most of the lemmas in the file.

  It seems likely that formulating the 
  problem in a more general setting (e.g., for n-dimensional
  space instead of just R) would, in fact, lead to a different
  and substantially simpler approach.
-/

noncomputable section Analysis_Problem


noncomputable section

open Set Filter MeasureTheory ENNReal TopologicalSpace MetricSpace
open scoped symmDiff Topology
open MeasureTheory
open MeasureTheory.Measure TopologicalSpace
open Metric
open ENNReal (ofReal)
open Real

--- variable {α : Type*} [MeasurableSpace α]

variable {A : Set ℝ}
variable (a : NNReal)

lemma volle (r s : ℝ) : volume (Icc r s) ≤ edist s r := by
  simp_all only [volume_Icc]
  rw [edist_eq_enorm_sub]
  exact ofReal_le_enorm (s - r)

lemma volKle (r s : ℝ) (K : Set ℝ) : volume (K ∩ Icc r s) ≤ edist s r := by
  have : K ∩ Icc r s ⊆ Icc r s := inter_subset_right
  calc volume (K ∩ Icc r s)
   _≤ volume (Icc r s) := OuterMeasureClass.measure_mono volume this
   _≤ edist s r := volle r s

lemma exist_compact_meas_lt (lta : a < volume A) (hyp : MeasurableSet A) : ∃ K : Set ℝ,
  K ⊆ A ∧ IsCompact K ∧ (a < volume K) := by
  have : (volume : Measure ℝ).InnerRegular := by
     exact InnerRegularCompactLTTop.instInnerRegularOfSigmaFinite
  apply MeasurableSet.exists_lt_isCompact
  ·  exact hyp
  ·  exact lta

lemma ball_int (r : ℝ) : closedBall (0 : ℝ) r = Icc (-r) r := by
  ext x
  constructor
  · intro xin
    simp only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at xin
    simp only [mem_Icc]
    exact abs_le.mp xin
  · intro xin
    simp_all only [mem_Icc, mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact abs_le.mpr xin

lemma volint (r s : ℝ) : volume (Icc r s) = ofReal (s - r) :=
  volume_Icc

lemma cbints {x y : ℝ} : closedBall 0 y ⊆
  (closedBall 0 x) ∪ (Ioc x y) ∪ (Ico (-y) (-x)) := by
  intro v vin
  simp_all only [mem_closedBall, dist_zero_right, norm_eq_abs, mem_union, mem_Ioc, mem_Ico]
  by_cases h : |v| ≤ x
  · left
    · left
      exact h
  by_cases k : 0 ≤ v
  · left
    right
    have : |v| = v := by exact abs_of_nonneg k
    rw [this] at vin
    simp only [not_le] at h
    rw [this] at h
    tauto
  · right
    simp only [not_le] at k
    have : |v| = -v := by exact abs_of_neg k
    rw [this] at vin
    rw [this] at h
    simp only [not_le] at h
    constructor
    · exact neg_le.mp vin
    · exact lt_neg_of_lt_neg h

lemma edisteq (x y : ℝ) : edist x y = edist (-y) (-x) := by
  rw[edist_comm]
  exact Eq.symm (edist_neg_neg y x)

lemma meascont (K : Set ℝ) : Continuous (fun r ↦
(volume (K ∩ closedBall (0 : ℝ) r))) := by
  refine continuous_of_le_add_edist 2 (fun a ↦ ?_) ?_
  · contrapose! a
    exact Ne.symm top_ne_ofNat
  · intro x y
    have cbcont : closedBall 0 x ⊆ closedBall 0 y ∪ Ioc y x ∪ Ico (-x) (-y) := cbints
    have Kcont : K ∩ closedBall 0 x ⊆ (K ∩ closedBall 0 y) ∪ (K ∩ Ioc y x)
      ∪ (K ∩ Ico (-x) (-y)) := by grind
    have Kcontb : K ∩ closedBall 0 x ⊆ (K ∩ closedBall 0 y) ∪ (K ∩ Icc y x)
      ∪ (K ∩ Icc (-x) (-y)) := by grind
    have : volume (K ∩ closedBall 0 y ∪ K ∩ Icc y x) ≤ volume (K ∩ closedBall 0 y) + edist x y :=
      calc volume (K ∩ closedBall 0 y ∪ K ∩ Icc y x)
        _≤ volume (K ∩ closedBall 0 y) + volume (K ∩ Icc y x) :=
          measure_union_le (K ∩ closedBall 0 y) (K ∩ Icc y x)
        _≤ volume (K ∩ closedBall 0 y) + edist x y := by
          apply add_le_add_right
          exact volKle y x K
    calc volume (K ∩ closedBall 0 x)
      _≤ volume ((K ∩ closedBall 0 y) ∪ (K ∩ Icc y x)
      ∪ (K ∩ Icc (-x) (-y))) := OuterMeasureClass.measure_mono volume Kcontb
      _≤ volume ((K ∩ closedBall 0 y) ∪ (K ∩ Icc y x))
        + volume (K ∩ Icc (-x) (-y)) :=
          measure_union_le (K ∩ closedBall 0 y ∪ K ∩ Icc y x) (K ∩ Icc (-x) (-y))
      _≤  volume ((K ∩ closedBall 0 y) ∪ (K ∩ Icc y x)) + edist (-y) (-x) := by
        apply add_le_add_right
        exact volKle (-x) (-y) K
      _≤ volume ((K ∩ closedBall 0 y))  + volume (K ∩ Icc y x) + edist (-y) (-x) := by
        apply add_le_add_left
        exact measure_union_le (K ∩ closedBall 0 y) (K ∩ Icc y x)
      _≤ volume ((K ∩ closedBall 0 y))  + edist x y + edist (-y) (-x) := by
          apply add_le_add_left
          apply add_le_add_right
          exact volKle y x K
      _≤ volume ((K ∩ closedBall 0 y))  + 2 * edist x y := by
        rw [add_assoc]
        apply add_le_add_right
        rw [← edisteq]
        apply ge_of_eq
        ring

lemma volpt :  volume (closedBall (0 : ℝ) 0) = 0 := by
  have : closedBall (0 : ℝ) 0 = Icc 0 0 := by
    ext x
    norm_num
  rw [this]
  simp only [Icc_self, measure_singleton]

theorem exists_compact_eq (lta : a < volume A) (hyp : MeasurableSet A) :
∃ K : Set ℝ, K ⊆ A ∧ IsCompact K ∧ (a = volume K) := by
  obtain ⟨K, Ksub, Kcom, alt⟩ := exist_compact_meas_lt a lta hyp
  let f := (fun r ↦ (volume (K ∩ closedBall (0 : ℝ) r)))
  have cont : Continuous f := meascont K
  have : ∃ s : ℝ,  K ⊆ closedBall (0 : ℝ) s := by
    refine (isBounded_iff_subset_closedBall 0).mp ?_
    exact IsCompact.isBounded Kcom
  obtain ⟨s, Kin⟩ := this
  have Kinab : K ⊆ closedBall 0 |s| :=
    calc K
      _⊆ closedBall 0 s := Kin
      _⊆ closedBall 0 |s| := by
        refine closedBall_subset_closedBall ?_
        exact le_abs_self s
  have Kempt : K \ closedBall 0 |s| = ∅ := diff_eq_empty.mpr Kinab
  have fas : f |s| = volume K := by
    refine measure_inter_conull' ?_
    rw [Kempt]
    exact OuterMeasureClass.measure_empty volume
  have zls : 0 ≤ |s| := abs_nonneg s
  have ivtml : Icc (f 0) (f |s|) ⊆ f '' Icc 0 |s| := by
    refine intermediate_value_Icc zls ?_
    exact Continuous.continuousOn cont
  have : f 0 = 0 := by
    refine measure_inter_null_of_null_right K ?_
    exact volpt
  have ain : ↑a ∈ Icc (f 0) (f |s|) := by
    refine mem_Icc.mpr ?_
    constructor
    · rw[this]
      simp
    · rw[fas]
      exact Std.le_of_lt alt
  have  : ∃ t : ℝ, t ∈ Icc 0 |s| ∧ f t = a := by
    refine (mem_image f (Icc 0 |s|) ↑a).mp ?_
    exact (mem_image f (Icc 0 |s|) ↑a).mpr (ivtml ain)
  obtain ⟨t, tin, foft⟩ := this
  use K ∩ closedBall 0 t
  constructor
  · calc K ∩ closedBall 0 t
      _⊆ K := inter_subset_left
      _⊆ A := Ksub
  · constructor
    · refine IsCompact.inter_right Kcom ?_
      exact isClosed_closedBall
    · rw[← foft]
