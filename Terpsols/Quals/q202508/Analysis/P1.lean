import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Defs


noncomputable section Analysis_Problem

/-
Problem 1: Let A be a Lebesgue measurable subset of R with 0 < m(A) < ∞,
where m denotes the Lebesgue measure on R.
Prove that for any positive real number a < m(A), there exists a compact set K ⊂ A
such that m(K) = a.
-/

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

#check (volume : Measure ℝ)
#check volume A
#check (volume : Measure ℝ) A
#check NNReal
#check ENNReal
#check volume.InnerRegular
#check Icc
#check closedBall
#check volume_Icc
#check ofReal

example : volume A = (volume : Measure ℝ) A := rfl
example : (0 : ENNReal) < ⊤ := by norm_num
example : ¬((⊤ : ENNReal) < ⊤) := by norm_num
example (a : NNReal) : a < (⊤ : ENNReal) := ENNReal.coe_lt_top

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

lemma compact_in_ball (K : Set ℝ) (com : IsCompact K) : ∃ r : ℝ,
K ⊆ Icc (-r) r := by
  have : ∃ r,  K ⊆ closedBall (0 : ℝ) r := by
    apply (isBounded_iff_subset_closedBall (0 : ℝ)).mp
    exact IsCompact.isBounded com
  obtain ⟨r, Kcont⟩ := this
  use r
  rw [← ball_int]
  exact Kcont

lemma intcompact (J K : Set ℝ) (cJ : IsCompact J) (cK : IsCompact K) :
IsCompact (J ∩ K) := by
  have : IsClosed K := IsCompact.isClosed cK
  exact IsCompact.inter_right cJ this

lemma compactmeas (K : Set ℝ) (cK : IsCompact K) : MeasurableSet K := by
  exact IsCompact.measurableSet cK

def v (r : NNReal) : ENNReal := volume (closedBall (0 : ℝ) r)

lemma volint (r s : ℝ) : volume (Icc r s)  = ofReal (s - r) :=
  volume_Icc

-- def measfun (K : Set ℝ) (r : NNReal) : ENNReal := volume (K ∩ (Icc (-r) r))

lemma meascont (K : Set ℝ) : Continuous (fun r ↦
(volume (K ∩ closedBall (0 : ℝ) r))) := by
  apply?

theorem exists_compact_eq (lta : a < volume A) (hyp : MeasurableSet A) :
∃ K : Set ℝ, K ⊆ A ∧ IsCompact K ∧ (a = volume K) := by
  obtain ⟨K, Ksub, Kcom, alt⟩ := exist_compact_meas_lt a lta hyp
  sorry
