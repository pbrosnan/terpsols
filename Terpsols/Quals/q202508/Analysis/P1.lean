import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.OuterMeasure.Basic
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
#check edist_le_ofReal
#check edist_eq_enorm_sub

example : volume A = (volume : Measure ℝ) A := rfl
example : (0 : ENNReal) < ⊤ := by norm_num
example : ¬((⊤ : ENNReal) < ⊤) := by norm_num
example (a : NNReal) : a < (⊤ : ENNReal) := ENNReal.coe_lt_top
example : (edist (0 : ℝ) 1).toReal = 1 := by
  simp only [edist_zero_left, nnnorm_one, coe_one, toReal_one]
example {r s : ℝ} (h : r < s) : (edist r s).toReal = s - r := by
  rw [edist_eq_enorm_sub]
  norm_num
  simp [abs]
  linarith
example {r s : ℝ} : (edist r s) = (edist s r) := by
  exact edist_comm r s

lemma distabs (r s : ℝ) : (edist r s).toReal = |r - s| := by
 rw [edist_eq_enorm_sub]
 norm_num

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

lemma volint (r s : ℝ) : volume (Icc r s) = ofReal (s - r) :=
  volume_Icc

#check measure_mono

lemma vintK (r s : ℝ) (K : Set ℝ) : volume (K ∩ (Icc r s))
≤ ofReal (s - r ) := by
  calc volume (K ∩ (Icc r s))
    _≤ volume (Icc r s) := by
      refine measure_mono ?_
      exact inter_subset_right
    _= ofReal (s -  r) := by exact volint r s

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


lemma ccbints {x y : ℝ} : closedBall 0 y ⊆
  (closedBall 0 x) ∪ (Icc x y) ∪ (Icc (-y) (-x)) := by
  intro v vin
  -- simp_all only [mem_closedBall, dist_zero_right, norm_eq_abs, mem_union, mem_Ioc, mem_Ico]
  simp
  by_cases h : |v| ≤ x
  · left
    · left
      exact h
  by_cases k : 0 ≤ v
  · left
    right
    have : |v| = v := by exact abs_of_nonneg k
    -- rw [this] at vin
    simp only [not_le] at h
    rw [this] at h
    norm_num
  · right
    simp only [not_le] at k
    have : |v| = -v := by exact abs_of_neg k
    -- rw [this] at vin
    rw [this] at h
    simp only [not_le] at h
    constructor
    · exact neg_le.mp vin
    · exact lt_neg_of_lt_neg h

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
    have : volume (K ∩ closedBall 0 y ∪ K ∩ Icc y x) ≤ volume (K ∩ closedBall 0 y) + edist x y := by
      calc
    calc volume (K ∩ closedBall 0 x)
      _≤ volume ((K ∩ closedBall 0 y) ∪ (K ∩ Icc y x)
      ∪ (K ∩ Icc (-x) (-y))) := OuterMeasureClass.measure_mono volume Kcontb
      _≤ volume ((K ∩ closedBall 0 y) ∪ (K ∩ Icc y x))
        + volume (K ∩ Icc (-x) (-y)) := measure_union_le (K ∩ closedBall 0 y ∪ K ∩ Icc y x) (K ∩ Icc (-x) (-y))
      _≤  volume ((K ∩ closedBall 0 y) ∪ (K ∩ Icc y x)) + edist (-y) (-x) := by
        refine (ENNReal.add_le_add_iff_left ?_).mpr ?_
        ·

#check le_of_add_le_add_right

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
  have fzero : f 0 = 0 := by
    refine measure_inter_null_of_null_right K ?_
    exact
  have ivt : ∃ t : ℝ, t ∈ Ioo 0 |s| ∧ f t = a := by
    apply?
