import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Data.ENNReal.Basic

noncomputable section Analysis_Problem_1

/-
Problem 1: Let A be a Lebesgue measurable subset of R with 0 < m(A) < ∞,
where m denotes the Lebesgue measure on R.
Prove that for any positive real number a < m(A), there exists a compact set K ⊂ A
such that m(K) = a.
-/

noncomputable section

open Set Filter MeasureTheory ENNReal TopologicalSpace
open scoped symmDiff Topology
open MeasureTheory.Measure TopologicalSpace


--- variable {α : Type*} [MeasurableSpace α]

variable {A : Set ℝ}
variable (a : NNReal)


#check (volume : Measure ℝ)

#check volume A
#check (volume : Measure ℝ) A
#check NNReal
#check ENNReal
#check volume.InnerRegular


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
