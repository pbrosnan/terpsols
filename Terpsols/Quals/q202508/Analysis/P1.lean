import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic


noncomputable section Analysis_Problem_1

/-
Problem 1: Let A be a Lebesgue measurable subset of R with 0 < m(A) < ∞,
where m denotes the Lebesgue measure on R.
Prove that for any positive real number a < m(A), there exists a compact set K ⊂ A
such that m(K) = a.
-/

open Set MeasureTheory

--- variable {α : Type*} [MeasurableSpace α]

variable {A : Set ℝ} {hA : MeasurableSet A}
variable (gt : 0 < volume A)
variable (lt : volume A < ⊤)
variable (a : NNReal)

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

#check (volume : Measure ℝ)

#check (Ico a b)
#check volume (Ico a b)
#check volume A
#check NNReal
#check ENNReal

example : (0 : ENNReal) < ⊤ := by norm_num
example : ¬((⊤ : ENNReal) < ⊤) := by norm_num
example (a : NNReal) : a < (⊤ : ENNReal) := ENNReal.coe_lt_top

theorem exist_compact_meas_lt (lta : a < volume A) : ∃ K : Set ℝ,
  K ⊆ A ∧ IsCompact K ∧ (a < volume K) := by sorry
