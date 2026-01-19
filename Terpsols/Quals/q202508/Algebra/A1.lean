import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

noncomputable section Algebra_Problem_1
open Subgroup
open Function
open MonoidHom

/-
   Problem 1: Let G be a group and let N be a normal subgroup.  Let
   C = { g ∈ G | gng⁻¹ = n for all n ∈ N}.
   (a) Show that C is a normal subgroup of G.
   (b) Show that if N is finite then C has finite index in G. (Hint: Aut(N) is finite.)
-/

/-
  Solution is in theorem alg_p1_b at the end of the file. 
-/

variable {G : Type*} [Group G]
variable (N : Subgroup G)

/- Defining Centralizer by hand because it is defined in the problem statement
   One issue here is that the problem statement asks us to prove that the centralizer is a
   subgroup, while, for lean, the centralizer is already defined as a subgroup in the library, mathlib4.
   Another issue is that, in the problem statement, the centralizer is defined in terms of  
   conjugation, while, in mathlib4, centralizers are defined for arbitrary magmas (without 
   using conjugation).
-/

def Cent : Subgroup G where
    carrier := { g : G | ∀ n, n ∈ N → g * n * g⁻¹ = n }
    one_mem' := by simp
    mul_mem' := by
        intro a b ain bin n nin
        have mulout : a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        rw [mulout]
        have bmul : b * n * b⁻¹ = n := bin n nin
        rw [bmul]
        exact ain n nin
    inv_mem' := by
        intro x xin n nin
        have : x * n * x⁻¹ = n := xin n nin
        nth_rw 1[← this]
        group

/-
   Proof that Cent as defined in the problem agrees with centralizer as defined in
   Mathlib4, which is in terms of the centralizer of a subset of a magma.
-/

theorem cent_is_centralizer : Cent N = Subgroup.centralizer N := by
    ext x
    constructor
    ·   intro xin g gin
        simp only [Cent] at xin
        have : x * g * x⁻¹ = g := xin g gin
        exact mul_eq_of_eq_mul_inv (id (Eq.symm this))
    ·   intro xin g gcong
        have : ∀ m ∈ N, m * x = x * m := Set.mem_centralizer_iff.mp xin
        have : g * x = x * g := this g gcong
        exact Eq.symm (eq_mul_inv_of_mul_eq (xin g gcong))

/- Proof of Part (a) of the Algebra Qual Problem 1 -/

theorem alg_p1_a [N.Normal] : (Cent N : Subgroup G).Normal := by
    have ce : Cent N = Subgroup.centralizer N := cent_is_centralizer N
    rw[ce]
    infer_instance

/- Lemma for proof of part (b) comparing the relative indexes of two tops.
   One is the top subgroup of G (i.e., what humans would call G).
   The other is the top subgroup of the top subgroup of G regarded as a group.
   Purely a Lean Mathlib4 thing.  But we have to do it. -/

lemma tiptop (H : Subgroup G) : (H.subgroupOf ⊤).relIndex ⊤ = H.relIndex ⊤ := by
    calc (H.subgroupOf (⊤ : Subgroup G)).relIndex ⊤
        _= (H.subgroupOf ⊤).index := relIndex_top_right (H.subgroupOf ⊤)
        _=  H.relIndex ⊤ := rfl

/- Proof of Part (b) of the Algebra Qual -/

theorem alg_p1_b (N : Subgroup G) (hyp : N.Normal) [Finite N] : (Cent N).FiniteIndex := by
    have nrmlzr : N.normalizer = ⊤ := normalizer_eq_top_iff.mpr hyp
    have relindN : relIndex N.normalizer ⊤ = 1 := by
        refine relIndex_eq_one.mpr ?_
        exact le_normalizer_of_normal
    have finaut : Finite (MulAut N) := MulEquiv.finite_right
    rw[cent_is_centralizer]
    refine finiteIndex_iff_finite_quotient.mpr ?_
    have nker : N.normalizerMonoidHom.ker =
        (Subgroup.centralizer N).subgroupOf N.normalizer := normalizerMonoidHom_ker N
    have finrange : Finite N.normalizerMonoidHom.range
        := instFiniteSubtypeMem N.normalizerMonoidHom.range
    have isothm : N.normalizer ⧸ N.normalizerMonoidHom.ker ≃* N.normalizerMonoidHom.range
        := QuotientGroup.quotientKerEquivRange N.normalizerMonoidHom
    have finquot : Finite (N.normalizer ⧸ N.normalizerMonoidHom.ker)
        := finite_quotient_of_finiteIndex
    have normquotnz : ((N.normalizerMonoidHom.ker).subgroupOf (⊤)).index ≠ 0
        := Subgroup.FiniteIndex.index_ne_zero
    have relnz : relIndex (N.normalizerMonoidHom.ker) (⊤) ≠ 0 := normquotnz
    rw [nker] at relnz
    rw [nrmlzr] at relnz
    have tptp : ((centralizer ↑N).subgroupOf (⊤ : Subgroup G)).relIndex ⊤
        = (centralizer ↑N).relIndex (⊤ : Subgroup G) := by
        apply tiptop
    have nrel : (centralizer ↑(N : Subgroup G)).relIndex (⊤ : Subgroup G) ≠ 0 := by
        rw [← tptp]
        exact relnz
    rw [Subgroup.relIndex_top_right] at nrel
    exact index_ne_zero_iff_finite.mp nrel

#min_imports

end Algebra_Problem_1
