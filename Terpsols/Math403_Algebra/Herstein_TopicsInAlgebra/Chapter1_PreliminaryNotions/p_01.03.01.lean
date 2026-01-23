import Mathlib.Data.Nat.Prime.Basic
import MIL.Common
import Init.Data.Int.Basic

open BigOperators

#check  mul_right_eq_self₀

lemma l3_1a (a b : ℤ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := sq_eq_sq_iff_eq_or_eq_neg.mp h

lemma l3_1b (a b : ℤ) (h : a * b = a) : b =  (1 : ℤ) ∨ a = 0 := mul_right_eq_self₀.mp h

lemma l3_1c (a b : ℤ) (h : a * b = a) (nz : a ≠ 0) : b = 1 := Int.eq_one_of_mul_eq_self_right nz h

lemma l3_1d (a b : ℤ) (h : a * b = 1) : a = b := Int.eq_of_mul_eq_one h

lemma l3_1e (a b : ℤ) (h : a * b = 1) : a = 1 ∨ a = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h

theorem h3_1 (a b : ℤ) (dab : a ∣ b) (dba : b ∣ a) : a = b ∨ a = -b := by
  obtain ⟨k, kab⟩ := dab
  obtain ⟨j, jba⟩ := dba
  have aeq : a = a * (j * k) := by
    nth_rw 1[jba]
    nth_rw 1[kab]
    ring
  have beq : b = b * (j * k) := by
    nth_rw 1[kab]
    nth_rw 1[jba]
    ring
  by_cases bez : b = 0
  · left
    rw [jba]
    rw [bez]
    ring
  · have jk1 : j * k = 1 := l3_1c b (j * k) (id (Eq.symm beq)) bez
    have jeq : j = k :=  l3_1d j k jk1
    have jor : j = 1 ∨ j = -1 := l3_1e j k jk1
    by_cases j1 : j = 1
    · left
      rw [jba]
      rw [j1]
      ring
    · have : j = -1 := by tauto
      right
      rw [jba]
      rw [this]
      ring

#check lcm 3 4 
#eval lcm 3 4 
#eval lcm 3 (lcm 4 5)
#eval gcd 3 4 

#eval 3 / 2
#eval 3 % 2
#eval 5 % 3

def div (n k : Nat) (ok : k ≠ 0): Nat := 
  if h : n < k then 
    0
  else 
    1 + div (n-k) k ok

#eval div 7 3 (by norm_num)

#eval gcd 7 3
#eval Nat.gcd 7 3
