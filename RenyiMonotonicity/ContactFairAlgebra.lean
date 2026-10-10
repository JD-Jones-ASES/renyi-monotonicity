module

public import RenyiMonotonicity.ContactTwoRoots

/-! Evaluation-weight signs forced by the fair-coordinate and splitting conditions. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- The repeated-interior/fair case has two nonnegative evaluation weights. -/
theorem linearMap_repeated_fair_weights (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℝ) (hp : 0 < p) (hpHalf : p < 1/2)
    (hP : L (coinFactor p*coinFactor p*coinFactor (1/2))=0)
    (hA : L (coinFactor p*coinFactor (1/2))=0)
    (hfair : 0 ≤ L (coinFactor p*coinFactor p))
    (hC : L ((X-1)^2*coinFactor (1/2)) ≤ 0) :
    ∃ w v : ℝ, 0 ≤ w ∧ 0 ≤ v ∧ ∀ j ≤ 3, L (X^j)=w*coinRoot p^j+v*(-1)^j := by
  have ht : L ((coinFactor p*coinFactor (1/2))*(X-1))=0 := by
    rw [show coinFactor p*coinFactor p*coinFactor (1/2) = (coinFactor p*coinFactor (1/2))*coinFactor p by ring,
      linearMap_mul_coinFactor,hA,zero_add] at hP
    exact (mul_eq_zero.mp hP).resolve_left hp.ne'
  have hz (j : ℕ) (hj : j+2≤3) : L (coinFactor p*coinFactor (1/2)*X^j)=0 := by
    have : j ≤ 1 := by omega
    interval_cases j
    · simpa using hA
    · rw [show coinFactor p*coinFactor (1/2)*X^1 = coinFactor p*coinFactor (1/2)+
        (coinFactor p*coinFactor (1/2))*(X-1) by ring,map_add,hA,ht,add_zero]
  obtain ⟨w,v,hm⟩ := linearMap_two_factor_moments L p (1/2) hp.ne' (by norm_num) hpHalf.ne 3 hz
  have hhalfroot : coinRoot (1/2) = -1 := by norm_num [coinRoot]
  have hfairEq : L (coinFactor p*coinFactor p)=v*(1-2*p)^2 := by
    have H := linearMap_eq_two_eval L (coinRoot p) (coinRoot (1/2)) w v 3 hm
      (coinFactor p*coinFactor p) (by unfold coinFactor; compute_degree; norm_num)
    rw [eval_mul,eval_mul,coinFactor_eval_root p hp.ne',hhalfroot,coinFactor_eval] at H
    convert H using 1; ring
  have hv : 0 ≤ v := by
    rw [hfairEq] at hfair
    exact nonneg_of_mul_nonneg_left hfair (sq_pos_of_ne_zero (by linarith : 1-2*p ≠ 0))
  have hCeq : L ((X-1)^2*coinFactor (1/2)) =
      w*(coinRoot p-1)^2*((coinFactor (1/2)).eval (coinRoot p)) := by
    have H := linearMap_eq_two_eval L (coinRoot p) (coinRoot (1/2)) w v 3 hm
      ((X-1)^2*coinFactor (1/2)) (by unfold coinFactor; compute_degree)
    simp only [eval_mul,eval_pow,eval_sub,eval_X,eval_one,coinFactor_eval_root (1/2) (by norm_num),
      mul_zero,add_zero] at H
    simpa only [mul_assoc] using H
  have hroot : coinRoot p < 0 := by unfold coinRoot; apply div_neg_of_neg_of_pos _ hp; linarith
  have hfeval : (coinFactor (1/2)).eval (coinRoot p) < 0 := by
    have he : (coinFactor (1/2)).eval (coinRoot p)=(2*p-1)/(2*p) := by
      rw [coinFactor_eval]
      unfold coinRoot
      field_simp
      ring
    rw [he]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hw : 0 ≤ w := by
    rw [hCeq] at hC
    have hn : (coinRoot p-1)^2*((coinFactor (1/2)).eval (coinRoot p)) < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (by linarith)) hfeval
    rw [mul_assoc] at hC
    exact nonneg_of_mul_nonpos_left hC hn
  refine ⟨w,v,hw,hv,?_⟩
  simpa only [hhalfroot] using hm

/-- Two distinct stationary interior factors leave only evaluation at the fair root. -/
theorem linearMap_distinct_fair_moments (L : ℝ[X] →ₗ[ℝ] ℝ) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hP : L (coinFactor (1/2)*coinFactor a*coinFactor b)=0)
    (hA : L (coinFactor (1/2)*coinFactor a)=0)
    (hB : L (coinFactor (1/2)*coinFactor b)=0) :
    ∀ j ≤ 3, L (X^j)=L 1*(-1)^j := by
  rw [linearMap_mul_coinFactor] at hA hB
  have ht : L (coinFactor (1/2)*(X-1))=0 := by
    apply (mul_eq_zero.mp (show (a-b)*L (coinFactor (1/2)*(X-1))=0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hab
  have hf : L (coinFactor (1/2))=0 := by rw [ht] at hA; simpa only [mul_zero,add_zero] using hA
  rw [linearMap_mul_coinFactor] at hP
  have hsq : L (coinFactor (1/2)*(X-1)^2)=0 := by
    have he : L (coinFactor (1/2)*coinFactor a*(X-1)) =
        L (coinFactor (1/2)*(X-1))+a*L (coinFactor (1/2)*(X-1)^2) := by
      rw [show coinFactor (1/2)*coinFactor a*(X-1) = (coinFactor (1/2)*(X-1))*coinFactor a by ring,
        linearMap_mul_coinFactor]
      rw [show coinFactor (1/2)*(X-1)*(X-1)=coinFactor (1/2)*(X-1)^2 by ring]
    rw [linearMap_mul_coinFactor,hf,ht,he] at hP
    rw [ht] at hP
    simpa only [add_zero,mul_zero,zero_add,mul_eq_zero,ha,hb,false_or] using hP
  have hm := linearMap_factor_moments L (1/2) (by norm_num) 3 (by
    intro j hj
    interval_cases j
    · simpa using hf
    · rw [show coinFactor (1/2)*X^1 = coinFactor (1/2)+coinFactor (1/2)*(X-1) by ring,map_add,hf,ht,add_zero]
    · rw [show coinFactor (1/2)*X^2 = coinFactor (1/2)+(2:ℝ) • (coinFactor (1/2)*(X-1))+
        coinFactor (1/2)*(X-1)^2 by simp only [smul_eq_C_mul,map_ofNat]; ring]
      simp only [map_add,map_smul,hf,ht,hsq,smul_zero,add_zero])
  norm_num [coinRoot] at hm
  exact hm

end RenyiMonotonicity
