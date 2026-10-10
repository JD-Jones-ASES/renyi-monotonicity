module

public import RenyiMonotonicity.ContactEvaluation
public import RenyiMonotonicity.ContactSplitting
public import RenyiMonotonicity.ContactOrientation

/-! Actual singleton-versus-repeated-parameter contact ordering. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- A stationary singleton lies strictly below a distinct repeated interior parameter;
the corresponding splitting curvature is strictly negative. -/
theorem stationary_singleton_lt_repeated {m : ℕ} (q p a : ℝ) (h : Fin m → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hpp : 0 < p) (hpHalf : p < 1/2)
    (ha : 0 < a) (haHalf : a ≤ 1/2) (hh : ∀ i, 0 < h i) (hhHalf : ∀ i, h i ≤ 1/2)
    (hpa : p ≠ a)
    (hzero : midpointFunctional q (tripleCoins p p a h)=0)
    (hstationary : ∀ i : Fin 3, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins p p a h) (⟨i.val,by omega⟩ : Fin (m+3)) t))
      ((tripleCoins p p a h) ⟨i.val,by omega⟩)=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins p p a h) ≤ midpointFunctional q r) :
    a < p ∧ polynomialGradientPairing q (tripleCoins p p a h)
      (bernoulliPolynomial (Fin.cons a h)*(X-1)^2) < 0 := by
  let P := tripleCoins p p a h
  let L := backgroundGradientLinearMap q P h
  have hPpos : ∀ i, 0 < P i := by
    intro i
    exact Fin.cases hpp (fun i => Fin.cases hpp (fun i => Fin.cases ha hh i) i) i
  have hPhalf : ∀ i, P i ≤ 1/2 := by
    intro i
    exact Fin.cases hpHalf.le (fun i => Fin.cases hpHalf.le (fun i => Fin.cases haHalf hhHalf i) i) i
  have hPone : ∀ i, P i < 1 := fun i => lt_of_le_of_lt (hPhalf i) (by norm_num)
  have hz (i : Fin 3) : polynomialGradientPairing q P
      (bernoulliPolynomial (omitCoin P ⟨i.val,by omega⟩))=0 := by
    have H := (bernoulliGradientPairing_omit_of_stationary q P hPpos hPone
      ⟨i.val,by omega⟩ hzero (hstationary i)).1
    simpa only [pow_zero,mul_one,Nat.cast_zero] using
      (polynomialGradientPairing_shift_eq q P (omitCoin P ⟨i.val,by omega⟩) 0).trans H
  have hA : L (coinFactor p*coinFactor a)=0 := by
    have H := hz 0
    change polynomialGradientPairing q P (bernoulliPolynomial (omitCoin P 0))=0 at H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hB : L (coinFactor p*coinFactor p)=0 := by
    have H := hz 2
    change polynomialGradientPairing q P (bernoulliPolynomial (omitCoin P ((0:Fin (m+1)).succ).succ))=0 at H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,omitCoin_cons_succ,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hP : L (coinFactor p*coinFactor p*coinFactor a)=0 := by
    have H := polynomialGradientPairing_euler q P hPpos hPone
    rw [hzero,mul_zero] at H
    simpa only [L,P,tripleCoins,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hm := linearMap_repeated_singleton_moments L p a hpp.ne' ha.ne' hpa hP hA hB
  have hwne : L 1 ≠ 0 := by
    intro hw
    obtain ⟨j,hj⟩ := polynomialGradientPairing_four_shifts_nonzero q P h hq0 hq1 hPpos hPhalf hh
      (fun i => lt_of_le_of_lt (hhHalf i) (by norm_num))
    have H := hm j.val (by omega)
    rw [hw,zero_mul] at H
    exact hj H
  have hξ : coinRoot p < 0 := by
    unfold coinRoot
    apply div_neg_of_neg_of_pos _ hpp
    linarith
  have hw : L 1 < 0 := by
    by_contra hw
    have hwpos := lt_of_le_of_ne (le_of_not_gt hw) (Ne.symm hwne)
    apply polynomialGradientPairing_not_positive_alternating q P h hq0 hq1 hPpos hPone hh
      (fun i => lt_of_le_of_lt (hhHalf i) (by norm_num))
    change 0 < L (X^0) ∧ L (X^1)<0 ∧ 0<L (X^2) ∧ L (X^3)<0
    rw [hm 0 (by omega),hm 1 (by omega),hm 2 (by omega),hm 3 (by omega)]
    refine ⟨by simpa using hwpos,by simpa using mul_neg_of_pos_of_neg hwpos hξ,?_,?_⟩
    · exact mul_pos hwpos (sq_pos_of_ne_zero hξ.ne)
    · exact mul_neg_of_pos_of_neg hwpos (by nlinarith [mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hξ.ne) hξ])
  have hC : L ((X-1)^2*coinFactor a) ≤ 0 := by
    have H := polynomialGradientPairing_splitting_nonpos q p (Fin.cons a h) hpp hpHalf
      (fun i => Fin.cases ha hh i) (fun i => Fin.cases haHalf hhHalf i) hmin
    simpa only [L,P,backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,
      bernoulliPolynomial_cons,coinFactor,pairCoins,tripleCoins,mul_comm,mul_left_comm,mul_assoc] using H
  have he := linearMap_repeated_singleton_curvature L p a hpp.ne' hm
  have hp3 : 0 < p^3 := pow_pos hpp 3
  have hap : a < p := by
    have H := mul_nonpos_of_nonneg_of_nonpos hp3.le hC
    rw [he] at H
    have : a ≤ p := by nlinarith
    exact lt_of_le_of_ne this (Ne.symm hpa)
  have hCstrict : L ((X-1)^2*coinFactor a) < 0 := by
    have H : (p-a)*L 1 < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr hap) hw
    rw [← he] at H
    exact neg_of_mul_neg_right H hp3.le
  refine ⟨hap,?_⟩
  simpa only [L,P,backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,
    bernoulliPolynomial_cons,coinFactor,mul_comm,mul_left_comm,mul_assoc] using hCstrict

end RenyiMonotonicity
