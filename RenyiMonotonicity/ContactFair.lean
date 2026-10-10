module

public import RenyiMonotonicity.ContactFairAlgebra
public import RenyiMonotonicity.ContactConditions
public import RenyiMonotonicity.ContactOrientation
public import RenyiMonotonicity.ContactSplitting

/-! Actual exclusion of fair parameters from the two possible nontrivial contact patterns. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

lemma polynomialGradientPairing_not_nonnegative_twoRoots {m : ℕ} (q : ℝ) (P : Fin (m+3) → ℝ)
    (h : Fin m → ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hp : ∀ i, 0 < P i) (hpHalf : ∀ i, P i ≤ 1/2)
    (hh : ∀ i, 0 < h i) (hhHalf : ∀ i, h i ≤ 1/2)
    (x y w v : ℝ) (hx : x<0) (hy : y<0) (hw : 0≤w) (hv : 0≤v)
    (hm : ∀ j≤3, backgroundGradientLinearMap q P h (X^j)=w*x^j+v*y^j) : False := by
  have hsum : 0 < w+v := by
    by_contra hc
    have hw0 : w=0 := by linarith
    have hv0 : v=0 := by linarith
    obtain ⟨j,hj⟩ := polynomialGradientPairing_four_shifts_nonzero q P h hq0 hq1 hp hpHalf hh
      (fun i => lt_of_le_of_lt (hhHalf i) (by norm_num))
    have H := hm j.val (by omega)
    rw [hw0,hv0,zero_mul,zero_mul,add_zero] at H
    exact hj H
  apply polynomialGradientPairing_not_positive_alternating q P h hq0 hq1 hp
    (fun i => lt_of_le_of_lt (hpHalf i) (by norm_num)) hh
    (fun i => lt_of_le_of_lt (hhHalf i) (by norm_num))
  change 0 < backgroundGradientLinearMap q P h (X^0) ∧
    backgroundGradientLinearMap q P h (X^1)<0 ∧ 0<backgroundGradientLinearMap q P h (X^2) ∧
      backgroundGradientLinearMap q P h (X^3)<0
  rw [hm 0 (by omega),hm 1 (by omega),hm 2 (by omega),hm 3 (by omega)]
  have hcase : 0<w ∨ 0<v := by by_contra hn; push Not at hn; linarith
  refine ⟨by simpa using hsum,?_,?_,?_⟩
  · simp only [pow_one]
    rcases hcase with hw'|hv'
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hw' hx) (mul_nonpos_of_nonneg_of_nonpos hv hy.le)
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hw hx.le) (mul_neg_of_pos_of_neg hv' hy)
  · rcases hcase with hw'|hv'
    · exact add_pos_of_pos_of_nonneg (mul_pos hw' (sq_pos_of_ne_zero hx.ne)) (mul_nonneg hv (sq_nonneg y))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hw (sq_nonneg x)) (mul_pos hv' (sq_pos_of_ne_zero hy.ne))
  · have hx3 : x^3<0 := by nlinarith [mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hx.ne) hx]
    have hy3 : y^3<0 := by nlinarith [mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hy.ne) hy]
    rcases hcase with hw'|hv'
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hw' hx3) (mul_nonpos_of_nonneg_of_nonpos hv hy3.le)
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hw hx3.le) (mul_neg_of_pos_of_neg hv' hy3)

/-- A fair coin cannot coexist with two equal interior coins at an actual zero minimum. -/
theorem no_fair_repeated_contact {m : ℕ} (q p : ℝ) (h : Fin m → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hpp : 0<p) (hpHalf : p<1/2)
    (hh : ∀ i, 0<h i) (hhHalf : ∀ i, h i≤1/2)
    (hzero : midpointFunctional q (tripleCoins p p (1/2) h)=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins p p (1/2) h) ≤ midpointFunctional q r) : False := by
  let P := tripleCoins p p (1/2) h
  let L := backgroundGradientLinearMap q P h
  have hp : ∀ i, 0<P i := fun i => Fin.cases hpp (fun i => Fin.cases hpp (fun i => Fin.cases (by change 0<(1/2:ℝ); norm_num) hh i) i) i
  have hpH : ∀ i, P i≤1/2 := fun i => Fin.cases hpHalf.le (fun i => Fin.cases hpHalf.le (fun i => Fin.cases le_rfl hhHalf i) i) i
  have hp1 : ∀ i, P i<1 := fun i => lt_of_le_of_lt (hpH i) (by norm_num)
  have hstationary := midpoint_deriv_zero_of_min q P (fun i => ⟨(hp i).le,hpH i⟩) 0 hpp hpHalf hmin
  have hA : L (coinFactor p*coinFactor (1/2))=0 := by
    have H := (bernoulliGradientPairing_omit_of_stationary q P hp hp1 0 hzero hstationary).1
    have H' := (polynomialGradientPairing_shift_eq q P (omitCoin P 0) 0).trans H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,pow_zero,mul_one,one_mul,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H'
  have hP : L (coinFactor p*coinFactor p*coinFactor (1/2))=0 := by
    have H := polynomialGradientPairing_euler q P hp hp1
    rw [hzero,mul_zero] at H
    simpa only [L,P,tripleCoins,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hfair : 0≤L (coinFactor p*coinFactor p) := by
    have hd := midpoint_deriv_nonpos_of_min_fair q P hp hpH ((0:Fin (m+1)).succ).succ rfl hmin
    have H := bernoulliGradientPairing_omit_nonneg q P hp hp1 ((0:Fin (m+1)).succ).succ hzero hd
    have he := polynomialGradientPairing_shift_eq q P (omitCoin P ((0:Fin (m+1)).succ).succ) 0
    have H' : 0≤polynomialGradientPairing q P (bernoulliPolynomial (omitCoin P ((0:Fin (m+1)).succ).succ)) := by
      have he' := he
      simp only [pow_zero,mul_one,Nat.cast_zero] at he'
      rw [he']; exact H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,omitCoin_cons_succ,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H'
  have hC : L ((X-1)^2*coinFactor (1/2))≤0 := by
    have H := polynomialGradientPairing_splitting_nonpos q p (Fin.cons (1/2) h) hpp hpHalf
      (fun i => Fin.cases (by change 0<(1/2:ℝ); norm_num) hh i) (fun i => Fin.cases le_rfl hhHalf i) hmin
    simpa only [L,P,backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,
      bernoulliPolynomial_cons,coinFactor,pairCoins,tripleCoins,mul_comm,mul_left_comm,mul_assoc] using H
  obtain ⟨w,v,hw,hv,hm⟩ := linearMap_repeated_fair_weights L p hpp hpHalf hP hA hfair hC
  exact polynomialGradientPairing_not_nonnegative_twoRoots q P h hq0 hq1 hp hpH hh hhHalf
    (coinRoot p) (-1) w v (by unfold coinRoot; apply div_neg_of_neg_of_pos _ hpp; linarith)
    (by norm_num) hw hv hm

/-- A fair coin cannot coexist with two distinct interior coins at an actual zero minimum. -/
theorem no_fair_distinct_contact {m : ℕ} (q a b : ℝ) (h : Fin m → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (ha : 0<a) (haHalf : a<1/2)
    (hb : 0<b) (hbHalf : b<1/2) (hab : a≠b)
    (hh : ∀ i, 0<h i) (hhHalf : ∀ i, h i≤1/2)
    (hzero : midpointFunctional q (tripleCoins a b (1/2) h)=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins a b (1/2) h) ≤ midpointFunctional q r) : False := by
  let P := tripleCoins a b (1/2) h
  let L := backgroundGradientLinearMap q P h
  have hp : ∀ i, 0<P i := fun i => Fin.cases ha (fun i => Fin.cases hb
    (fun i => Fin.cases (by change 0<(1/2:ℝ); norm_num) hh i) i) i
  have hpH : ∀ i, P i≤1/2 := fun i => Fin.cases haHalf.le (fun i => Fin.cases hbHalf.le
    (fun i => Fin.cases le_rfl hhHalf i) i) i
  have hp1 : ∀ i, P i<1 := fun i => lt_of_le_of_lt (hpH i) (by norm_num)
  have hA : L (coinFactor (1/2)*coinFactor b)=0 := by
    have hd := midpoint_deriv_zero_of_min q P (fun i => ⟨(hp i).le,hpH i⟩) 0 ha haHalf hmin
    have H := (bernoulliGradientPairing_omit_of_stationary q P hp hp1 0 hzero hd).1
    have H' := (polynomialGradientPairing_shift_eq q P (omitCoin P 0) 0).trans H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,pow_zero,mul_one,one_mul,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H'
  have hB : L (coinFactor (1/2)*coinFactor a)=0 := by
    have hd := midpoint_deriv_zero_of_min q P (fun i => ⟨(hp i).le,hpH i⟩) (0:Fin (m+2)).succ hb hbHalf hmin
    have H := (bernoulliGradientPairing_omit_of_stationary q P hp hp1 (0:Fin (m+2)).succ hzero hd).1
    have H' := (polynomialGradientPairing_shift_eq q P (omitCoin P (0:Fin (m+2)).succ) 0).trans H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,omitCoin_cons_succ,pow_zero,mul_one,one_mul,
      bernoulliPolynomial_cons,coinFactor,backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,
      mul_comm,mul_left_comm,mul_assoc] using H'
  have hP : L (coinFactor (1/2)*coinFactor a*coinFactor b)=0 := by
    have H := polynomialGradientPairing_euler q P hp hp1
    rw [hzero,mul_zero] at H
    simpa only [L,P,tripleCoins,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hfair : 0≤L (coinFactor a*coinFactor b) := by
    have hd := midpoint_deriv_nonpos_of_min_fair q P hp hpH ((0:Fin (m+1)).succ).succ rfl hmin
    have H := bernoulliGradientPairing_omit_nonneg q P hp hp1 ((0:Fin (m+1)).succ).succ hzero hd
    have he := polynomialGradientPairing_shift_eq q P (omitCoin P ((0:Fin (m+1)).succ).succ) 0
    simp only [pow_zero,mul_one,Nat.cast_zero] at he
    rw [← he] at H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,omitCoin_cons_succ,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hm := linearMap_distinct_fair_moments L a b ha.ne' hb.ne' hab hP hB hA
  have he : L (coinFactor a*coinFactor b)=L 1*((1-2*a)*(1-2*b)) := by
    have H := linearMap_eq_two_eval L (-1) (-1) (L 1) 0 3
      (by intro j hj; simpa using hm j hj) (coinFactor a*coinFactor b)
      (by unfold coinFactor; compute_degree; norm_num)
    simp only [zero_mul,add_zero,eval_mul,coinFactor_eval] at H
    convert H using 1; ring
  have hw : 0≤L 1 := by
    rw [he] at hfair
    exact nonneg_of_mul_nonneg_left hfair (mul_pos (by linarith) (by linarith))
  exact polynomialGradientPairing_not_nonnegative_twoRoots q P h hq0 hq1 hp hpH hh hhHalf
    (-1) (-1) (L 1) 0 (by norm_num) (by norm_num) hw le_rfl
    (by intro j hj; simpa using hm j hj)

end RenyiMonotonicity
