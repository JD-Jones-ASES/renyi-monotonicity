module

public import RenyiMonotonicity.ContactPolynomial

/-! Low-degree polynomial identities used to classify an actual contact. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- One Bernoulli generating factor. -/
def coinFactor (a : ℝ) : ℝ[X] := C (1-a)+C a*X

lemma coinFactor_eq (a : ℝ) : coinFactor a = 1+a • (X-1) := by
  simp [coinFactor, smul_eq_C_mul]
  ring

lemma linearMap_coinFactor_pair (L : ℝ[X] →ₗ[ℝ] ℝ) (a b : ℝ) :
    L (coinFactor a*coinFactor b) = L 1+(a+b)*L (X-1)+a*b*L ((X-1)^2) := by
  rw [show coinFactor a*coinFactor b = 1+(a+b) • (X-1)+(a*b) • ((X-1)^2) by
    simp only [coinFactor_eq, smul_eq_C_mul]; simp only [map_add, map_mul]; ring]
  simp only [map_add, map_smul, smul_eq_mul]

lemma linearMap_coinFactor_triple (L : ℝ[X] →ₗ[ℝ] ℝ) (a b c : ℝ) :
    L (coinFactor a*coinFactor b*coinFactor c) =
      L 1+(a+b+c)*L (X-1)+(a*b+a*c+b*c)*L ((X-1)^2)+(a*b*c)*L ((X-1)^3) := by
  rw [show coinFactor a*coinFactor b*coinFactor c =
      1+(a+b+c) • (X-1)+(a*b+a*c+b*c) • ((X-1)^2)+(a*b*c) • ((X-1)^3) by
    simp only [coinFactor_eq, smul_eq_C_mul]; simp only [map_add, map_mul]; ring]
  simp only [map_add, map_smul, smul_eq_mul]

lemma linearMap_X_powers_zero (L : ℝ[X] →ₗ[ℝ] ℝ)
    (h₀ : L 1=0) (h₁ : L (X-1)=0) (h₂ : L ((X-1)^2)=0) (h₃ : L ((X-1)^3)=0) :
    ∀ j : Fin 4, L (X^j.val)=0 := by
  intro j
  fin_cases j
  · simpa using h₀
  · rw [show (X:ℝ[X])^1 = 1+(X-1) by ring, map_add, h₀,h₁,add_zero]
  · rw [show (X:ℝ[X])^2 = 1+(2:ℝ) • (X-1)+(X-1)^2 by simp only [smul_eq_C_mul, map_ofNat]; ring]
    simp only [map_add,map_smul, h₀,h₁,h₂,smul_zero,add_zero]
  · rw [show (X:ℝ[X])^3 = 1+(3:ℝ) • (X-1)+(3:ℝ) • ((X-1)^2)+(X-1)^3 by
      simp only [smul_eq_C_mul, map_ofNat]; ring]
    simp only [map_add,map_smul, h₀,h₁,h₂,h₃,smul_zero,add_zero]

/-- Three distinct nonzero factors and their omissions force four annihilated moments. -/
theorem linearMap_three_distinct_factors (L : ℝ[X] →ₗ[ℝ] ℝ) (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : L (coinFactor a*coinFactor b*coinFactor c)=0)
    (hA : L (coinFactor b*coinFactor c)=0)
    (hB : L (coinFactor a*coinFactor c)=0)
    (hC : L (coinFactor a*coinFactor b)=0) : ∀ j : Fin 4, L (X^j.val)=0 := by
  rw [linearMap_coinFactor_triple] at hP
  rw [linearMap_coinFactor_pair] at hA hB hC
  have h₁ : L (X-1)+c*L ((X-1)^2)=0 := by
    apply (mul_eq_zero.mp (show (a-b)*(L (X-1)+c*L ((X-1)^2))=0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hab
  have h₂ : L (X-1)+b*L ((X-1)^2)=0 := by
    apply (mul_eq_zero.mp (show (a-c)*(L (X-1)+b*L ((X-1)^2))=0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hac
  have hsq : L ((X-1)^2)=0 := by
    apply (mul_eq_zero.mp (show (b-c)*L ((X-1)^2)=0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hbc
  have hlin : L (X-1)=0 := by simpa [hsq] using h₁
  have hconst : L 1=0 := by simpa [hlin,hsq] using hA
  have hcub : L ((X-1)^3)=0 := by
    simpa [hlin,hsq,hconst,ha,hb,hc] using hP
  exact linearMap_X_powers_zero L hconst hlin hsq hcub

@[simp] lemma omitCoin_cons_zero {n : ℕ} (a : ℝ) (p : Fin n → ℝ) :
    omitCoin (Fin.cons a p) 0 = p := by
  funext i
  simp [omitCoin]

@[simp] lemma omitCoin_cons_succ {n : ℕ} (a : ℝ) (p : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    omitCoin (Fin.cons a p) i.succ = Fin.cons a (omitCoin p i) := by
  exact Fin.cons_comp_succ_succAbove a p i

def tripleCoins {m : ℕ} (a b c : ℝ) (h : Fin m → ℝ) : Fin (m+3) → ℝ :=
  Fin.cons a (Fin.cons b (Fin.cons c h))

/-- At value zero, three distinct stationary parameters are impossible on the positive half cube. -/
theorem no_three_distinct_stationary_cons {m : ℕ} (q a b c : ℝ) (h : Fin m → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hp : ∀ i : Fin (m+3), 0 < (tripleCoins a b c h) i)
    (hpHalf : ∀ i : Fin (m+3), (tripleCoins a b c h) i ≤ 1/2)
    (hzero : midpointFunctional q (tripleCoins a b c h)=0)
    (hstationary : ∀ i : Fin 3, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins a b c h)
        (⟨i.val,by omega⟩ : Fin (m+3)) t)) ((tripleCoins a b c h) (⟨i.val,by omega⟩ : Fin (m+3)))=0) :
    a=b ∨ a=c ∨ b=c := by
  by_contra hd
  push Not at hd
  let p := tripleCoins a b c h
  let L := backgroundGradientLinearMap q p h
  have hp1 : ∀ i, p i < 1 := fun i => lt_of_le_of_lt (hpHalf i) (by norm_num)
  have hz (i : Fin 3) : polynomialGradientPairing q p
      (bernoulliPolynomial (omitCoin p ⟨i.val,by omega⟩))=0 := by
    have H := (bernoulliGradientPairing_omit_of_stationary q p hp hp1
      ⟨i.val,by omega⟩ hzero (hstationary i)).1
    simpa only [pow_zero,mul_one,Nat.cast_zero] using
      (polynomialGradientPairing_shift_eq q p (omitCoin p ⟨i.val,by omega⟩) 0).trans H
  have hA : L (coinFactor b*coinFactor c)=0 := by
    have H := hz 0
    change polynomialGradientPairing q p (bernoulliPolynomial (omitCoin p 0))=0 at H
    simpa only [L, p, tripleCoins, omitCoin_cons_zero, pow_zero, mul_one, bernoulliPolynomial_cons,
      coinFactor, backgroundGradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      mul_comm, mul_left_comm, mul_assoc] using H
  have hB : L (coinFactor a*coinFactor c)=0 := by
    have H := hz 1
    change polynomialGradientPairing q p (bernoulliPolynomial (omitCoin p (0:Fin (m+2)).succ))=0 at H
    simpa only [L, p, tripleCoins, omitCoin_cons_succ, omitCoin_cons_zero, pow_zero, mul_one, bernoulliPolynomial_cons,
      coinFactor, backgroundGradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      mul_comm, mul_left_comm, mul_assoc] using H
  have hC : L (coinFactor a*coinFactor b)=0 := by
    have H := hz 2
    change polynomialGradientPairing q p (bernoulliPolynomial (omitCoin p ((0:Fin (m+1)).succ).succ))=0 at H
    simpa only [L, p, tripleCoins, omitCoin_cons_succ, omitCoin_cons_zero, pow_zero, mul_one, bernoulliPolynomial_cons,
      coinFactor, backgroundGradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      mul_comm, mul_left_comm, mul_assoc] using H
  have hP : L (coinFactor a*coinFactor b*coinFactor c)=0 := by
    have H := polynomialGradientPairing_euler q p hp hp1
    rw [hzero,mul_zero] at H
    simpa only [L, p, tripleCoins, bernoulliPolynomial_cons, coinFactor, backgroundGradientLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, mul_comm, mul_left_comm, mul_assoc] using H
  have hall := linearMap_three_distinct_factors L a b c (hp 0).ne'
    (hp (0:Fin (m+2)).succ).ne' (hp ((0:Fin (m+1)).succ).succ).ne' hd.1 hd.2.1 hd.2.2 hP hA hB hC
  obtain ⟨j,hj⟩ := polynomialGradientPairing_four_shifts_nonzero q p h hq0 hq1 hp hpHalf
    (fun i => hp i.succ.succ.succ) (fun i => hp1 i.succ.succ.succ)
  exact hj (hall j)

end RenyiMonotonicity
