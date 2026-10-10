module

public import RenyiMonotonicity.ContactAlgebra

/-! Explicit root evaluation for the low-degree contact functional. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

def coinRoot (a : ℝ) : ℝ := -(1-a)/a

lemma linearMap_mul_coinFactor (L : ℝ[X] →ₗ[ℝ] ℝ) (V : ℝ[X]) (a : ℝ) :
    L (V*coinFactor a) = L V+a*L (V*(X-1)) := by
  rw [show V*coinFactor a = V+a • (V*(X-1)) by rw [coinFactor_eq]; simp only [smul_eq_C_mul]; ring]
  simp only [map_add,map_smul,smul_eq_mul]

lemma linearMap_factor_moments (L : ℝ[X] →ₗ[ℝ] ℝ) (a : ℝ) (ha : a ≠ 0) (r : ℕ)
    (hzero : ∀ j < r, L (coinFactor a*X^j)=0) :
    ∀ j ≤ r, L (X^j)=L 1*coinRoot a^j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have H := hzero j (by omega)
    rw [show coinFactor a*X^j = (1-a) • X^j+a • X^(j+1) by
      simp only [coinFactor,smul_eq_C_mul,pow_succ]; ring,
      map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at H
    apply mul_left_cancel₀ ha
    calc
      a*L (X^(j+1)) = -(1-a)*L (X^j) := by linarith
      _ = a*(L 1*coinRoot a^(j+1)) := by
        rw [ih (by omega),pow_succ]
        unfold coinRoot
        field_simp

/-- Two distinct stationary omissions of a repeated factor force root-evaluation moments. -/
theorem linearMap_repeated_singleton_moments (L : ℝ[X] →ₗ[ℝ] ℝ) (p a : ℝ)
    (hp : p ≠ 0) (ha : a ≠ 0) (hpa : p ≠ a)
    (hP : L (coinFactor p*coinFactor p*coinFactor a)=0)
    (hA : L (coinFactor p*coinFactor a)=0)
    (hB : L (coinFactor p*coinFactor p)=0) :
    ∀ j ≤ 3, L (X^j)=L 1*coinRoot p^j := by
  rw [linearMap_mul_coinFactor] at hA hB
  have ht : L (coinFactor p*(X-1))=0 := by
    apply (mul_eq_zero.mp (show (p-a)*L (coinFactor p*(X-1))=0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hpa
  have hf : L (coinFactor p)=0 := by simpa [ht] using hA
  rw [linearMap_mul_coinFactor] at hP
  have hsq : L (coinFactor p*(X-1)^2)=0 := by
    have he : L (coinFactor p*coinFactor p*(X-1)) =
        L (coinFactor p*(X-1))+p*L (coinFactor p*(X-1)^2) := by
      rw [show coinFactor p*coinFactor p*(X-1) = (coinFactor p*(X-1))*coinFactor p by ring,
        linearMap_mul_coinFactor]
      rw [show coinFactor p*(X-1)*(X-1)=coinFactor p*(X-1)^2 by ring]
    rw [linearMap_mul_coinFactor,hf,ht,he] at hP
    simpa [ht,ha,hp] using hP
  apply linearMap_factor_moments L p hp 3
  intro j hj
  interval_cases j
  · simpa using hf
  · rw [show coinFactor p*X^1 = coinFactor p+coinFactor p*(X-1) by ring,map_add,hf,ht,add_zero]
  · rw [show coinFactor p*X^2 = coinFactor p+(2:ℝ) • (coinFactor p*(X-1))+coinFactor p*(X-1)^2 by
      simp only [smul_eq_C_mul,map_ofNat]; ring]
    simp only [map_add,map_smul,hf,ht,hsq,smul_zero,add_zero]

/-- The exact curvature-to-evaluation-weight identity for a repeated factor and a singleton. -/
theorem linearMap_repeated_singleton_curvature (L : ℝ[X] →ₗ[ℝ] ℝ) (p a : ℝ)
    (hp : p ≠ 0) (hm : ∀ j ≤ 3, L (X^j)=L 1*coinRoot p^j) :
    p^3*L ((X-1)^2*coinFactor a) = (p-a)*L 1 := by
  have hx := hm 1 (by omega)
  have hxx := hm 2 (by omega)
  have hxxx := hm 3 (by omega)
  rw [show (X-1)^2*coinFactor a = (1-a) • (1:ℝ[X])+(3*a-2) • X+(1-3*a) • X^2+a • X^3 by
    simp only [coinFactor,smul_eq_C_mul,map_sub,map_mul,map_ofNat,map_one]; ring]
  simp only [map_add,map_smul,smul_eq_mul]
  simp only [pow_one] at hx
  rw [hx,hxx,hxxx]
  unfold coinRoot
  field_simp
  ring

end RenyiMonotonicity
