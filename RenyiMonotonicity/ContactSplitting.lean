module

public import RenyiMonotonicity.ContactAlgebra
public import RenyiMonotonicity.ContactLocalMin

/-! The actual opposite-pair perturbation and its contact curvature sign. -/

@[expose] public section
noncomputable section
open Filter Topology
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

def massSecondDifference (h : ℤ → ℝ) (k : ℤ) : ℝ := h (k-2)-2*h (k-1)+h k

def pairCoins {m : ℕ} (a b : ℝ) (h : Fin m → ℝ) : Fin (m+2) → ℝ := Fin.cons a (Fin.cons b h)

lemma bernoulliMass_opposite_pair {m : ℕ} (a t : ℝ) (h : Fin m → ℝ) (k : ℤ) :
    bernoulliMass (pairCoins (a+t) (a-t) h) k = bernoulliMass (pairCoins a a h) k-
      t^2*massSecondDifference (bernoulliMass h) k := by
  simp only [pairCoins, bernoulliMass_cons, massSecondDifference]
  rw [show k-1-1=k-2 by omega]
  ring

lemma massSecondDifference_outer_left {m : ℕ} (h : Fin m → ℝ) :
    massSecondDifference (bernoulliMass h) (-1)=0 := by
  norm_num [massSecondDifference, bernoulliMass_neg]

lemma massSecondDifference_outer_right {m : ℕ} (h : Fin m → ℝ) :
    massSecondDifference (bernoulliMass h) ((m:ℤ)+3)=0 := by
  simp only [massSecondDifference]
  rw [show (m:ℤ)+3-2=(m:ℤ)+1 by omega, show (m:ℤ)+3-1=((m+2:ℕ):ℤ) by omega,
    show (m:ℤ)+3=((m+3:ℕ):ℤ) by omega, bernoulliMass_outer_right,
    bernoulliMass_natCast, bernoulliMass_natCast, coeff_bernoulliPolynomial_eq_zero h _ (by omega),
    coeff_bernoulliPolynomial_eq_zero h _ (by omega)]
  ring

lemma polynomialGradientPairing_secondDifference {n m : ℕ} (q : ℝ) (p : Fin n → ℝ) (h : Fin m → ℝ) :
    polynomialGradientPairing q p (bernoulliPolynomial h*(X-1)^2) =
      massGradientPairing q n (bernoulliMass p) (massSecondDifference (bernoulliMass h)) := by
  rw [show bernoulliPolynomial h*(X-1)^2 = bernoulliPolynomial h*X^2-
      C 2*(bernoulliPolynomial h*X^1)+bernoulliPolynomial h*X^0 by simp only [map_ofNat]; ring,
    polynomialGradientPairing_add, polynomialGradientPairing_sub, polynomialGradientPairing_C_mul]
  rw [polynomialGradientPairing_shift_eq,polynomialGradientPairing_shift_eq,polynomialGradientPairing_shift_eq]
  simp only [bernoulliGradientPairing, massGradientPairing, massSecondDifference, Nat.cast_ofNat, Nat.cast_zero, sub_zero]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  change (bernoulliMass h ((k.val:ℤ)-2)*_ - 2*(bernoulliMass h ((k.val:ℤ)-1)*_)) + bernoulliMass h k.val*_ = _
  ring

/-- Oppositely perturbing two equal interior parameters forces the actual splitting curvature nonpositive. -/
theorem polynomialGradientPairing_splitting_nonpos {m : ℕ} (q a : ℝ) (h : Fin m → ℝ)
    (ha : 0 < a) (haHalf : a < 1/2) (hh : ∀ i, 0 < h i) (hhHalf : ∀ i, h i ≤ 1/2)
    (hmin : ∀ r : Fin (m+2) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (pairCoins a a h) ≤ midpointFunctional q r) :
    polynomialGradientPairing q (pairCoins a a h) (bernoulliPolynomial h*(X-1)^2) ≤ 0 := by
  let p := pairCoins a a h
  let v := massSecondDifference (bernoulliMass h)
  let F := fun s : ℝ => finiteMassFunctional q (m+2) (fun k => bernoulliMass p k-s*v k)
  have hp : ∀ i, 0 < p i := by intro i; refine Fin.cases ha (fun i => ?_) i; exact Fin.cases ha hh i
  have hp1 : ∀ i, p i < 1 := by
    intro i
    refine Fin.cases (by change a<1; linarith) (fun i => ?_) i
    refine Fin.cases (by change a<1; linarith) (fun i => ?_) i
    exact lt_of_le_of_lt (hhHalf i) (by norm_num)
  have hd : HasDerivAt F (-massGradientPairing q (m+2) (bernoulliMass p) v) 0 := by
    have H := hasDerivAt_finiteMassFunctional_path q (m+2)
      (fun s k => bernoulliMass p k-s*v k) (fun k => -v k) 0
      (fun k => by
        convert (hasDerivAt_const (0:ℝ) (bernoulliMass p k)).sub ((hasDerivAt_id (0:ℝ)).mul_const (v k)) using 1
        · funext s; rfl
        · simp)
      (by intro k; simpa only [zero_mul,sub_zero,edgeSum] using edgeSum_pos p hp hp1 k)
      (by simp [v, massSecondDifference_outer_left])
      (by rw [show (((m+2:ℕ):ℤ)+1)=(m:ℤ)+3 by omega]; simp only [v,massSecondDifference_outer_right,neg_zero])
    simpa [F,massGradientPairing,Finset.sum_neg_distrib,neg_mul] using H
  have hright : ∀ᶠ s in 𝓝[>] (0:ℝ), F 0 ≤ F s := by
    let δ := min a (1/2-a)
    have hδ : 0 < δ := lt_min ha (by linarith)
    have hs : ∀ᶠ s in 𝓝[>] (0:ℝ), s < δ^2 :=
      (eventually_lt_nhds (show (0:ℝ)<δ^2 by positivity)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs,self_mem_nhdsWithin] with s hs hspos
    have ht0 := Real.sqrt_nonneg s
    have htsq := Real.sq_sqrt (le_of_lt hspos)
    have ht : Real.sqrt s < δ := by nlinarith
    have htA : Real.sqrt s < a := lt_of_lt_of_le ht (min_le_left _ _)
    have htB : Real.sqrt s < 1/2-a := lt_of_lt_of_le ht (min_le_right _ _)
    have hr : ∀ i, pairCoins (a+Real.sqrt s) (a-Real.sqrt s) h i ∈ Set.Icc (0:ℝ) (1/2) := by
      intro i
      refine Fin.cases (by change 0≤a+Real.sqrt s ∧ a+Real.sqrt s≤1/2; constructor <;> linarith) (fun i => ?_) i
      refine Fin.cases (by change 0≤a-Real.sqrt s ∧ a-Real.sqrt s≤1/2; constructor <;> linarith) (fun i => ?_) i
      exact ⟨(hh i).le,hhHalf i⟩
    have H := hmin _ hr
    have he : (fun k => bernoulliMass p k-s*v k) =
        bernoulliMass (pairCoins (a+Real.sqrt s) (a-Real.sqrt s) h) := by
      funext k
      rw [bernoulliMass_opposite_pair,htsq]
    simpa only [F,zero_mul,sub_zero,he,finiteMassFunctional_bernoulliMass] using H
  have H := hasDerivAt_nonneg_of_right_min hd hright
  rw [polynomialGradientPairing_secondDifference]
  exact neg_nonneg.mp H

end RenyiMonotonicity
