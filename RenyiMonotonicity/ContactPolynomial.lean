module

public import RenyiMonotonicity.ContactCalculus

/-! The actual polynomial gradient functional and its finite shift obstruction. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- The linear functional defined by the actual mass-gradient coefficients. -/
def polynomialGradientPairing {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (Q : ℝ[X]) : ℝ :=
  ∑ k : Fin (n+1), Q.coeff k.val * bernoulliMassGradient q p k.val

lemma polynomialGradientPairing_add {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (Q R : ℝ[X]) :
    polynomialGradientPairing q p (Q+R) = polynomialGradientPairing q p Q+polynomialGradientPairing q p R := by
  simp [polynomialGradientPairing, add_mul, Finset.sum_add_distrib]

lemma polynomialGradientPairing_sub {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (Q R : ℝ[X]) :
    polynomialGradientPairing q p (Q-R) = polynomialGradientPairing q p Q-polynomialGradientPairing q p R := by
  simp [polynomialGradientPairing, sub_mul, Finset.sum_sub_distrib]

lemma polynomialGradientPairing_C_mul {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (a : ℝ) (Q : ℝ[X]) :
    polynomialGradientPairing q p (C a*Q) = a*polynomialGradientPairing q p Q := by
  simp [polynomialGradientPairing, mul_assoc, Finset.mul_sum]

lemma polynomialGradientPairing_sum {n : ℕ} {ι : Type*} (q : ℝ) (p : Fin n → ℝ)
    (s : Finset ι) (Q : ι → ℝ[X]) :
    polynomialGradientPairing q p (∑ i ∈ s, Q i) = ∑ i ∈ s, polynomialGradientPairing q p (Q i) := by
  simp only [polynomialGradientPairing, finsetSum_coeff, Finset.sum_mul]
  exact Finset.sum_comm

/-- The polynomial gradient pairing packaged as an actual real linear map. -/
def polynomialGradientLinearMap {n : ℕ} (q : ℝ) (p : Fin n → ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun := polynomialGradientPairing q p
  map_add' := polynomialGradientPairing_add q p
  map_smul' a Q := by
    simp [polynomialGradientPairing, smul_eq_C_mul, mul_assoc, Finset.mul_sum]

/-- Multiply a polynomial perturbation by a fixed actual background before pairing. -/
def backgroundGradientLinearMap {n m : ℕ} (q : ℝ) (p : Fin n → ℝ) (h : Fin m → ℝ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun V := polynomialGradientPairing q p (bernoulliPolynomial h*V)
  map_add' V W := by rw [mul_add, polynomialGradientPairing_add]
  map_smul' a V := by
    simp only [RingHom.id_apply, smul_eq_C_mul]
    rw [show bernoulliPolynomial h*(C a*V)=C a*(bernoulliPolynomial h*V) by ring,
      polynomialGradientPairing_C_mul]
    rfl

lemma polynomialGradientPairing_monomial {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (d : ℕ) (c : ℝ)
    (hd : d ≤ n) : polynomialGradientPairing q p (monomial d c) = c*bernoulliMassGradient q p d := by
  classical
  unfold polynomialGradientPairing
  rw [Finset.sum_eq_single (⟨d,by omega⟩ : Fin (n+1))]
  · simp
  · intro k _ hk
    have he : d ≠ k.val := by intro h; apply hk; apply Fin.ext; exact h.symm
    simp [coeff_monomial, he]
  · simp

lemma bernoulliPolynomial_eq_sum_monomials {m : ℕ} (h : Fin m → ℝ) :
    bernoulliPolynomial h = ∑ k : Fin (m+1), monomial k.val (bernoulliMass h k.val) := by
  have hd : (bernoulliPolynomial h).natDegree ≤ m :=
    natDegree_le_iff_coeff_eq_zero.mpr (coeff_bernoulliPolynomial_eq_zero h)
  simp only [bernoulliMass_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun k => monomial k ((bernoulliPolynomial h).coeff k))]
  exact (bernoulliPolynomial h).as_sum_range' (m+1) (by omega)

/-- Pairing a shifted actual law is exactly the concrete coefficient convolution. -/
theorem polynomialGradientPairing_shift {n m : ℕ} (q : ℝ) (p : Fin n → ℝ) (h : Fin m → ℝ)
    (j : ℕ) (hj : m+j ≤ n) :
    polynomialGradientPairing q p (bernoulliPolynomial h*X^j) =
      ∑ k : Fin (m+1), bernoulliMass h k.val*bernoulliMassGradient q p (j+k.val) := by
  rw [bernoulliPolynomial_eq_sum_monomials, Finset.sum_mul, polynomialGradientPairing_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [monomial_mul_X_pow, polynomialGradientPairing_monomial q p _ _ (by omega)]
  congr 2
  omega

lemma coeff_bernoulliPolynomial_shift {m : ℕ} (h : Fin m → ℝ) (j k : ℕ) :
    (bernoulliPolynomial h*X^j).coeff k = bernoulliMass h ((k:ℤ)-j) := by
  rw [coeff_mul_X_pow']
  split_ifs with hj
  · rw [← Nat.cast_sub hj, bernoulliMass_natCast]
  · exact (bernoulliMass_neg h _ (by omega)).symm

/-- The polynomial and integer-shift presentations define the same pairing. -/
theorem polynomialGradientPairing_shift_eq {n m : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (h : Fin m → ℝ) (j : ℕ) :
    polynomialGradientPairing q p (bernoulliPolynomial h*X^j) = bernoulliGradientPairing q p h j := by
  simp only [polynomialGradientPairing, bernoulliGradientPairing, massGradientPairing,
    bernoulliMassGradient, coeff_bernoulliPolynomial_shift]

/-- Euler's identity in the polynomial-functional presentation. -/
theorem polynomialGradientPairing_euler {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    polynomialGradientPairing q p (bernoulliPolynomial p) = q*midpointFunctional q p := by
  simpa [polynomialGradientPairing, bernoulliMass_natCast] using bernoulliMassGradient_euler q p hp hp1

/-- Four successive shifts of a positive background cannot all annihilate the actual half-cube gradient. -/
theorem polynomialGradientPairing_four_shifts_nonzero {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (h : Fin m → ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1/2)
    (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i < 1) :
    ∃ j : Fin 4, polynomialGradientPairing q p (bernoulliPolynomial h*X^j.val) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : ∀ j : Fin (3+1), ∑ k : Fin (m+1), bernoulliMass h k.val *
      bernoulliMassGradient q p ((j.val+k.val:ℕ):ℤ) = 0 := by
    intro j
    have H := hn j
    rw [polynomialGradientPairing_shift q p h j.val (by omega)] at H
    exact H
  have hne : ¬∀ j < m+3+1, bernoulliMassGradient q p (j:ℤ) = 0 := by
    intro hall
    obtain ⟨k,hk⟩ := bernoulliMassGradient_nonzero q p hq0 hq1 hp hpHalf
    exact hk (hall k.val k.isLt)
  have H := bernoulliShift_kernel_signVariations h (fun j => bernoulliMassGradient q p j) 3 hh hh1 hne hz
  have H' := bernoulliMassGradient_signVariations_le_three q p hq0 hq1 hp
    (fun i => lt_of_le_of_lt (hpHalf i) (by norm_num))
  change 4 ≤ (List.ofFn (fun k : Fin (m+3+1) => bernoulliMassGradient q p k.val)).signVariations at H
  omega

end RenyiMonotonicity
