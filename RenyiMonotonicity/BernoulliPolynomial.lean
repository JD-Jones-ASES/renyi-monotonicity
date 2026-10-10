module

public import RenyiMonotonicity.Definitions

@[expose] public section

open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- Expanding the product chooses the success set of the binary outcome. -/
theorem bernoulliPolynomial_eq_sum {n : ℕ} (p : Fin n → ℝ) :
    bernoulliPolynomial p =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        Polynomial.C (bernoulliWeight p s) * Polynomial.X ^ s.card := by
  classical
  unfold bernoulliPolynomial
  simp_rw [add_comm (Polynomial.C (1 - p _))]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    bernoulliWeight, map_mul]
  ring

/-- Finite product-space semantics: sum the independent weights of all outcomes
with exactly `k` successful coins. Every success set is one binary outcome. -/
theorem coeff_bernoulliPolynomial {n : ℕ} (p : Fin n → ℝ) (k : ℕ) :
    (bernoulliPolynomial p).coeff k =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun s => s.card = k),
        bernoulliWeight p s := by
  classical
  rw [bernoulliPolynomial_eq_sum, Polynomial.finsetSum_coeff, Finset.sum_filter]
  simp only [Polynomial.coeff_C_mul_X_pow]
  congr 1
  ext s
  simp only [eq_comm]

/-- The coefficient-defined mass is the count distribution of independent coins. -/
theorem bernoulliSum_eq_sum_weights {n : ℕ} (p : Fin n → ℝ) (k : Fin (n + 1)) :
    bernoulliSum p k =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun s => s.card = k.val),
        bernoulliWeight p s := coeff_bernoulliPolynomial p k.val

/-- No coefficient lies above the number of available coins. -/
theorem coeff_bernoulliPolynomial_eq_zero {n : ℕ} (p : Fin n → ℝ)
    (k : ℕ) (hk : n < k) : (bernoulliPolynomial p).coeff k = 0 := by
  classical
  rw [coeff_bernoulliPolynomial]
  apply Finset.sum_eq_zero
  intro s hs
  obtain ⟨hs, hcard⟩ := Finset.mem_filter.mp hs
  have hle : s.card ≤ n := by
    simpa using Finset.card_le_card (Finset.mem_powerset.mp hs)
  omega

/-- The probabilities of all binary outcomes sum to one, algebraically even
without sign assumptions on the parameter vector. -/
theorem sum_bernoulliWeight {n : ℕ} (p : Fin n → ℝ) :
    ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, bernoulliWeight p s = 1 := by
  classical
  have h := Finset.prod_add (fun i : Fin n => p i) (fun i => 1 - p i) Finset.univ
  simpa [bernoulliWeight] using h.symm

/-- Normalization of the concrete finite coefficient law. -/
theorem sum_bernoulliSum {n : ℕ} (p : Fin n → ℝ) : ∑ k, bernoulliSum p k = 1 := by
  classical
  simp_rw [bernoulliSum, bernoulliPolynomial_eq_sum, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_comm]
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ k : Fin (n + 1), if k.val = s.card then bernoulliWeight p s else 0) =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, bernoulliWeight p s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hle : s.card ≤ n := by
        simpa using Finset.card_le_card (Finset.mem_powerset.mp hs)
      let a : Fin (n + 1) := ⟨s.card, by omega⟩
      have heq (k : Fin (n + 1)) : k.val = s.card ↔ k = a := by
        constructor
        · intro h
          apply Fin.ext
          exact h
        · intro h
          simp [h, a]
      simp only [heq]
      simp
    _ = 1 := sum_bernoulliWeight p

@[simp] theorem bernoulliMass_neg {n : ℕ} (p : Fin n → ℝ) (k : ℤ) (hk : k < 0) :
    bernoulliMass p k = 0 := by simp [bernoulliMass, not_le.mpr hk]

@[simp] theorem bernoulliMass_natCast {n : ℕ} (p : Fin n → ℝ) (k : ℕ) :
    bernoulliMass p k = (bernoulliPolynomial p).coeff k := by simp [bernoulliMass]

@[simp] theorem bernoulliMass_outer_left {n : ℕ} (p : Fin n → ℝ) :
    bernoulliMass p (-1) = 0 := by simp [bernoulliMass]

@[simp] theorem bernoulliMass_outer_right {n : ℕ} (p : Fin n → ℝ) :
    bernoulliMass p (n + 1) = 0 := by
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, bernoulliMass_natCast]
  exact coeff_bernoulliPolynomial_eq_zero p (n + 1) (by omega)

@[simp] theorem bernoulliPolynomial_empty (p : Fin 0 → ℝ) :
    bernoulliPolynomial p = 1 := by simp [bernoulliPolynomial]

@[simp] theorem bernoulliSum_empty (p : Fin 0 → ℝ) (k : Fin 1) :
    bernoulliSum p k = 1 := by
  simp [bernoulliSum]

@[simp] theorem bernoulliPolynomial_zero {n : ℕ} :
    bernoulliPolynomial (fun _ : Fin n => (0 : ℝ)) = 1 := by
  simp [bernoulliPolynomial]

@[simp] theorem bernoulliSum_zero {n : ℕ} (k : Fin (n + 1)) :
    bernoulliSum (fun _ : Fin n => (0 : ℝ)) k = if k.val = 0 then 1 else 0 := by
  simp [bernoulliSum, Polynomial.coeff_one]

/-- Adding one independent Bernoulli coin multiplies the generating polynomial. -/
theorem bernoulliPolynomial_cons {n : ℕ} (a : ℝ) (p : Fin n → ℝ) :
    bernoulliPolynomial (Fin.cons a p) =
      (Polynomial.C (1 - a) + Polynomial.C a * Polynomial.X) * bernoulliPolynomial p := by
  simp [bernoulliPolynomial, Fin.prod_univ_succ]

/-- Leftmost convolution coefficient; no natural predecessor is used. -/
theorem coeff_bernoulliPolynomial_cons_zero {n : ℕ} (a : ℝ) (p : Fin n → ℝ) :
    (bernoulliPolynomial (Fin.cons a p)).coeff 0 =
      (1 - a) * (bernoulliPolynomial p).coeff 0 := by
  rw [bernoulliPolynomial_cons, add_mul]
  simp [mul_assoc]

/-- Interior and right-edge convolution coefficients. -/
theorem coeff_bernoulliPolynomial_cons_succ {n : ℕ} (a : ℝ) (p : Fin n → ℝ)
    (k : ℕ) :
    (bernoulliPolynomial (Fin.cons a p)).coeff (k + 1) =
      (1 - a) * (bernoulliPolynomial p).coeff (k + 1) +
        a * (bernoulliPolynomial p).coeff k := by
  rw [bernoulliPolynomial_cons, add_mul]
  simp only [Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

/-- Uniform convolution formula on integer indices, valid outside support too. -/
theorem bernoulliMass_cons {n : ℕ} (a : ℝ) (p : Fin n → ℝ) (k : ℤ) :
    bernoulliMass (Fin.cons a p) k =
      (1 - a) * bernoulliMass p k + a * bernoulliMass p (k - 1) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    cases k with
    | zero => simp [bernoulliMass, coeff_bernoulliPolynomial_cons_zero]
    | succ k =>
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
      simp only [bernoulliMass_natCast]
      exact coeff_bernoulliPolynomial_cons_succ a p k
  · have hkm : k - 1 < 0 := by omega
    simp [bernoulliMass_neg _ _ (lt_of_not_ge hk), bernoulliMass_neg _ _ hkm]

/-- Deleting a zero-probability coin changes no coefficient. -/
@[simp] theorem bernoulliPolynomial_cons_zero {n : ℕ} (p : Fin n → ℝ) :
    bernoulliPolynomial (Fin.cons 0 p) = bernoulliPolynomial p := by
  simp [bernoulliPolynomial_cons]

@[simp] theorem bernoulliMass_cons_zero {n : ℕ} (p : Fin n → ℝ) (k : ℤ) :
    bernoulliMass (Fin.cons 0 p) k = bernoulliMass p k := by
  simp [bernoulliMass_cons]

/-- Reordering the coins leaves their count law unchanged. -/
theorem bernoulliPolynomial_comp_equiv {n : ℕ} (p : Fin n → ℝ) (e : Fin n ≃ Fin n) :
    bernoulliPolynomial (p ∘ e) = bernoulliPolynomial p := by
  unfold bernoulliPolynomial
  exact Equiv.prod_comp e (fun i => Polynomial.C (1 - p i) + Polynomial.C (p i) * Polynomial.X)

theorem bernoulliSum_comp_equiv {n : ℕ} (p : Fin n → ℝ) (e : Fin n ≃ Fin n) :
    bernoulliSum (p ∘ e) = bernoulliSum p := by
  funext k
  simp only [bernoulliSum, bernoulliPolynomial_comp_equiv]

end RenyiMonotonicity
