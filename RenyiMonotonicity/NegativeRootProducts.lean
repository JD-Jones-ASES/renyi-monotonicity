module

public import RenyiMonotonicity.ProductCoefficientLimits

/-! Normalizing a complete list of negative roots as positive linear factors. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- A concrete complete list of simple negative zeros determines the positive-factor product. -/
theorem polynomial_eq_positiveFactorProduct {n : ℕ} (P : ℝ[X]) (r : Fin n → ℝ)
    (hP : P.eval 0 ≠ 0) (hd : P.natDegree ≤ n) (hinj : Function.Injective r)
    (hr : ∀ i, r i < 0) (hz : ∀ i, P.eval (r i)=0) :
    P = C (P.eval 0) * linearFactorProduct (fun i => 1/(-r i)) := by
  classical
  have hne : P ≠ 0 := by intro h; simp [h] at hP
  have hroots : P.roots = (Finset.univ.image r).val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hz i
    · simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hd
    · exact hne
  have he : P.roots.card = n := by
    rw [hroots]
    simp only [Finset.card_val, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hs : P.Splits := splits_iff_card_roots.mpr (le_antisymm (card_roots' P) (by omega))
  have hev (x : ℝ) : P.eval x = P.leadingCoeff*∏ i, (x-r i) := by
    rw [hs.eval_eq_prod_roots, hroots]
    congr 1
    change (∏ y ∈ Finset.univ.image r, (x-y)) = _
    exact Finset.prod_image (fun a _ b _ hab => hinj hab)
  apply Polynomial.funext
  intro x
  rw [eval_mul, eval_C, hev 0]
  simp only [linearFactorProduct, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X, zero_sub]
  rw [mul_assoc, ← Finset.prod_mul_distrib, hev x]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hi : r i ≠ 0 := (hr i).ne
  field_simp
  ring

theorem linearFactorProduct_append {n m : ℕ} (u : Fin n → ℝ) (v : Fin m → ℝ) :
    linearFactorProduct (Fin.append u v) = linearFactorProduct u*linearFactorProduct v := by
  simp [linearFactorProduct, Fin.prod_univ_add]

/-- Padding the shorter root product with zero parameters preserves coefficient domination. -/
theorem linearFactorProduct_cross_of_le {n m : ℕ} (hnm : n ≤ m)
    (u : Fin n → ℝ) (v : Fin m → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (huv : ∀ i, u i ≤ v (Fin.castLE hnm i)) (k : ℕ) (hk : k < m) :
    (linearFactorProduct u).coeff (k+1)*(linearFactorProduct v).coeff k ≤
      (linearFactorProduct u).coeff k*(linearFactorProduct v).coeff (k+1) := by
  have he : n+(m-n)=m := Nat.add_sub_of_le hnm
  let u' : Fin (n+(m-n)) → ℝ := Fin.append u (fun _ => 0)
  let v' : Fin (n+(m-n)) → ℝ := fun i => v (Fin.cast he i)
  have hu' (i : Fin (n+(m-n))) : 0 ≤ u' i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [u'] using hu j
    · intro j
      simp [u']
  have huv' (i : Fin (n+(m-n))) : u' i ≤ v' i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      have H := huv j
      have hj : Fin.cast he (Fin.castAdd (m-n) j) = Fin.castLE hnm j := by ext; rfl
      simpa [u',v',hj] using H
    · intro j
      simpa [u',v'] using hv (Fin.cast he (Fin.natAdd n j))
  have hup : linearFactorProduct u'=linearFactorProduct u := by
    change linearFactorProduct (Fin.append u (fun _ : Fin (m-n) => 0)) = _
    rw [linearFactorProduct_append]
    simp [linearFactorProduct]
  have hvp : linearFactorProduct v'=linearFactorProduct v := by
    unfold linearFactorProduct
    exact Equiv.prod_comp (finCongr he) (fun i => 1+C (v i)*X)
  have H := linearFactorProduct_cross_nonneg u' v' hu' huv' k (by omega)
  simpa only [hup,hvp] using H

end RenyiMonotonicity
