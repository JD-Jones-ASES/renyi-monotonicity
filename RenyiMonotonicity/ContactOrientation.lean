module

public import RenyiMonotonicity.ContactPolynomial

/-! The forbidden positive-first four-moment pattern at an actual contact. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

lemma four_alternating_positive_signs {u : Fin 4 → ℝ}
    (h₀ : 0 < u 0) (h₁ : u 1 < 0) (h₂ : 0 < u 2) (h₃ : u 3 < 0) :
    (List.ofFn u).signVariations=3 ∧ (nonzeroSigns (List.ofFn u)).head?=some 1 := by
  have he : List.ofFn u = [u 0,u 1,u 2,u 3] := by simp [List.ofFn_succ]
  rw [he]
  norm_num [List.signVariations, nonzeroSigns, sign_pos h₀, sign_neg h₁,sign_pos h₂,sign_neg h₃,
    List.destutter, List.destutter']

/-- Positive convolution of the actual gradient cannot produce four strictly alternating moments starting positive. -/
theorem polynomialGradientPairing_not_positive_alternating {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (h : Fin m → ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hh : ∀ i, 0 < h i) (hh1 : ∀ i, h i < 1) :
    ¬(0 < polynomialGradientPairing q p (bernoulliPolynomial h*X^0) ∧
      polynomialGradientPairing q p (bernoulliPolynomial h*X^1) < 0 ∧
      0 < polynomialGradientPairing q p (bernoulliPolynomial h*X^2) ∧
      polynomialGradientPairing q p (bernoulliPolynomial h*X^3) < 0) := by
  rintro ⟨h₀,h₁,h₂,h₃⟩
  let u : Fin 4 → ℝ := fun j => ∑ k : Fin (m+1), bernoulliMass h k.val*
    bernoulliMassGradient q p ((j.val+k.val:ℕ):ℤ)
  have he (j : Fin 4) : polynomialGradientPairing q p (bernoulliPolynomial h*X^j.val)=u j :=
    polynomialGradientPairing_shift q p h j.val (by omega)
  have hu : (List.ofFn u).signVariations=3 ∧ (nonzeroSigns (List.ofFn u)).head?=some 1 := by
    apply four_alternating_positive_signs
    · exact (he 0).symm ▸ h₀
    · exact (he 1).symm ▸ h₁
    · exact (he 2).symm ▸ h₂
    · exact (he 3).symm ▸ h₃
  have hvar : (List.ofFn (fun k : Fin (m+3+1) => bernoulliMassGradient q p k.val)).signVariations=3 := by
    have H := bernoulliShift_signVariations_le h (fun k => bernoulliMassGradient q p k) 3 hh hh1
    have H' := bernoulliMassGradient_signVariations_le_three q p hq0 hq1 hp hp1
    change (List.ofFn u).signVariations ≤ _ at H
    rw [hu.1] at H
    exact le_antisymm H' H
  have hne : ¬∀ j : Fin 4, u j=0 := by
    intro hz
    have H : 0 < u 0 := (he 0).symm ▸ h₀
    rw [hz 0] at H
    exact (lt_irrefl (0:ℝ)) H
  have H := bernoulliShift_sign_endpoints_of_variations_eq h (fun k => bernoulliMassGradient q p k) 3 hh hh1 hne
    (by change (List.ofFn u).signVariations=(List.ofFn (fun k : Fin (m+3+1) => bernoulliMassGradient q p k.val)).signVariations; rw [hu.1,hvar])
  have H' := (bernoulliMassGradient_endpoints_of_three q p hq0 hq1 hp hp1 hvar).1
  have Hhead := H.1
  change (nonzeroSigns (List.ofFn u)).head? = _ at Hhead
  rw [hu.2] at Hhead
  have : (some (1:SignType))=some (-1) := Hhead.trans H'
  cases this

end RenyiMonotonicity
