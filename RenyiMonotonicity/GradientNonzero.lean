module

public import RenyiMonotonicity.GradientOrientation

/-! Nonvanishing of the actual mass gradient on the positive half cube. -/

@[expose] public section
noncomputable section

namespace RenyiMonotonicity

/-- The first three coefficients satisfy the half-cube elementary-symmetric bound. -/
theorem bernoulliMass_low_coefficients {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpHalf : ∀ i, p i ≤ 1/2) :
    bernoulliMass p 1 ^ 2 ≤ bernoulliMass p 0 * bernoulliMass p 1 +
      2 * bernoulliMass p 0 * bernoulliMass p 2 := by
  induction n with
  | zero => norm_num [bernoulliMass, bernoulliPolynomial, Polynomial.coeff_one]
  | succ n ih =>
    have H := ih (Fin.tail p) (fun i => hp i.succ) (fun i => hpHalf i.succ)
    have h₁ := mul_nonneg (sq_nonneg (1-p 0)) (sub_nonneg.mpr H)
    have h₂ := mul_nonneg (mul_nonneg (hp 0) (by linarith [hpHalf 0] : 0 ≤ 1-2*p 0))
      (sq_nonneg (bernoulliMass (Fin.tail p) 0))
    have he : p = Fin.cons (p 0) (Fin.tail p) := (Fin.cons_self_tail p).symm
    rw [he]
    simp only [bernoulliMass_cons]
    norm_num only [show (0:ℤ)-1=-1 by omega, show (1:ℤ)-1=0 by omega,
      show (2:ℤ)-1=1 by omega, bernoulliMass_outer_left, mul_zero, add_zero]
    nlinarith

/-- A zero left-edge gradient forces the next mass to exceed three times the edge mass. -/
theorem massGradientEntry_zero_left_ratio {q b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hb : 0 < b) (hc : 0 < c) (hzero : massGradientEntry q 0 b c = 0) : 3*b < c := by
  have hbc : b < c := by
    by_contra h
    have H := (massGradientEntry_mode_pos_iff hq0 hq1 hb ⟨le_rfl,hb.le⟩
      ⟨hc.le,le_of_not_gt h⟩).mpr hc
    linarith
  have he := criticalMass_unique hq0 hq1 (le_refl (0:ℝ)) hb hbc (sub_eq_zero.mp hzero)
  have H := criticalMass_curvature hq0 hq1 (le_refl (0:ℝ)) hb
  rw [← he] at H
  have hk : tripleKappa 0 b c < 1 := by
    rw [H.2.2]
    exact (scalarKappa_bounds hq0 hq1 (gradientCoordinate_mem (le_refl (0:ℝ)) hb)).2
  have hden : 0 < b*(0-2*b+c) := mul_pos hb H.1
  have hbound := (div_lt_iff₀ hden).mp hk
  nlinarith

/-- If the leftmost gradient vanishes, the next entry is strictly positive on the positive half cube. -/
theorem bernoulliMassGradient_one_pos_of_zero {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1/2)
    (hzero : bernoulliMassGradient q p 0 = 0) : 0 < bernoulliMassGradient q p 1 := by
  have hp1 : ∀ i, p i < 1 := fun i => lt_of_le_of_lt (hpHalf i) (by norm_num)
  have hb := bernoulliMass_pos p hp hp1 0 (by omega) (by omega)
  have hc := bernoulliMass_pos p hp hp1 1 (by omega) (by omega)
  have h₀ : massGradientEntry q 0 (bernoulliMass p 0) (bernoulliMass p 1) = 0 := by
    simpa [bernoulliMassGradient] using hzero
  have hratio := massGradientEntry_zero_left_ratio hq0 hq1 hb hc h₀
  have hineq := bernoulliMass_low_coefficients p (fun i => (hp i).le) hpHalf
  have hsecond : bernoulliMass p 0 < bernoulliMass p 2 := by
    by_contra h
    have H := mul_pos (by linarith : 0 < bernoulliMass p 1 - 2*bernoulliMass p 0)
      (by linarith : 0 < bernoulliMass p 1 + bernoulliMass p 0)
    have H' := mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity : 0 ≤ 2*bernoulliMass p 0)
    nlinarith
  by_cases hinc : bernoulliMass p 1 < bernoulliMass p 2
  · simpa using bernoulliMassGradient_increasing_step q p hq0 hq1 hp hp1 0 (by omega) (by omega)
      (show bernoulliMass p 0 < bernoulliMass p 1 by linarith) hinc.le (by rw [hzero])
  · change 0 < massGradientEntry q (bernoulliMass p (1-1)) (bernoulliMass p 1) (bernoulliMass p (1+1))
    norm_num only [show (1:ℤ)-1=0 by omega, show (1:ℤ)+1=2 by omega]
    exact (massGradientEntry_mode_pos_iff hq0 hq1 hc ⟨hb.le,by linarith⟩
      ⟨(hb.trans hsecond).le,le_of_not_gt hinc⟩).mpr hsecond

/-- Every positive half-cube law with at least one coin has a nonzero actual mass gradient. -/
theorem bernoulliMassGradient_nonzero {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1/2) :
    ∃ k : Fin (n+2), bernoulliMassGradient q p k.val ≠ 0 := by
  by_cases h : bernoulliMassGradient q p 0 = 0
  · exact ⟨⟨1,by omega⟩,(bernoulliMassGradient_one_pos_of_zero q p hq0 hq1 hp hpHalf h).ne'⟩
  · exact ⟨0,h⟩

end RenyiMonotonicity
