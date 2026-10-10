module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Order.Sublattice
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Finite algebra used by the inverse-score association inequality. -/

@[expose] public section

namespace RenyiMonotonicity

/-- The positive ordered-pair kernel in the inverse-score inequality. -/
def pairKernel (α a b : ℝ) : ℝ := (b - a) ^ 2 * (1 - α * a * b)

lemma pairKernel_symm (α a b : ℝ) : pairKernel α a b = pairKernel α b a := by
  unfold pairKernel
  ring

lemma score_factor_pos {α a b : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) : 0 < 1 - α * a * b := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a + 1) (by linarith : 0 ≤ 1 - a)]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ b + 1) (by linarith : 0 ≤ 1 - b)]
  have hab : a * b ≤ 1 := by nlinarith [sq_nonneg (a - b)]
  have := mul_le_mul_of_nonneg_left hab hα
  nlinarith

lemma pairKernel_pos {α a b : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hab : a < b) :
    0 < pairKernel α a b := by
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr hab)) (score_factor_pos hα hα1 ha hb)

lemma pairKernel_nonneg {α a b : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) : 0 ≤ pairKernel α a b :=
  mul_nonneg (sq_nonneg _) (score_factor_pos hα hα1 ha hb).le

/-- Algebraic TP2 on every rectangle contained in the strict upper triangle. -/
theorem pairKernel_tp2 {α a a' b b' : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (ha : -1 ≤ a) (hab : a ≤ a') (ha'b : a' < b) (hbb' : b ≤ b') (hb' : b' ≤ 1) :
    pairKernel α a b' * pairKernel α a' b ≤
      pairKernel α a b * pairKernel α a' b' := by
  let r := Real.sqrt α
  have hr0 : 0 ≤ r := Real.sqrt_nonneg α
  have hr2 : r ^ 2 = α := Real.sq_sqrt hα
  have hr1 : r < 1 := by nlinarith
  have fac (u v : ℝ) (hu : -1 ≤ u) (hv : v ≤ 1) :
      r * (v - u) ≤ 1 - α * u * v := by
    have h1 : 0 ≤ 1 + r * u := by nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ u + 1)]
    have h2 : 0 ≤ 1 - r * v := by nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ 1 - v)]
    have hf := mul_nonneg h1 h2
    have hi : 1 - α * u * v - r * (v - u) = (1 + r * u) * (1 - r * v) := by
      rw [← hr2]
      ring
    linarith
  let x := (b - a) * (b' - a')
  let y := (b' - a) * (b - a')
  let δ := (a' - a) * (b' - b)
  let P := (1 - α * a * b) * (1 - α * a' * b')
  have hx : 0 ≤ x := mul_nonneg (by linarith) (by linarith)
  have hy : 0 ≤ y := mul_nonneg (by linarith) (by linarith)
  have hd : 0 ≤ δ := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbb')
  have hxy : x - y = δ := by dsimp [x, y, δ]; ring
  have hP : α * x ≤ P := by
    have hf := mul_le_mul (fac a b ha (by linarith))
      (fac a' b' (by linarith) hb')
      (mul_nonneg hr0 (by linarith : 0 ≤ b' - a'))
      (score_factor_pos hα hα1 ⟨ha, by linarith⟩ ⟨by linarith, by linarith⟩).le
    dsimp [x, P]
    rw [← hr2] at *
    nlinarith only [hf]
  have hbkt : 0 ≤ (x + y) * P - α * y ^ 2 := by
    have h1 := mul_nonneg (show 0 ≤ x + y by linarith) (show 0 ≤ P - α * x by linarith)
    have h2 := mul_nonneg hα (show 0 ≤ x ^ 2 - y ^ 2 + x * y by
      nlinarith [mul_nonneg (show 0 ≤ x - y by linarith) (show 0 ≤ x + y by linarith), mul_nonneg hx hy])
    nlinarith
  have hid : pairKernel α a b * pairKernel α a' b' -
      pairKernel α a b' * pairKernel α a' b = δ * ((x + y) * P - α * y ^ 2) := by
    dsimp [pairKernel, δ, x, y, P]
    ring
  nlinarith [mul_nonneg hd hbkt]

/-- The exact finite weighted Chebyshev identity; normalization is unnecessary. -/
theorem weighted_chebyshev_identity {n : ℕ} (w f g : Fin n → ℝ) :
    (∑ i, ∑ j, w i * w j * ((f i - f j) * (g i - g j))) =
      2 * ((∑ i, w i) * (∑ i, w i * (f i * g i)) -
        (∑ i, w i * f i) * (∑ i, w i * g i)) := by
  have expand : ∀ i j, w i * w j * ((f i - f j) * (g i - g j)) =
      (w i * (f i * g i)) * w j + w i * (w j * (f j * g j)) -
        (w i * f i) * (w j * g j) - (w i * g i) * (w j * f j) := by
    intros; ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Chebyshev association for any nonnegative finite weights on a chain. -/
theorem weighted_chebyshev {n : ℕ} (w f g : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : Monotone f) (hg : Monotone g) :
    (∑ i, w i * f i) * (∑ i, w i * g i) ≤
      (∑ i, w i) * (∑ i, w i * (f i * g i)) := by
  have H : 0 ≤ ∑ i, ∑ j, w i * w j * ((f i - f j) * (g i - g j)) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (mul_nonneg (hw i) (hw j))
    rcases le_total i j with hij | hji
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hij)) (sub_nonpos.mpr (hg hij))
    · exact mul_nonneg (sub_nonneg.mpr (hf hji)) (sub_nonneg.mpr (hg hji))
  rw [weighted_chebyshev_identity] at H
  linarith

end RenyiMonotonicity
