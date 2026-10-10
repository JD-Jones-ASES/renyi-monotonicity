module
public import RenyiMonotonicity.NormalizedMidpoint

@[expose] public section
noncomputable section
open Set
open scoped Topology

namespace RenyiMonotonicity

def normalizedPair (q a b : ℝ) : ℝ := (a - b) * entropyOrderKernel q (a + b)

/-- The two partial derivatives are uniformly bounded throughout orders zero
through one, provided the adjacent sum is positive and at most one. -/
theorem normalizedPair_partials_bound {q a b : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 < a + b) (hs1 : a + b ≤ 1) :
    |entropyOrderKernel q (a + b) - (a - b) * (a + b) ^ (q - 2)| ≤ 2 / (a + b) ∧
    |-entropyOrderKernel q (a + b) - (a - b) * (a + b) ^ (q - 2)| ≤ 2 / (a + b) := by
  have hd : |a - b| ≤ a + b := abs_le.mpr ⟨by linarith, by linarith⟩
  have hpow : (a + b) * (a + b) ^ (q - 2) = (a + b) ^ (q - 1) := by
    calc
      _ = (a + b) ^ (1 : ℝ) * (a + b) ^ (q - 2) := by rw [Real.rpow_one]
      _ = (a + b) ^ ((1 : ℝ) + (q - 2)) := (Real.rpow_add hs _ _).symm
      _ = _ := by congr 1; ring
  have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (-1 : ℝ) ≤ q - 1 by linarith)
  rw [Real.rpow_neg_one] at hp
  have hdp : |(a - b) * (a + b) ^ (q - 2)| ≤ (a + b)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
    exact (mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hs.le _)).trans (hpow.le.trans hp)
  have hw := entropyOrderKernel_le_inv hq0 hs hs1
  have hw0 := entropyOrderKernel_nonneg hq1 hs hs1
  constructor
  · calc
      _ ≤ |entropyOrderKernel q (a + b)| + |(a - b) * (a + b) ^ (q - 2)| := abs_sub _ _
      _ ≤ ((a + b)⁻¹ - 1) + (a + b)⁻¹ := by
        rw [abs_of_nonneg hw0]
        exact add_le_add hw hdp
      _ ≤ 2 / (a + b) := by simp only [div_eq_mul_inv]; linarith
  · calc
      _ ≤ |-entropyOrderKernel q (a + b)| + |(a - b) * (a + b) ^ (q - 2)| := abs_sub _ _
      _ ≤ ((a + b)⁻¹ - 1) + (a + b)⁻¹ := by
        rw [abs_neg, abs_of_nonneg hw0]
        exact add_le_add hw hdp
      _ ≤ 2 / (a + b) := by simp only [div_eq_mul_inv]; linarith

theorem hasDerivAt_normalizedPair_segment (q a b u v t : ℝ)
    (hs : 0 < (a + t * (u - a)) + (b + t * (v - b))) :
    HasDerivAt (fun t => normalizedPair q (a + t * (u - a)) (b + t * (v - b)))
      ((u - a) * (entropyOrderKernel q ((a + t * (u - a)) + (b + t * (v - b))) -
          ((a + t * (u - a)) - (b + t * (v - b))) *
            ((a + t * (u - a)) + (b + t * (v - b))) ^ (q - 2)) +
       (v - b) * (-entropyOrderKernel q ((a + t * (u - a)) + (b + t * (v - b))) -
          ((a + t * (u - a)) - (b + t * (v - b))) *
            ((a + t * (u - a)) + (b + t * (v - b))) ^ (q - 2))) t := by
  have ha := ((hasDerivAt_id t).mul_const (u - a)).const_add a
  have hb := ((hasDerivAt_id t).mul_const (v - b)).const_add b
  convert (ha.sub hb).mul ((hasDerivAt_entropyOrderKernel (q := q) hs).comp t (ha.add hb)) using 1
  · ext x
    rfl
  · simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, id_eq, one_mul]
    ring

/-- Uniform control of one old adjacent pair along a probability-law segment. -/
theorem normalizedPair_lipschitz {q a b u v c : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hab : c ≤ a + b) (huv : c ≤ u + v) (hab1 : a + b ≤ 1) (huv1 : u + v ≤ 1) :
    |normalizedPair q u v - normalizedPair q a b| ≤
      (2 / c) * (|u - a| + |v - b|) := by
  let A := fun t : ℝ => a + t * (u - a)
  let B := fun t : ℝ => b + t * (v - b)
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ A t := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) ha, mul_nonneg ht.1 hu]
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ B t := by
    dsimp [B]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hb, mul_nonneg ht.1 hv]
  have hS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : c ≤ A t + B t := by
    dsimp [A, B]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab),
      mul_nonneg ht.1 (sub_nonneg.mpr huv)]
  have hS1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : A t + B t ≤ 1 := by
    dsimp [A, B]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab1),
      mul_nonneg ht.1 (sub_nonneg.mpr huv1)]
  let D := fun t => (u - a) * (entropyOrderKernel q (A t + B t) -
    (A t - B t) * (A t + B t) ^ (q - 2)) +
    (v - b) * (-entropyOrderKernel q (A t + B t) -
    (A t - B t) * (A t + B t) ^ (q - 2))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => normalizedPair q (A t) (B t)) (D t) t :=
    hasDerivAt_normalizedPair_segment q a b u v t (hc.trans_le (hS t ht))
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖D t‖ ≤ (2 / c) * (|u - a| + |v - b|) := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    obtain ⟨h₁, h₂⟩ := normalizedPair_partials_bound hq0 hq1 (hA t ht') (hB t ht')
      (hc.trans_le (hS t ht')) (hS1 t ht')
    have hdiv : 2 / (A t + B t) ≤ 2 / c :=
      div_le_div_of_nonneg_left (by norm_num) hc (hS t ht')
    rw [Real.norm_eq_abs]
    calc
      |D t| ≤ |u - a| * |entropyOrderKernel q (A t + B t) - (A t - B t) * (A t + B t) ^ (q - 2)| +
          |v - b| * |-entropyOrderKernel q (A t + B t) - (A t - B t) * (A t + B t) ^ (q - 2)| := by
        simpa only [D, abs_mul] using abs_add_le ((u - a) * (entropyOrderKernel q (A t + B t) -
          (A t - B t) * (A t + B t) ^ (q - 2))) ((v - b) * (-entropyOrderKernel q (A t + B t) -
          (A t - B t) * (A t + B t) ^ (q - 2)))
      _ ≤ |u - a| * (2 / c) + |v - b| * (2 / c) :=
        add_le_add (mul_le_mul_of_nonneg_left (h₁.trans hdiv) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (h₂.trans hdiv) (abs_nonneg _))
      _ = _ := by ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt) hbound
  simpa [A, B, Real.norm_eq_abs] using hh

end RenyiMonotonicity
