module
public import RenyiMonotonicity.Definitions

/-! Explicit finite-law differentiation on positive-support neighbourhoods. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

def affineMass {m : ℕ} (a b : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun k => (1 - t) * a k + t * b k

def tsallisSlope {m : ℕ} (q : ℝ) (a b : Fin m → ℝ) (t : ℝ) : ℝ :=
  q / (1 - q) * ∑ k, (b k - a k) * (affineMass a b t k) ^ (q - 1)

theorem hasDerivAt_affineMass {m : ℕ} (a b : Fin m → ℝ) (t : ℝ) (k : Fin m) :
    HasDerivAt (fun u => affineMass a b u k) (b k - a k) t := by
  convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const (a k)).add
    ((hasDerivAt_id t).mul_const (b k)) using 1
  · ext u; simp [affineMass]
  · simp; ring

theorem hasDerivAt_powerSum_affine {m : ℕ} (q : ℝ) (a b : Fin m → ℝ) (t : ℝ)
    (hpos : ∀ k, 0 < affineMass a b t k) :
    HasDerivAt (fun u => powerSum q (affineMass a b u))
      (q * ∑ k, (b k - a k) * (affineMass a b t k) ^ (q - 1)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_affineMass a b t k).rpow_const (p := q) (Or.inl (ne_of_gt (hpos k))))
  convert h using 1
  · ext u; simp [powerSum]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem hasDerivAt_tsallis_affine {m : ℕ} (q : ℝ) (a b : Fin m → ℝ) (t : ℝ)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hpos : ∀ k, 0 < affineMass a b t k) :
    HasDerivAt (fun u => tsallis q (affineMass a b u)) (tsallisSlope q a b t) t := by
  simpa [tsallis, hq0, hq1, tsallisSlope, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using ((hasDerivAt_powerSum_affine q a b t hpos).sub_const 1).div_const (1-q)

theorem hasDerivAt_tsallisSlope {m : ℕ} (q : ℝ) (a b : Fin m → ℝ) (t : ℝ)
    (hq1 : q ≠ 1) (hpos : ∀ k, 0 < affineMass a b t k) :
    HasDerivAt (tsallisSlope q a b)
      (-q * ∑ k, (b k - a k)^2 * (affineMass a b t k) ^ (q - 2)) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_affineMass a b t k).rpow_const (p := q-1)
      (Or.inl (ne_of_gt (hpos k)))).const_mul (b k - a k))).const_mul (q / (1-q))
  convert h using 1
  · ext u; simp [tsallisSlope]
  · simp only [show q - 1 - 1 = q - 2 by ring, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hden : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
    field_simp
    ring

theorem tsallis_second_derivative_nonpos {m : ℕ} (q : ℝ) (a b : Fin m → ℝ)
    (t : ℝ) (hq : 0 ≤ q) (hpos : ∀ k, 0 < affineMass a b t k) :
    -q * (∑ k, (b k - a k)^2 * (affineMass a b t k) ^ (q - 2)) ≤ 0 := by
  apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq)
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hpos k).le _))

theorem hasDerivAt_shannon_affine {m : ℕ} (a b : Fin m → ℝ) (t : ℝ)
    (hpos : ∀ k, 0 < affineMass a b t k) :
    HasDerivAt (fun u => shannon (affineMass a b u))
      (∑ k, (-Real.log (affineMass a b t k)-1) * (b k-a k)) t := by
  simpa only [shannon, Function.comp_def] using HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (Real.hasDerivAt_negMulLog (ne_of_gt (hpos k))).comp t (hasDerivAt_affineMass a b t k))

theorem continuousAt_tsallis_affine {m : ℕ} (q : ℝ) (a b : Fin m → ℝ) (t : ℝ)
    (hq : 0 < q) : ContinuousAt (fun u => tsallis q (affineMass a b u)) t := by
  by_cases hq1 : q = 1
  · simp only [tsallis, hq1, one_ne_zero, ↓reduceIte, shannon]
    apply tendsto_finsetSum
    intro k _
    exact Real.continuous_negMulLog.continuousAt.comp (hasDerivAt_affineMass a b t k).continuousAt
  · simp only [tsallis, ne_of_gt hq, hq1, ↓reduceIte, powerSum]
    apply ContinuousAt.div_const
    apply ContinuousAt.sub _ continuousAt_const
    apply tendsto_finsetSum
    intro k _
    exact ((hasDerivAt_affineMass a b t k).continuousAt.rpow_const (Or.inr hq.le))

end RenyiMonotonicity
