module
public import RenyiMonotonicity.OneBiasedMoments

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RenyiMonotonicity

def oneBiasedSeriesScale (m : ℕ) (q : ℝ) : ℝ :=
  (2:ℝ)^q*((1/2:ℝ)^(m+2))^q

theorem oneBiasedSeriesScale_pos (m : ℕ) (q : ℝ) : 0 < oneBiasedSeriesScale m q := by
  unfold oneBiasedSeriesScale
  positivity

lemma positive_mass_edge_scale (q w z u : ℝ) (hw : 0 < w) (hu : 0 < u) :
    (w*z)*(w*u)^(q-1)=w^q*z*u^(q-1) := by
  rw [Real.mul_rpow hw.le hu.le,Real.rpow_sub hw,Real.rpow_one]
  field_simp

/-- Exact finite-transform expression for the actual one-biased midpoint. -/
theorem midpointFunctional_oneBiased_transform (m : ℕ) (q δ : ℝ)
    (hδ : δ ∈ Ioo (0:ℝ) 1) :
    midpointFunctional q (oneBiasedParameters m ((1-δ)/2)) =
      oneBiasedSeriesScale m q *
        (-escortBinomialTransform (m+2) q δ 1 + δ/(m+1:ℝ)*
          (escortBinomialTransform (m+2) q δ 0-(m+2:ℝ)*escortBinomialTransform (m+2) q δ 2)) := by
  have hdelta : 1-2*((1-δ)/2)=δ := by ring
  have he (k : Fin (m+3)) :
      edgeDifference (oneBiasedParameters m ((1-δ)/2)) k *
        edgeSum (oneBiasedParameters m ((1-δ)/2)) k ^ (q-1) =
      oneBiasedSeriesScale m q * (Nat.choose (m+2) k.val:ℝ)^q *
        (-escortGrid (m+2) k + δ*(1-(m+2:ℝ)*(escortGrid (m+2) k)^2)/(m+1:ℝ)) *
          (1+δ*escortGrid (m+2) k)^(q-1) := by
    have hB : 0 < fairBinomialMass (m+2) (k.val : ℤ) := by
      rw [fairBinomialMass_nat]
      exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos (show k.val ≤ m+2 by omega))
    have hU : 0 < 1+δ*escortGrid (m+2) k := by
      have hx := (abs_le.mp (escortGrid_abs_le (m+2) (by omega) k)).1
      nlinarith [hδ.2,mul_nonneg hδ.1.le (by linarith : 0 ≤ escortGrid (m+2) k+1)]
    rw [oneBiased_edgeDifference,oneBiased_edgeSum,hdelta]
    have hg : binomialGridPoint (m+2) (k.val : ℤ)=escortGrid (m+2) k := by
      simp only [binomialGridPoint,escortGrid,Int.cast_natCast]
    rw [hg,positive_mass_edge_scale q _ _ _ (by positivity) hU]
    rw [fairBinomialMass_nat,Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
    unfold oneBiasedSeriesScale
    ring
  simp only [midpointFunctional,he]
  simp only [escortBinomialTransform,pow_zero,pow_one,mul_one]
  simp only [mul_add,mul_sub,mul_neg,Finset.mul_sum,
    ←Finset.sum_add_distrib,←Finset.sum_sub_distrib,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end RenyiMonotonicity
