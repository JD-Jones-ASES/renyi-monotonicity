module
public import RenyiMonotonicity.OneBiasedBridge
public import RenyiMonotonicity.OneBiasedSigns
public import RenyiMonotonicity.OneBiasedBoundary
public import RenyiMonotonicity.SignedSeries

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RenyiMonotonicity

def oneBiasedNormalizedSeries (m : ℕ) (q δ : ℝ) : ℝ :=
  (m+1:ℝ)*midpointFunctional q (oneBiasedParameters m ((1-δ)/2)) /
    (oneBiasedSeriesScale m q*δ)

/-- Exact open-interval coefficient series for the actual one-biased law. -/
theorem hasSum_oneBiased_series (m : ℕ) (q δ : ℝ) (hδ : δ ∈ Ioo (0:ℝ) 1) :
    HasSum (fun ell => oneBiasedSeriesCoefficient (m+2) q ell*δ^(2*ell))
      (oneBiasedNormalizedSeries m q δ) := by
  have hdabs : |δ| < 1 := by rw [abs_of_pos hδ.1]; exact hδ.2
  have h₀ := hasSum_escortBinomial_even (m+2) (by omega) q δ hdabs 0
  have h₂ := hasSum_escortBinomial_even (m+2) (by omega) q δ hdabs 1
  have h₁ := hasSum_escortBinomial_odd (m+2) (by omega) q δ hdabs
  simp only [Nat.add_zero,Nat.mul_zero,Nat.mul_one] at h₀ h₂
  have hs := ((h₁.neg).add ((h₀.sub (h₂.mul_left (m+2:ℝ))).mul_left (δ/(m+1:ℝ)))).mul_left ((m+1:ℝ)/δ)
  convert hs using 1
  · funext ell
    have hl : 2*(ell:ℝ)+1 ≠ 0 := by positivity
    have hc : Ring.choose (q-1) (2*ell+1) =
        Ring.choose (q-1) (2*ell)*(q-1-2*(ell:ℝ))/(2*(ell:ℝ)+1) := by
      apply (eq_div_iff hl).mpr
      have hh := real_choose_mul_succ (q-1) (2*ell)
      push_cast at hh
      nlinarith
    rw [hc]
    unfold oneBiasedSeriesCoefficient
    simp only [pow_succ,Nat.cast_add,Nat.cast_ofNat]
    have hm : (m+1:ℝ) ≠ 0 := by positivity
    field_simp [hδ.1.ne']
    ring
  · unfold oneBiasedNormalizedSeries
    rw [midpointFunctional_oneBiased_transform m q δ hδ]
    have hS := (oneBiasedSeriesScale_pos m q).ne'
    have hm : (m+1:ℝ) ≠ 0 := by positivity
    field_simp

/-- The normalized interior series has zero left limit at one, derived from
actual support-loss continuity of the finite Bernoulli law. -/
theorem tendsto_oneBiasedNormalizedSeries (m : ℕ) (q : ℝ) (hq : 0 < q) :
    Tendsto (oneBiasedNormalizedSeries m q) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have ht := ((tendsto_midpointFunctional_oneBiased_boundary m q hq).const_mul (m+1:ℝ)).div
    ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (1:ℝ)) (𝓝 1)).mono_left
      nhdsWithin_le_nhds |>.const_mul (oneBiasedSeriesScale m q))
    (by simpa using (oneBiasedSeriesScale_pos m q).ne')
  convert ht using 1
  · rfl
  · simp

/-- Moment-ratio monotonicity implies the strict sign for the actual
one-biased-plus-fair family. -/
theorem midpointFunctional_oneBiased_pos_of_ratio (m : ℕ) (q p : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hpHalf : p < 1/2)
    (hm : Antitone (cmbMomentRatio (m+2) q)) :
    0 < midpointFunctional q (oneBiasedParameters m p) := by
  obtain ⟨L,hleft,hright⟩ := oneBiased_coefficient_sign_change_of_ratio_antitone (m+2) (by omega) q hq0 hq1 hm
  have hpos := signed_series_pos_of_boundary_zero (oneBiasedSeriesCoefficient (m+2) q)
    (oneBiasedNormalizedSeries m q) L hleft (fun k hk => (hright k hk).le)
    (hright (L+1) (by omega)) (fun δ hδ => hasSum_oneBiased_series m q δ hδ)
    (tendsto_oneBiasedNormalizedSeries m q hq0) (1-2*p) ⟨by linarith,by linarith⟩
  unfold oneBiasedNormalizedSeries at hpos
  have hden : 0 < oneBiasedSeriesScale m q*(1-2*p) :=
    mul_pos (oneBiasedSeriesScale_pos m q) (by linarith)
  have hh := (lt_div_iff₀ hden).mp hpos
  have he : (1-(1-2*p))/2=p := by ring
  rw [he,zero_mul] at hh
  exact pos_of_mul_pos_right hh (by positivity)

end RenyiMonotonicity
