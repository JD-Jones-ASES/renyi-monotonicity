module

public import RenyiMonotonicity.CMBMomentComparison
public import RenyiMonotonicity.CMBMatching
public import RenyiMonotonicity.CMBTail
public import RenyiMonotonicity.BetaBinomialMomentRatio

/-! Transferring beta-binomial moment-ratio order to the actual CMB moments. -/

@[expose] public section
noncomputable section

namespace RenyiMonotonicity

/-- Matching the first moment and using the proven second-moment comparison
transfers one beta-binomial moment-ratio inequality to CMB. -/
theorem cmbMomentRatio_step_of_betaBinomial_step (N : ℕ) (hN : 0<N)
    (q a : ℝ) (ha : 1<a) (ell : ℕ)
    (hmean : betaBinomialMoment N a (ell+1)/betaBinomialMoment N a ell =
      cmbMoment N q (ell+1)/cmbMoment N q ell)
    (hbb : (2*(ell:ℝ)+3)*(betaBinomialMoment N a (ell+1)/betaBinomialMoment N a (ell+2)-1) ≤
      (2*(ell:ℝ)+1)*(betaBinomialMoment N a ell/betaBinomialMoment N a (ell+1)-1)) :
    cmbMomentRatio N q (ell+1)≤cmbMomentRatio N q ell := by
  have hp (m : ℕ) : 0<cmbMoment N q m := cmbMoment_pos N (by omega) q m
  have hb (m : ℕ) : 0<betaBinomialMoment N a m := betaBinomialMoment_pos N (by omega) a (by linarith) m
  have hsecond := cmb_betaBinomial_matchedMean_secondMoment_le N hN q a ha ell hmean
  have he : cmbMoment N q ell/cmbMoment N q (ell+1)=
      betaBinomialMoment N a ell/betaBinomialMoment N a (ell+1) := by
    have H := (div_eq_div_iff (hb ell).ne' (hp ell).ne').mp hmean
    apply (div_eq_div_iff (hp (ell+1)).ne' (hb (ell+1)).ne').mpr
    nlinarith
  have hn : cmbMoment N q (ell+1)/cmbMoment N q (ell+2)≤
      betaBinomialMoment N a (ell+1)/betaBinomialMoment N a (ell+2) := by
    calc
      _ = (cmbMoment N q (ell+1)/cmbMoment N q ell)/
          (cmbMoment N q (ell+2)/cmbMoment N q ell) := by field_simp [(hp ell).ne', (hp (ell+2)).ne']
      _ = (betaBinomialMoment N a (ell+1)/betaBinomialMoment N a ell)/
          (cmbMoment N q (ell+2)/cmbMoment N q ell) := by rw [hmean]
      _ ≤ (betaBinomialMoment N a (ell+1)/betaBinomialMoment N a ell)/
          (betaBinomialMoment N a (ell+2)/betaBinomialMoment N a ell) :=
        div_le_div_of_nonneg_left (div_pos (hb (ell+1)) (hb ell)).le
          (div_pos (hb (ell+2)) (hb ell)) hsecond
      _ = _ := by field_simp [(hb ell).ne', (hb (ell+2)).ne']
  unfold cmbMomentRatio
  push_cast
  rw [show ell+1+1=ell+2 by omega,he]
  calc
    _ = (2*(ell:ℝ)+3)*(cmbMoment N q (ell+1)/cmbMoment N q (ell+2)-1) := by ring
    _ ≤ (2*(ell:ℝ)+3)*(betaBinomialMoment N a (ell+1)/betaBinomialMoment N a (ell+2)-1) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hn 1) (by positivity)
    _ ≤ _ := hbb

/-- Explicit transfer interface, parameterized by the actual beta-binomial
moment-ratio step; matching and density comparison are fully discharged. -/
theorem cmbMomentRatio_antitone_of_betaBinomial (N : ℕ) (hN : 3≤N) (q : ℝ)
    (hq0 : 0<q) (hq1 : q<1)
    (hbb : ∀ a : ℝ, 1<a → ∀ ell : ℕ,
      (2*(ell:ℝ)+3)*(betaBinomialMoment N a (ell+1)/betaBinomialMoment N a (ell+2)-1) ≤
        (2*(ell:ℝ)+1)*(betaBinomialMoment N a ell/betaBinomialMoment N a (ell+1)-1)) :
    Antitone (cmbMomentRatio N q) := by
  apply antitone_nat_of_succ_le
  intro ell
  obtain ⟨a,ha,hm⟩ := betaBinomial_matching_shape N hN q hq0 hq1 ell
  exact cmbMomentRatio_step_of_betaBinomial_step N (by omega) q a ha ell hm (hbb a ha ell)


/-- The actual CMB moment-ratio sequence is antitone for every strict exponent.
All matching, finite density, beta-binomial root, and limiting arguments are proved. -/
theorem cmbMomentRatio_antitone (N : ℕ) (hN : 3≤N) (q : ℝ)
    (hq0 : 0<q) (hq1 : q<1) : Antitone (cmbMomentRatio N q) := by
  apply cmbMomentRatio_antitone_of_betaBinomial N hN q hq0 hq1
  intro a ha ell
  have H := betaBinomialMoment_ratio_antitone_step N hN a ha ell
  convert H using 1
  push_cast
  ring

end RenyiMonotonicity
