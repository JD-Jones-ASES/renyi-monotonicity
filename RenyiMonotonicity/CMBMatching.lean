module

public import RenyiMonotonicity.BetaCompact
public import RenyiMonotonicity.CMBOrdering

/-! An actual beta-binomial shape matching each finite CMB tilted mean. -/

@[expose] public section
noncomputable section
open scoped Topology

namespace RenyiMonotonicity

/-- Every strict CMB exponent has a beta-binomial shape above one with the same
tilted first moment. The shape may depend on the finite size and tilt order. -/
theorem betaBinomial_matching_shape (N : ℕ) (hN : 3 ≤ N) (q : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (ell : ℕ) :
    ∃ a : ℝ, 1 < a ∧
      betaBinomialMoment N a (ell+1)/betaBinomialMoment N a ell =
        cmbMoment N q (ell+1)/cmbMoment N q ell := by
  let f (u : ℝ) := compactBetaMoment N u (ell+1)/compactBetaMoment N u ell
  have hf : ContinuousOn f (Set.Icc (0:ℝ) 1) := by
    apply (continuous_compactBetaMoment N (ell+1)).continuousOn.div
      (continuous_compactBetaMoment N ell).continuousOn
    intro u hu
    exact (compactBetaMoment_pos N (by omega) u hu.1 ell).ne'
  have h0 : f 0 = cmbMoment N 1 (ell+1)/cmbMoment N 1 ell := by
    dsimp [f]
    rw [compactBetaMoment_at_zero, compactBetaMoment_at_zero]
    have hd : (N.factorial:ℝ) ≠ 0 := by positivity
    have hm : cmbMoment N 1 ell ≠ 0 := (cmbMoment_pos N (by omega) 1 ell).ne'
    field_simp
  have h1 : f 1 = cmbMoment N 0 (ell+1)/cmbMoment N 0 ell := by
    simp only [f, compactBetaMoment_at_one]
  have hbetween : cmbMoment N q (ell+1)/cmbMoment N q ell ∈ Set.Ioo (f 0) (f 1) := by
    rw [h0,h1]
    exact ⟨cmb_tiltedMean_strictAnti N hN ell q 1 hq₁,
      cmb_tiltedMean_strictAnti N hN ell 0 q hq₀⟩
  obtain ⟨u, hu, he⟩ := intermediate_value_Ioo (by norm_num : (0:ℝ) ≤ 1) hf hbetween
  refine ⟨1/u, (lt_div_iff₀ hu.1).mpr (by simpa using hu.2), ?_⟩
  have hscale : u^N ≠ 0 := pow_ne_zero _ hu.1.ne'
  have hm : betaBinomialMoment N (1/u) ell ≠ 0 :=
    (betaBinomialMoment_pos N (by omega) (1/u) (div_pos zero_lt_one hu.1) ell).ne'
  have heq : f u = betaBinomialMoment N (1/u) (ell+1)/betaBinomialMoment N (1/u) ell := by
    dsimp [f]
    rw [compactBetaMoment_eq N u hu.1.ne', compactBetaMoment_eq N u hu.1.ne']
    field_simp
  exact heq.symm.trans he

end RenyiMonotonicity
