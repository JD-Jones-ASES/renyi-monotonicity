module
public import RenyiMonotonicity.CMBTail

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RenyiMonotonicity

def oneBiasedSeriesCoefficient (N : ℕ) (q : ℝ) (ell : ℕ) : ℝ :=
  Ring.choose (q-1) (2*ell) * (cmbMoment N q ell-
    (1+(N-1:ℝ)*q/(2*(ell:ℝ)+1))*cmbMoment N q (ell+1))

theorem oneBiasedSeriesCoefficient_eq (N : ℕ) (hN : 0 < N) (q : ℝ) (ell : ℕ) :
    oneBiasedSeriesCoefficient N q ell =
      (Ring.choose (q-1) (2*ell)*cmbMoment N q (ell+1)/(2*(ell:ℝ)+1))*
        (cmbMomentRatio N q ell-(N-1:ℝ)*q) := by
  have hm := (cmbMoment_pos N (by omega) q (ell+1)).ne'
  have hl : 2*(ell:ℝ)+1 ≠ 0 := by positivity
  unfold oneBiasedSeriesCoefficient cmbMomentRatio
  field_simp
  ring

theorem oneBiasedSeriesCoefficient_factor_pos (N : ℕ) (hN : 0 < N) (q : ℝ)
    (hq : q < 1) (ell : ℕ) :
    0 < Ring.choose (q-1) (2*ell)*cmbMoment N q (ell+1)/(2*(ell:ℝ)+1) := by
  exact div_pos (mul_pos (real_choose_negative_even_pos (q-1) (by linarith) ell)
    (cmbMoment_pos N (by omega) q (ell+1))) (by positivity)

/-- Moment-ratio monotonicity and the actual finite moment tail produce one
coefficient sign change with a strictly negative tail. -/
theorem oneBiased_coefficient_sign_change_of_ratio_antitone (N : ℕ) (hN : 2 ≤ N)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hm : Antitone (cmbMomentRatio N q)) :
    ∃ L : ℕ, (∀ k < L, 0 ≤ oneBiasedSeriesCoefficient N q k) ∧
      (∀ k, L ≤ k → oneBiasedSeriesCoefficient N q k < 0) := by
  have hn : 0 < N := by omega
  have hthreshold : 0 < (N-1:ℝ)*q := mul_pos (by
    have h : (2:ℝ) ≤ N := by exact_mod_cast hN
    linarith) hq0
  have hex : ∃ k, cmbMomentRatio N q k < (N-1:ℝ)*q :=
    ((tendsto_cmbMomentRatio N hn q).eventually (eventually_lt_nhds hthreshold)).exists
  let L := Nat.find hex
  refine ⟨L,?_,?_⟩
  · intro k hk
    have hh : (N-1:ℝ)*q ≤ cmbMomentRatio N q k := le_of_not_gt (Nat.find_min hex hk)
    rw [oneBiasedSeriesCoefficient_eq N hn q k]
    exact mul_nonneg (oneBiasedSeriesCoefficient_factor_pos N hn q hq1 k).le (sub_nonneg.mpr hh)
  · intro k hk
    have hh : cmbMomentRatio N q k < (N-1:ℝ)*q := (hm hk).trans_lt (Nat.find_spec hex)
    rw [oneBiasedSeriesCoefficient_eq N hn q k]
    exact mul_neg_of_pos_of_neg (oneBiasedSeriesCoefficient_factor_pos N hn q hq1 k) (sub_neg.mpr hh)

end RenyiMonotonicity
