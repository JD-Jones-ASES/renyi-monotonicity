module

public import RenyiMonotonicity.CMBDensity

/-! Actual tilted CMB and beta-binomial laws: matched mean implies second-moment order. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

/-- A common nonnegative tilt preserves the negative interval of a normalized
log density with interval sublevels. Zero tilted weights are retained harmlessly. -/
theorem tilted_intervalNegativeBlock_of_log_valley {ι : Type*}
    (y w v t : ι→ℝ) (A B : ℝ) (hw : ∀i, 0<w i) (hv : ∀i, 0<v i)
    (ht : ∀i, 0≤t i) (hA : 0<A) (hB : 0<B)
    (hvalley : ∀i j k, y i≤y j → y j≤y k →
      Real.log (w j)-Real.log (v j) ≤
        max (Real.log (w i)-Real.log (v i)) (Real.log (w k)-Real.log (v k))) :
    IntervalNegativeBlock y (fun i => w i*t i/A-v i*t i/B) := by
  have he (i : ι) : w i*t i/A-v i*t i/B=t i*(w i/A-v i/B) := by ring
  have hneg (i : ι) (hi : w i*t i/A-v i*t i/B<0) :
      Real.log (w i)-Real.log (v i)<Real.log A-Real.log B := by
    rw [he] at hi
    have h : w i/A-v i/B<0 := by
      by_contra hn
      exact (not_lt_of_ge (mul_nonneg (ht i) (le_of_not_gt hn))) hi
    have H := (div_lt_div_iff₀ hA hB).mp (sub_neg.mp h)
    have H := (Real.log_lt_log_iff (mul_pos (hw i) hB) (mul_pos (hv i) hA)).mpr H
    rw [Real.log_mul (hw i).ne' hB.ne',Real.log_mul (hv i).ne' hA.ne'] at H
    linarith
  intro i j k hij hjk hi hk
  have H := (hvalley i j k hij hjk).trans_lt (max_lt (hneg i hi) (hneg k hk))
  have H₁ : Real.log (w j*B)≤Real.log (v j*A) := by
    rw [Real.log_mul (hw j).ne' hB.ne',Real.log_mul (hv j).ne' hA.ne']
    linarith
  have H₂ := (Real.log_le_log_iff (mul_pos (hw j) hB) (mul_pos (hv j) hA)).mp H₁
  have H₃ := (div_le_div_iff₀ hA hB).mpr H₂
  change w j*t j/A-v j*t j/B≤0
  rw [he]
  exact mul_nonpos_of_nonneg_of_nonpos (ht j) (sub_nonpos.mpr H₃)

/-- The literal CMB/BB normalized tilted difference has one negative interval. -/
theorem cmb_betaBinomial_intervalNegativeBlock (N : ℕ) (hN : 0<N) (q a : ℝ)
    (ha : 1<a) (ell : ℕ) :
    IntervalNegativeBlock (cmbGrid N) (fun k =>
      (N.choose k.val:ℝ)^q*cmbGrid N k^ell/cmbMoment N q ell-
        betaBinomialWeight a N k.val*cmbGrid N k^ell/betaBinomialMoment N a ell) := by
  have hw (k : Fin (N+1)) : 0<(N.choose k.val:ℝ)^q :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.choose_pos (show k.val≤N by omega)) q
  apply tilted_intervalNegativeBlock_of_log_valley (cmbGrid N)
    (fun k => (N.choose k.val:ℝ)^q) (fun k => betaBinomialWeight a N k.val)
    (fun k => cmbGrid N k^ell) (cmbMoment N q ell) (betaBinomialMoment N a ell)
    hw (fun k => betaBinomialWeight_pos a (by linarith) N k.val (by omega))
    (fun k => pow_nonneg (cmbGrid_nonneg N k) ell)
    (cmbMoment_pos N (by omega) q ell) (betaBinomialMoment_pos N (by omega) a (by linarith) ell)
  intro i j k hij hjk
  have hl (k : Fin (N+1)) : Real.log ((N.choose k.val:ℝ)^q)-Real.log (betaBinomialWeight a N k.val)=
      cmbLogDensity N q a k.val := by
    rw [Real.log_rpow (by exact_mod_cast Nat.choose_pos (show k.val≤N by omega)) q]
    rfl
  simp only [hl]
  exact cmbLogDensity_grid_valley N hN q a ha i j k hij hjk

/-- Matching the actual tilted means orders their actual second moments.
The theorem covers every exponent whenever a matching shape greater than one exists. -/
theorem cmb_betaBinomial_matchedMean_secondMoment_le (N : ℕ) (hN : 0<N)
    (q a : ℝ) (ha : 1<a) (ell : ℕ)
    (hmean : betaBinomialMoment N a (ell+1)/betaBinomialMoment N a ell =
      cmbMoment N q (ell+1)/cmbMoment N q ell) :
    betaBinomialMoment N a (ell+2)/betaBinomialMoment N a ell ≤
      cmbMoment N q (ell+2)/cmbMoment N q ell := by
  let P (k : Fin (N+1)) := (N.choose k.val:ℝ)^q*cmbGrid N k^ell/cmbMoment N q ell
  let Q (k : Fin (N+1)) := betaBinomialWeight a N k.val*cmbGrid N k^ell/betaBinomialMoment N a ell
  have hP (m : ℕ) : (∑ k, P k*cmbGrid N k^m)=cmbMoment N q (ell+m)/cmbMoment N q ell := by
    simp only [P,cmbMoment,Finset.sum_div,pow_add]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hQ (m : ℕ) : (∑ k, Q k*cmbGrid N k^m)=betaBinomialMoment N a (ell+m)/betaBinomialMoment N a ell := by
    simp only [Q,betaBinomialMoment,Finset.sum_div,pow_add]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hp0 : ∑ k, P k=1 := by
    have H := hP 0
    simpa only [pow_zero,mul_one,Nat.add_zero,div_self (cmbMoment_pos N (by omega) q ell).ne'] using H
  have hq0 : ∑ k, Q k=1 := by
    have H := hQ 0
    simpa only [pow_zero,mul_one,Nat.add_zero,
      div_self (betaBinomialMoment_pos N (by omega) a (by linarith) ell).ne'] using H
  have hm : ∑ k, P k*cmbGrid N k=∑ k, Q k*cmbGrid N k := by
    simpa only [pow_one] using (hP 1).trans (hmean.symm.trans (hQ 1).symm)
  have H := matchedMean_secondMoment_le (cmbGrid N) P Q (hp0.trans hq0.symm) hm
    (cmb_betaBinomial_intervalNegativeBlock N hN q a ha ell)
  rw [hP 2,hQ 2] at H
  exact H

end RenyiMonotonicity
