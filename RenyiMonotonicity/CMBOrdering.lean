module

public import RenyiMonotonicity.CMBDefinitions

/-! Strict order monotonicity of the actual CMB tilted mean. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

def binomialFold (N k : ℕ) : ℕ := min k (N-k)

theorem binomialFold_le_half (N k : ℕ) (hk : k ≤ N) : binomialFold N k ≤ N/2 := by
  unfold binomialFold
  omega

theorem choose_binomialFold (N k : ℕ) (hk : k ≤ N) : N.choose (binomialFold N k) = N.choose k := by
  unfold binomialFold
  rcases le_total k (N-k) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.choose_symm hk]

theorem cmbGrid_fold (N : ℕ) (k : Fin (N+1)) :
    cmbGrid N k = (((N:ℝ)-2*(binomialFold N k.val:ℝ))/N)^2 := by
  unfold cmbGrid binomialFold
  rcases le_total k.val (N-k.val) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.cast_sub (show k.val ≤ N by omega)]
    ring

theorem choose_le_choose_of_le_half {N i j : ℕ} (hij : i ≤ j) (hj : j ≤ N/2) :
    N.choose i ≤ N.choose j := by
  induction hij with
  | refl => rfl
  | @step j hij ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Larger squared distance from the center has a no-larger binomial coefficient. -/
theorem choose_antitone_cmbGrid {N : ℕ} (hN : 0 < N) (i j : Fin (N+1))
    (hij : cmbGrid N i < cmbGrid N j) : N.choose j.val ≤ N.choose i.val := by
  have hi := binomialFold_le_half N i.val (by omega)
  have hj := binomialFold_le_half N j.val (by omega)
  have hf : binomialFold N j.val ≤ binomialFold N i.val := by
    by_contra hn
    have hn' : binomialFold N i.val ≤ binomialFold N j.val := by omega
    have hreal : (binomialFold N i.val:ℝ) ≤ binomialFold N j.val := by exact_mod_cast hn'
    have hjreal : 2*(binomialFold N j.val:ℝ) ≤ N := by exact_mod_cast (show 2*binomialFold N j.val ≤ N by omega)
    have hNreal : 0 < (N:ℝ) := by exact_mod_cast hN
    rw [cmbGrid_fold N i, cmbGrid_fold N j] at hij
    have hdiv : ((N:ℝ)-2*binomialFold N j.val)/N ≤ ((N:ℝ)-2*binomialFold N i.val)/N := by
      exact div_le_div_of_nonneg_right (by linarith) hNreal.le
    have hnonneg : 0 ≤ ((N:ℝ)-2*binomialFold N j.val)/N := div_nonneg (by linarith) hNreal.le
    nlinarith
  simpa only [choose_binomialFold N i.val (by omega), choose_binomialFold N j.val (by omega)] using
    choose_le_choose_of_le_half hf hi

/-- Strict negative weighted covariance, retaining one explicit positive-weight witness pair. -/
theorem finite_opposite_covariance_lt {ι : Type*} [Fintype ι] (w Y T : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hopp : ∀ i j, (Y i-Y j)*(T i-T j) ≤ 0)
    (i j : ι) (hwi : 0 < w i) (hwj : 0 < w j)
    (hstrict : (Y i-Y j)*(T i-T j) < 0) :
    (∑ i, w i*Y i*T i)*(∑ i, w i) < (∑ i, w i*Y i)*(∑ i, w i*T i) := by
  have hn : ∑ a, ∑ b, w a*w b*((Y a-Y b)*(T a-T b)) < 0 := by
    apply Finset.sum_neg'
    · intro a _
      exact Finset.sum_nonpos (fun b _ => mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw a) (hw b)) (hopp a b))
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Finset.sum_neg'
      · intro b _
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw i) (hw b)) (hopp i b)
      · exact ⟨j, Finset.mem_univ _, mul_neg_of_pos_of_neg (mul_pos hwi hwj) hstrict⟩
  have he : (∑ a, ∑ b, w a*w b*((Y a-Y b)*(T a-T b))) =
      2*((∑ i, w i*Y i*T i)*(∑ i, w i)-(∑ i, w i*Y i)*(∑ i, w i*T i)) := by
    have ht (a b : ι) : w a*w b*((Y a-Y b)*(T a-T b)) =
        (w a*Y a*T a)*w b+w a*(w b*Y b*T b)-
          (w a*Y a)*(w b*T b)-(w a*T a)*(w b*Y b) := by ring
    simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [he] at hn
  linarith

theorem cmbGrid_one_pos_lt_one (N : ℕ) (hN : 3 ≤ N) :
    0 < cmbGrid N (⟨1,by omega⟩ : Fin (N+1)) ∧ cmbGrid N (⟨1,by omega⟩ : Fin (N+1)) < 1 := by
  have hNr : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < ((N:ℝ)-2)/N := div_pos (by linarith) (by linarith)
  have hd1 : ((N:ℝ)-2)/N < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  simp only [cmbGrid, Nat.cast_one, mul_one]
  constructor <;> nlinarith

/-- For every finite tilt order, increasing the CMB exponent strictly lowers its mean. -/
theorem cmb_tiltedMean_strictAnti (N : ℕ) (hN : 3 ≤ N) (ell : ℕ) (q r : ℝ) (hqr : q < r) :
    cmbMoment N r (ell+1)/cmbMoment N r ell < cmbMoment N q (ell+1)/cmbMoment N q ell := by
  let w (k : Fin (N+1)) := (N.choose k.val:ℝ)^q*cmbGrid N k^ell
  let T (k : Fin (N+1)) := (N.choose k.val:ℝ)^(r-q)
  have hchoose (k : Fin (N+1)) : 0 < (N.choose k.val:ℝ) := by
    exact_mod_cast Nat.choose_pos (show k.val ≤ N by omega)
  have hw (k : Fin (N+1)) : 0 ≤ w k :=
    mul_nonneg (Real.rpow_nonneg (hchoose k).le _) (pow_nonneg (cmbGrid_nonneg N k) _)
  have hopp (i j : Fin (N+1)) : (cmbGrid N i-cmbGrid N j)*(T i-T j) ≤ 0 := by
    rcases lt_trichotomy (cmbGrid N i) (cmbGrid N j) with h | h | h
    · have hc : (N.choose j.val:ℝ) ≤ N.choose i.val := by exact_mod_cast choose_antitone_cmbGrid (by omega) i j h
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.le)
        (sub_nonneg.mpr (Real.rpow_le_rpow (hchoose j).le hc (sub_pos.mpr hqr).le))
    · simp [h]
    · have hc : (N.choose i.val:ℝ) ≤ N.choose j.val := by exact_mod_cast choose_antitone_cmbGrid (by omega) j i h
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.le)
        (sub_nonpos.mpr (Real.rpow_le_rpow (hchoose i).le hc (sub_pos.mpr hqr).le))
  let j : Fin (N+1) := ⟨1,by omega⟩
  have hy := cmbGrid_one_pos_lt_one N hN
  have hwi : 0 < w 0 := by simp [w, cmbGrid_zero N (by omega)]
  have hwj : 0 < w j := mul_pos (Real.rpow_pos_of_pos (hchoose j) _) (pow_pos hy.1 _)
  have hT : 1 < T j := by
    dsimp [T,j]
    rw [Nat.choose_one_right]
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1)
      (show (1:ℝ)<N by exact_mod_cast (show 1<N by omega)) (sub_pos.mpr hqr)
  have hstrict : (cmbGrid N 0-cmbGrid N j)*(T 0-T j) < 0 := by
    simp only [cmbGrid_zero N (by omega), T, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, Real.one_rpow]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hy.2) (sub_neg.mpr hT)
  have H := finite_opposite_covariance_lt w (cmbGrid N) T hw hopp 0 j hwi hwj hstrict
  have hprod (k : Fin (N+1)) : w k*T k = (N.choose k.val:ℝ)^r*cmbGrid N k^ell := by
    dsimp [w,T]
    rw [show (N.choose k.val:ℝ)^q*cmbGrid N k^ell*(N.choose k.val:ℝ)^(r-q) =
      ((N.choose k.val:ℝ)^q*(N.choose k.val:ℝ)^(r-q))*cmbGrid N k^ell by ring,
      ← Real.rpow_add (hchoose k)]
    congr 2
    ring
  have hprodY (k : Fin (N+1)) : w k*cmbGrid N k*T k = (N.choose k.val:ℝ)^r*cmbGrid N k^(ell+1) := by
    rw [show w k*cmbGrid N k*T k=(w k*T k)*cmbGrid N k by ring, hprod, pow_succ]
    ring
  have hqY (k : Fin (N+1)) : w k*cmbGrid N k = (N.choose k.val:ℝ)^q*cmbGrid N k^(ell+1) := by
    dsimp [w]
    rw [pow_succ]
    ring
  simp_rw [hprodY, hprod, hqY] at H
  change cmbMoment N r (ell+1)*cmbMoment N q ell < cmbMoment N q (ell+1)*cmbMoment N r ell at H
  exact (div_lt_div_iff₀ (cmbMoment_pos N (by omega) r ell) (cmbMoment_pos N (by omega) q ell)).mpr H

end RenyiMonotonicity
