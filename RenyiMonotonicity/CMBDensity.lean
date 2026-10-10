module

public import RenyiMonotonicity.CMBLogRatio
public import RenyiMonotonicity.CMBOrdering

/-! The actual CMB to beta-binomial density has interval sublevels on its squared grid. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace RenyiMonotonicity

/-- Logarithm of the unnormalized density ratio. -/
def cmbLogDensity (N : ℕ) (q a : ℝ) (k : ℕ) : ℝ :=
  q*Real.log (N.choose k:ℝ)-Real.log (betaBinomialWeight a N k)

lemma centralLog_fraction {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    centralLog ((u-v)/(u+v))=Real.log u-Real.log v := by
  have hs : u+v≠0 := ne_of_gt (add_pos hu hv)
  have h1 : 1+(u-v)/(u+v)=2*u/(u+v) := by field_simp; ring
  have h2 : 1-(u-v)/(u+v)=2*v/(u+v) := by field_simp; ring
  rw [centralLog,h1,h2,Real.log_div (mul_ne_zero (by norm_num) hu.ne') hs,
    Real.log_div (mul_ne_zero (by norm_num) hv.ne') hs,
    Real.log_mul (by norm_num) hu.ne',Real.log_mul (by norm_num) hv.ne']
  ring

lemma log_multichoose_succ (a : ℝ) (ha : 0<a) (k : ℕ) :
    Real.log (Ring.multichoose a (k+1))-Real.log (Ring.multichoose a k)=
      Real.log (a+k)-Real.log ((k:ℝ)+1) := by
  have H := congrArg Real.log (real_multichoose_mul_succ a k)
  rw [Real.log_mul (by positivity) (real_multichoose_pos a ha _).ne',
    Real.log_mul (by positivity) (real_multichoose_pos a ha _).ne'] at H
  linarith

lemma log_choose_succ (N k : ℕ) (hk : k<N) :
    Real.log (N.choose (k+1):ℝ)-Real.log (N.choose k:ℝ)=
      Real.log ((N:ℝ)-k)-Real.log ((k:ℝ)+1) := by
  have H : (N.choose (k+1):ℝ)*((k:ℝ)+1)=(N.choose k:ℝ)*((N:ℝ)-k) := by
    rw [← Nat.cast_sub (show k≤N by omega)]
    exact_mod_cast Nat.choose_succ_right_eq N k
  have Hp (j : ℕ) (hj : j≤N) : 0<(N.choose j:ℝ) := by exact_mod_cast Nat.choose_pos hj
  have Hn : 0<(N:ℝ)-k := by
    have H : (k:ℝ)<N := by exact_mod_cast hk
    linarith
  have H := congrArg Real.log H
  rw [Real.log_mul (Hp _ (by omega)).ne' (by positivity),
    Real.log_mul (Hp _ (by omega)).ne' Hn.ne'] at H
  linarith

lemma cmbLogDensity_succ (N k : ℕ) (q a : ℝ) (ha : 1<a) (hk : k<N) :
    cmbLogDensity N q a (k+1)-cmbLogDensity N q a k =
      Real.log (a+N-k-1)-Real.log (a+k)-
        (1-q)*(Real.log ((N:ℝ)-k)-Real.log ((k:ℝ)+1)) := by
  have ha0 : 0<a := by linarith
  have hn : N-k=(N-(k+1))+1 := by omega
  have hB (j : ℕ) (hj : j≤N) : Real.log (betaBinomialWeight a N j)=
      Real.log (Ring.multichoose a j)+Real.log (Ring.multichoose a (N-j)) := by
    rw [betaBinomialWeight,ite_eq_left hj,Real.log_mul (real_multichoose_pos a ha0 _).ne'
      (real_multichoose_pos a ha0 _).ne']
  have H₁ := log_multichoose_succ a ha0 k
  have H₂ := log_multichoose_succ a ha0 (N-(k+1))
  rw [← hn] at H₂
  have he : (N-(k+1):ℕ)=(N:ℝ)-k-1 := by
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]; ring
  rw [he] at H₂
  have H₃ := log_choose_succ N k hk
  unfold cmbLogDensity
  rw [hB (k+1) (by omega),hB k (by omega)]
  calc
    _ = q*(Real.log (N.choose (k+1):ℝ)-Real.log (N.choose k:ℝ))-
      (Real.log (Ring.multichoose a (k+1))-Real.log (Ring.multichoose a k))+
      (Real.log (Ring.multichoose a (N-k))-Real.log (Ring.multichoose a (N-(k+1)))) := by ring
    _ = _ := by
      rw [H₁,H₂,H₃]
      rw [show a+((N:ℝ)-k-1)=a+N-k-1 by ring,
        show (N:ℝ)-k-1+1=N-k by ring]
      ring

/-- The left-half adjacent increment factors through a monotone log quotient. -/
lemma cmbLogDensity_succ_central (N k : ℕ) (q a : ℝ) (ha : 1<a) (hk : k<N/2) :
    let x := ((N:ℝ)-2*k-1)/(N+1)
    let c := ((N:ℝ)+1)/(N+2*a-1)
    cmbLogDensity N q a (k+1)-cmbLogDensity N q a k =
      centralLog (c*x)-(1-q)*centralLog x := by
  dsimp
  have hkN : k<N := by omega
  have hN : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hkR : (k:ℝ)<N := by exact_mod_cast hkN
  rw [cmbLogDensity_succ N k q a ha hkN]
  have H₁ := centralLog_fraction (u:=(N:ℝ)-k) (v:=(k:ℝ)+1) (by linarith) (by positivity)
  have H₂ := centralLog_fraction (u:=a+N-k-1) (v:=a+k) (by linarith) (by positivity)
  have he₁ : ((N:ℝ)-k-((k:ℝ)+1))/((N:ℝ)-k+((k:ℝ)+1))=((N:ℝ)-2*k-1)/(N+1) := by ring
  have he₂ : (a+N-k-1-(a+k))/(a+N-k-1+(a+k))=
      ((N:ℝ)+1)/(N+2*a-1)*(((N:ℝ)-2*k-1)/(N+1)) := by
    have h1 : (N:ℝ)+1≠0 := by positivity
    have h2 : (N:ℝ)+2*a-1≠0 := by linarith
    field_simp
    ring
  rw [he₁] at H₁
  rw [he₂] at H₂
  rw [H₁,H₂]

/-- Once an adjacent log density increment on the left half is positive,
all subsequent increments there are nonnegative. -/
lemma cmbLogDensity_step_persistence (N : ℕ) (q a : ℝ) (ha : 1<a)
    (i j : ℕ) (hij : i≤j) (hj : j<N/2)
    (hi : cmbLogDensity N q a i<cmbLogDensity N q a (i+1)) :
    cmbLogDensity N q a j≤cmbLogDensity N q a (j+1) := by
  let x (k : ℕ) : ℝ := ((N:ℝ)-2*k-1)/(N+1)
  let c : ℝ := ((N:ℝ)+1)/(N+2*a-1)
  have hN : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hc0 : 0<c := div_pos (by positivity) (by linarith)
  have hc1 : c<1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hx (k : ℕ) (hk : k<N/2) : x k∈Ioo 0 1 := by
    have hkR : 2*(k:ℝ)+2≤N := by exact_mod_cast (show 2*k+2≤N by omega)
    constructor
    · exact div_pos (by linarith) (by positivity)
    · exact (div_lt_one (by positivity)).mpr (by linarith [(Nat.cast_nonneg k : (0:ℝ)≤k)])
  have hxi := hx i (by omega)
  have hxj := hx j hj
  have hxx : x j≤x i := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have H : (i:ℝ)≤j := by exact_mod_cast hij
    linarith
  have H := (centralLog_scaled_ratio_strictAnti hc0 hc1).antitoneOn hxj hxi hxx
  have he (k : ℕ) (hk : k<N/2) : cmbLogDensity N q a (k+1)-cmbLogDensity N q a k=
      centralLog (c*x k)-(1-q)*centralLog (x k) := cmbLogDensity_succ_central N k q a ha hk
  rw [← sub_pos] at hi
  rw [he i (by omega)] at hi
  have hp := centralLog_pos hxi
  have hpj := centralLog_pos hxj
  have H₁ : 1-q<centralLog (c*x i)/centralLog (x i) := (lt_div_iff₀ hp).mpr (by linarith)
  have H₂ : 1-q≤centralLog (c*x j)/centralLog (x j) := H₁.le.trans H
  have H₃ := (le_div_iff₀ hpj).mp H₂
  rw [← sub_nonneg,he j hj]
  linarith

/-- A finite sequence whose rising increments persist has interval sublevels. -/
lemma finite_valley_of_step_persistence (f : ℕ→ℝ) (M : ℕ)
    (hstep : ∀ i j, i≤j → j<M → f i<f (i+1) → f j≤f (j+1))
    (i j k : ℕ) (hij : i≤j) (hjk : j≤k) (hk : k≤M) :
    f j≤ max (f i) (f k) := by
  have hincr : ∀ j, i≤j → f i<f j → ∃r, i≤r ∧ r<j ∧ f r<f (r+1) := by
    intro j hij
    induction hij with
    | refl => intro h; exact (lt_irrefl _ h).elim
    | @step j hij ih =>
        intro h
        by_cases H : f i<f j
        · obtain ⟨r,hr₁,hr₂,hr₃⟩ := ih H
          exact ⟨r,hr₁,by omega,hr₃⟩
        · exact ⟨j,hij,by omega,by linarith⟩
  by_cases H : f j≤f i
  · exact H.trans (le_max_left _ _)
  · obtain ⟨r,hr₁,hr₂,hr₃⟩ := hincr j hij (lt_of_not_ge H)
    have hmono : ∀ t, j≤t → t≤M → f j≤f t := by
      intro t ht
      induction ht with
      | refl => intro _; rfl
      | @step t ht ih =>
          intro htM
          change j ≤ t at ht
          exact (ih (by omega)).trans (hstep r t (by omega) (by omega) hr₃)
    exact (hmono k hjk hk).trans (le_max_right _ _)

lemma cmbLogDensity_valley (N : ℕ) (q a : ℝ) (ha : 1<a)
    (i j k : ℕ) (hij : i≤j) (hjk : j≤k) (hk : k≤N/2) :
    cmbLogDensity N q a j≤ max (cmbLogDensity N q a i) (cmbLogDensity N q a k) :=
  finite_valley_of_step_persistence _ _ (cmbLogDensity_step_persistence N q a ha) i j k hij hjk hk


lemma cmbLogDensity_fold (N : ℕ) (q a : ℝ) (k : Fin (N+1)) :
    cmbLogDensity N q a (binomialFold N k.val)=cmbLogDensity N q a k.val := by
  unfold cmbLogDensity
  rw [choose_binomialFold N k.val (by omega)]
  unfold binomialFold
  rcases le_total k.val (N-k.val) with h|h
  · rw [min_eq_left h]
  · rw [min_eq_right h,betaBinomialWeight_reflect a N k.val (by omega)]

lemma binomialFold_antitone_cmbGrid (N : ℕ) (hN : 0<N) (i j : Fin (N+1))
    (hij : cmbGrid N i≤cmbGrid N j) : binomialFold N j.val≤binomialFold N i.val := by
  have hi := binomialFold_le_half N i.val (by omega)
  have hj := binomialFold_le_half N j.val (by omega)
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  by_contra H
  have hf : (binomialFold N i.val:ℝ)<binomialFold N j.val := by
    exact_mod_cast (lt_of_not_ge H)
  have hjR : 2*(binomialFold N j.val:ℝ)≤N := by
    exact_mod_cast (show 2*binomialFold N j.val≤N by omega)
  have hnon : 0≤((N:ℝ)-2*binomialFold N j.val)/N := div_nonneg (by linarith) hNr.le
  have hlt : ((N:ℝ)-2*binomialFold N j.val)/N<((N:ℝ)-2*binomialFold N i.val)/N :=
    div_lt_div_of_pos_right (by linarith) hNr
  rw [cmbGrid_fold N i,cmbGrid_fold N j] at hij
  nlinarith

/-- Interval sublevels hold on the actual squared grid, including repeated reflected nodes. -/
theorem cmbLogDensity_grid_valley (N : ℕ) (hN : 0<N) (q a : ℝ) (ha : 1<a)
    (i j k : Fin (N+1)) (hij : cmbGrid N i≤cmbGrid N j) (hjk : cmbGrid N j≤cmbGrid N k) :
    cmbLogDensity N q a j.val ≤ max (cmbLogDensity N q a i.val) (cmbLogDensity N q a k.val) := by
  have H := cmbLogDensity_valley N q a ha (binomialFold N k.val) (binomialFold N j.val)
    (binomialFold N i.val) (binomialFold_antitone_cmbGrid N hN j k hjk)
    (binomialFold_antitone_cmbGrid N hN i j hij) (binomialFold_le_half N i.val (by omega))
  simpa only [cmbLogDensity_fold,max_comm] using H

end RenyiMonotonicity
