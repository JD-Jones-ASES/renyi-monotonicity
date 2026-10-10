module

public import RenyiMonotonicity.NegativeRootProducts
public import RenyiMonotonicity.GegenbauerAngles
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Finite Chebyshev approximants inherit the ordered Gegenbauer root products. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

def chebyshevAffine (L : ℕ) : ℝ[X] := C 1+C (1/(2*(L:ℝ)^2))*X

def chebyshevGegenbauerF (a : ℝ) (m L : ℕ) : ℝ[X] :=
  (monicGegenbauer a m).comp ((Chebyshev.T ℝ (L:ℤ)).comp (chebyshevAffine L))

def chebyshevGegenbauerG (a : ℝ) (m L : ℕ) : ℝ[X] :=
  ((Chebyshev.U ℝ ((L-1:ℕ):ℤ)).comp (chebyshevAffine L))*
    (monicGegenbauer a (m+1)).comp ((Chebyshev.T ℝ (L:ℤ)).comp (chebyshevAffine L))

def chebyshevAngleRoot (L : ℕ) (θ : ℝ) : ℝ := 2*(L:ℝ)^2*(Real.cos (θ/L)-1)

@[simp] theorem chebyshevAffine_eval_zero (L : ℕ) : (chebyshevAffine L).eval 0 = 1 := by
  simp [chebyshevAffine]

theorem chebyshevAffine_degree (L : ℕ) (hL : 0 < L) : (chebyshevAffine L).natDegree=1 := by
  rw [chebyshevAffine, natDegree_C_add, natDegree_C_mul_X]
  positivity

theorem chebyshevAffine_angleRoot (L : ℕ) (hL : 0 < L) (θ : ℝ) :
    (chebyshevAffine L).eval (chebyshevAngleRoot L θ) = Real.cos (θ/L) := by
  have hLr : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [chebyshevAffine, chebyshevAngleRoot, eval_add, eval_C, eval_mul, eval_X]
  field_simp
  ring

theorem chebyshev_T_angleRoot (L : ℕ) (hL : 0 < L) (θ : ℝ) :
    ((Chebyshev.T ℝ (L:ℤ)).comp (chebyshevAffine L)).eval (chebyshevAngleRoot L θ) = Real.cos θ := by
  rw [eval_comp, chebyshevAffine_angleRoot L hL, Chebyshev.T_real_cos]
  congr 1
  have hLr : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp

theorem chebyshevAngleRoot_neg (L : ℕ) (hL : 0 < L) (θ : ℝ)
    (hθ : 0 < θ) (hθL : θ < (L:ℝ)*Real.pi) : chebyshevAngleRoot L θ < 0 := by
  have hLr : 0 < (L:ℝ) := by exact_mod_cast hL
  have hx : 0 < θ/L := div_pos hθ hLr
  have hxπ : θ/L < Real.pi := (div_lt_iff₀ hLr).mpr (by nlinarith)
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by rfl) hxπ.le hx
  simp only [Real.cos_zero] at hc
  exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hc)

theorem chebyshevAngleRoot_strictAnti (L : ℕ) (hL : 0 < L) :
    StrictAntiOn (chebyshevAngleRoot L) (Set.Ioo 0 ((L:ℝ)*Real.pi)) := by
  intro x hx y hy hxy
  have hLr : 0 < (L:ℝ) := by exact_mod_cast hL
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (div_nonneg hx.1.le hLr.le)
    ((div_le_iff₀ hLr).mpr (by nlinarith [hy.2])) ((div_lt_div_iff_of_pos_right hLr).mpr hxy)
  unfold chebyshevAngleRoot
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hc 1) (by positivity)

/-- A full number of periods of strictly interior angles stays below the terminal endpoint. -/
theorem periodicRootAngle_lt_periods {m : ℕ} (hm : 0 < m) (θ : Fin m → ℝ)
    (hθ : ∀ i, θ i < Real.pi) (L j : ℕ) (hj : j < m*L) :
    periodicRootAngle hm θ j < (L:ℝ)*Real.pi := by
  have hdiv : j/m < L := (Nat.div_lt_iff_lt_mul hm).mpr (by simpa [mul_comm] using hj)
  have hc : (j/m:ℕ)+1 ≤ L := by omega
  have hcr : ((j/m:ℕ):ℝ)+1 ≤ L := by exact_mod_cast hc
  unfold periodicRootAngle
  nlinarith [hθ ⟨j%m,Nat.mod_lt _ hm⟩, Real.pi_pos]

/-- Degree and positive normalization of the actual finite approximants. -/
theorem chebyshevGegenbauer_degrees (a : ℝ) (m L : ℕ) (hL : 0 < L) :
    (chebyshevGegenbauerF a m L).natDegree=m*L ∧
      (chebyshevGegenbauerG a m L).natDegree ≤ (m+2)*L-1 := by
  have hT : ((Chebyshev.T ℝ (L:ℤ)).comp (chebyshevAffine L)).natDegree=L := by
    rw [natDegree_comp, Chebyshev.natDegree_T, Int.natAbs_natCast, chebyshevAffine_degree L hL, mul_one]
  constructor
  · rw [chebyshevGegenbauerF, natDegree_comp, (monicGegenbauer_monic_degree a m).2, hT]
  · apply natDegree_mul_le.trans
    rw [natDegree_comp, Chebyshev.natDegree_U_natCast, chebyshevAffine_degree L hL, mul_one,
      natDegree_comp, (monicGegenbauer_monic_degree a (m+1)).2, hT]
    rw [show (m+2)*L=(m+1)*L+L by ring]
    omega

theorem chebyshevGegenbauer_zero_pos (a : ℝ) (ha : 0 < a) (m L : ℕ) (hL : 0 < L) :
    0 < (chebyshevGegenbauerF a m L).eval 0 ∧ 0 < (chebyshevGegenbauerG a m L).eval 0 := by
  simp only [chebyshevGegenbauerF, chebyshevGegenbauerG, eval_comp, chebyshevAffine_eval_zero,
    Chebyshev.T_eval_one, eval_mul, Chebyshev.U_eval_one]
  constructor
  · exact monicGegenbauer_eval_one_pos a ha m
  · apply mul_pos _ (monicGegenbauer_eval_one_pos a ha (m+1))
    have H : ((L-1:ℕ):ℝ)+1 = L := by exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ L by omega))
    push_cast
    rw [H]
    exact_mod_cast hL

/-- The terminal sine angle of a full block is exactly the endpoint of the full period range. -/
theorem periodic_sineAngle_last {P : ℝ[X]} {n : ℕ} (s : RealRootList P n)
    (L : ℕ) (hL : 0 < L) :
    periodicRootAngle (by omega : 0 < n+1) s.sineAngle ((n+1)*L-1) = (L:ℝ)*Real.pi := by
  have he : (n+1)*L-1 = n+(n+1)*(L-1) := by
    have H := Nat.mul_sub_left_distrib (n+1) L 1
    have hn : n+1 ≤ (n+1)*L := Nat.le_mul_of_pos_right _ hL
    simp only [Nat.mul_one] at H
    omega
  have hdiv : ((n+1)*L-1)/(n+1) = L-1 := by
    rw [he, Nat.add_mul_div_left _ _ (by omega)]
    simp [Nat.div_eq_of_lt (show n<n+1 by omega)]
  have hmod : ((n+1)*L-1)%(n+1) = n := by
    rw [he, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [periodicRootAngle, hdiv, hmod, RealRootList.sineAngle, lt_self_iff_false,
    ↓reduceDIte]
  have H : ((L-1:ℕ):ℝ)+1 = L := by exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ L by omega))
  rw [← H]
  ring

/-- Removing the terminal sine zero leaves every root strictly inside the cosine arc. -/
theorem periodic_sineAngle_lt_periods {P : ℝ[X]} {n : ℕ} (s : RealRootList P n)
    (hs : ∀ i, -1 < s.root i ∧ s.root i < 1) (L : ℕ) (hL : 0 < L) (j : ℕ)
    (hj : j < (n+1)*L-1) :
    periodicRootAngle (by omega : 0 < n+1) s.sineAngle j < (L:ℝ)*Real.pi := by
  rw [← periodic_sineAngle_last s L hL]
  exact periodicRootAngle_strictMono (by omega) s.sineAngle (s.sineAngle_mem hs)
    (s.sineAngle_strictMono hs) hj

/-- Every sine-augmented angle annihilates the product of the two actual factors. -/
theorem chebyshevGegenbauerG_angle_zero (a : ℝ) (m L : ℕ) (hL : 0 < L)
    (s : RealRootList (monicGegenbauer a (m+1)) (m+1))
    (hs : ∀ i, -1 < s.root i ∧ s.root i < 1) (j : ℕ) (hj : j < (m+2)*L-1) :
    (chebyshevGegenbauerG a m L).eval
      (chebyshevAngleRoot L (periodicRootAngle (by omega : 0 < m+2) s.sineAngle j)) = 0 := by
  let θ := periodicRootAngle (by omega : 0 < m+2) s.sineAngle j
  rw [chebyshevGegenbauerG, eval_mul, eval_comp, chebyshevAffine_angleRoot L hL,
    eval_comp, chebyshev_T_angleRoot L hL]
  change (Chebyshev.U ℝ ((L-1:ℕ):ℤ)).eval (Real.cos (θ/L))*
    (monicGegenbauer a (m+1)).eval (Real.cos θ) = 0
  by_cases hrem : j%(m+2) < m+1
  · have hz : (monicGegenbauer a (m+1)).eval (Real.cos θ)=0 := by
      dsimp [θ,periodicRootAngle,RealRootList.sineAngle]
      rw [dite_eq_left hrem, add_comm, Real.cos_add_nat_mul_pi]
      simp only [RealRootList.angle, Real.cos_arccos (hs _).1.le (hs _).2.le]
      rcases neg_one_pow_eq_or ℝ (j/(m+2)) with h | h
      · rw [h,one_mul]; exact s.isRoot _
      · rw [h,neg_one_mul,monicGegenbauer_eval_neg,s.isRoot,mul_zero]
    rw [hz,mul_zero]
  · have hsin : Real.sin θ=0 := by
      dsimp [θ,periodicRootAngle,RealRootList.sineAngle]
      rw [dite_eq_right hrem]
      rw [show ((j/(m+2):ℕ):ℝ)*Real.pi+Real.pi = ((j/(m+2)+1:ℕ):ℝ)*Real.pi by push_cast; ring]
      exact Real.sin_nat_mul_pi _
    have hθ : 0 < θ := periodicRootAngle_pos _ _ (fun i => (s.sineAngle_mem hs i).1) j
    have hθL : θ < (L:ℝ)*Real.pi := periodic_sineAngle_lt_periods s hs L hL j hj
    have hLr : 0 < (L:ℝ) := by exact_mod_cast hL
    have hx : 0 < Real.sin (θ/L) := Real.sin_pos_of_pos_of_lt_pi (div_pos hθ hLr)
      ((div_lt_iff₀ hLr).mpr (by nlinarith))
    have H := Chebyshev.U_real_cos (θ/L) ((L-1:ℕ):ℤ)
    have harg : (((L-1:ℕ):ℤ)+1:ℝ)*(θ/L)=θ := by
      have hc : (((L-1:ℕ):ℤ)+1:ℝ) = L := by
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ L by omega))
      rw [hc]
      field_simp
    rw [harg,hsin] at H
    have hz := (mul_eq_zero.mp H).resolve_right hx.ne'
    rw [hz,zero_mul]

/-- The actual finite Chebyshev/Gegenbauer polynomials obey the coefficient
cross inequality because their complete negative root lists are ordered. -/
theorem chebyshevGegenbauer_cross_nonneg (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : 0 < L) (k : ℕ) (hk : k < (m+2)*L-1) :
    (chebyshevGegenbauerF a m L).coeff (k+1)*(chebyshevGegenbauerG a m L).coeff k ≤
      (chebyshevGegenbauerF a m L).coeff k*(chebyshevGegenbauerG a m L).coeff (k+1) := by
  obtain ⟨r,s,hr,hs,hθ,hφ,hdom⟩ := gegenbauer_periodic_angle_domination a ha m hm
  let θ := periodicRootAngle hm r.angle
  let φ := periodicRootAngle (by omega : 0 < m+2) s.sineAngle
  let rf : Fin (m*L) → ℝ := fun i => chebyshevAngleRoot L (θ i.val)
  let rg : Fin ((m+2)*L-1) → ℝ := fun i => chebyshevAngleRoot L (φ i.val)
  have hθmem (i : Fin (m*L)) : θ i.val ∈ Set.Ioo 0 ((L:ℝ)*Real.pi) :=
    ⟨periodicRootAngle_pos hm r.angle (fun j => (r.angle_mem hr j).1) i.val,
      periodicRootAngle_lt_periods hm r.angle (fun j => (r.angle_mem hr j).2) L i.val i.isLt⟩
  have hφmem (i : Fin ((m+2)*L-1)) : φ i.val ∈ Set.Ioo 0 ((L:ℝ)*Real.pi) :=
    ⟨(hdom i.val).1, periodic_sineAngle_lt_periods s hs L hL i.val i.isLt⟩
  have hrfinj : Function.Injective rf := by
    apply StrictAnti.injective
    intro i j hij
    exact chebyshevAngleRoot_strictAnti L hL (hθmem i) (hθmem j) (hθ hij)
  have hrginj : Function.Injective rg := by
    apply StrictAnti.injective
    intro i j hij
    exact chebyshevAngleRoot_strictAnti L hL (hφmem i) (hφmem j) (hφ hij)
  have hrf (i : Fin (m*L)) : rf i < 0 := chebyshevAngleRoot_neg L hL _ (hθmem i).1 (hθmem i).2
  have hrg (i : Fin ((m+2)*L-1)) : rg i < 0 := chebyshevAngleRoot_neg L hL _ (hφmem i).1 (hφmem i).2
  have hzf (i : Fin (m*L)) : (chebyshevGegenbauerF a m L).eval (rf i)=0 := by
    rw [chebyshevGegenbauerF, eval_comp]
    change (monicGegenbauer a m).eval
      (((Chebyshev.T ℝ (L:ℤ)).comp (chebyshevAffine L)).eval (chebyshevAngleRoot L (θ i.val)))=0
    rw [chebyshev_T_angleRoot L hL]
    exact monicGegenbauer_periodic_angle_zero a m hm r hr i.val
  have hzg (i : Fin ((m+2)*L-1)) : (chebyshevGegenbauerG a m L).eval (rg i)=0 :=
    chebyshevGegenbauerG_angle_zero a m L hL s hs i.val i.isLt
  have hzero := chebyshevGegenbauer_zero_pos a ha m L hL
  have hdegree := chebyshevGegenbauer_degrees a m L hL
  have hfp := polynomial_eq_positiveFactorProduct (chebyshevGegenbauerF a m L) rf
    hzero.1.ne' hdegree.1.le hrfinj hrf hzf
  have hgp := polynomial_eq_positiveFactorProduct (chebyshevGegenbauerG a m L) rg
    hzero.2.ne' hdegree.2 hrginj hrg hzg
  have hsize : m*L ≤ (m+2)*L-1 := by
    rw [show (m+2)*L=m*L+2*L by ring]
    omega
  have hcross := linearFactorProduct_cross_of_le hsize (fun i => 1/(-rf i)) (fun i => 1/(-rg i))
    (fun i => (div_pos zero_lt_one (neg_pos.mpr (hrf i))).le)
    (fun i => (div_pos zero_lt_one (neg_pos.mpr (hrg i))).le)
    (fun i => show 1/(-rf i) ≤ 1/(-rg (Fin.castLE hsize i)) from by
      have ho : rf i ≤ rg (Fin.castLE hsize i) :=
        (chebyshevAngleRoot_strictAnti L hL).antitoneOn
          (hφmem (Fin.castLE hsize i)) (hθmem i) (hdom i.val).2
      exact div_le_div_of_nonneg_left zero_le_one (neg_pos.mpr (hrg _)) (by linarith)) k hk
  have H := mul_le_mul_of_nonneg_left hcross (mul_pos hzero.1 hzero.2).le
  rw [hfp,hgp]
  simp only [coeff_C_mul]
  convert H using 1 <;> ring

/-- The same comparison at every coefficient index, with exact zero coefficients
above the finite polynomial degrees. -/
theorem chebyshevGegenbauer_cross_nonneg_all (a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : 0 < L) (k : ℕ) :
    (chebyshevGegenbauerF a m L).coeff (k+1)*(chebyshevGegenbauerG a m L).coeff k ≤
      (chebyshevGegenbauerF a m L).coeff k*(chebyshevGegenbauerG a m L).coeff (k+1) := by
  by_cases hk : k < (m+2)*L-1
  · exact chebyshevGegenbauer_cross_nonneg a ha m hm L hL k hk
  · have hd := chebyshevGegenbauer_degrees a m L hL
    have hsize : m*L ≤ (m+2)*L-1 := by
      rw [show (m+2)*L=m*L+2*L by ring]
      omega
    rw [coeff_eq_zero_of_natDegree_lt (show (chebyshevGegenbauerF a m L).natDegree < k+1 by omega),
      coeff_eq_zero_of_natDegree_lt (show (chebyshevGegenbauerG a m L).natDegree < k+1 by omega)]
    simp

end RenyiMonotonicity
