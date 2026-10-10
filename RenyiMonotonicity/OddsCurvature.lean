module

public import RenyiMonotonicity.OddsTilt
public import RenyiMonotonicity.SecondDerivativeMinimum

/-! Actual common-odds curvature at an interior coin minimum. -/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Filter

namespace RenyiMonotonicity

/-- General second path derivative of the actual scalar edge. -/
theorem hasDerivAt_massEdge_path_gradient (q : ℝ) (a b da db : ℝ → ℝ) (u v : ℝ)
    (ha : HasDerivAt a (da 0) 0) (hb : HasDerivAt b (db 0) 0)
    (hda : HasDerivAt da u 0) (hdb : HasDerivAt db v 0)
    (hs : 0 < a 0+b 0) :
    HasDerivAt (fun t => da t*massGradientScalar q (a t) (b t)-
      db t*massGradientScalar q (b t) (a t))
      (massEdgeHessian q (a 0) (b 0) (da 0) (db 0)+
        (u*massGradientScalar q (a 0) (b 0)-v*massGradientScalar q (b 0) (a 0))) 0 := by
  have hG := hasDerivAt_massGradientScalar_pair q a b _ _ 0 ha hb hs
  have hG' := hasDerivAt_massGradientScalar_pair q b a _ _ 0 hb ha (by simpa [add_comm] using hs)
  convert (hda.mul hG).sub (hdb.mul hG') using 1
  have he : (a 0+b 0)^(q-2) = (a 0+b 0)^(q-3)*(a 0+b 0) := by
    rw [← Real.rpow_add_one hs.ne']; congr 1; ring
  unfold massEdgeHessian massGradientScalar
  rw [add_comm (b 0) (a 0), he]
  ring

/-- Geometric count tilting, expressed with real powers on every integer index. -/
def countTilt (g : ℤ → ℝ) (t : ℝ) (k : ℤ) : ℝ := (1+t)^(k:ℝ)*g k

def countTiltDerivative (g : ℤ → ℝ) (t : ℝ) (k : ℤ) : ℝ :=
  (k:ℝ)*(1+t)^((k:ℝ)-1)*g k

@[simp] theorem countTilt_zero (g : ℤ → ℝ) : countTilt g 0 = g := by
  funext k
  simp [countTilt]

@[simp] theorem countTiltDerivative_zero (g : ℤ → ℝ) :
    countTiltDerivative g 0 = fun k : ℤ => (k:ℝ)*g k := by
  funext k
  simp [countTiltDerivative]

theorem hasDerivAt_countTilt (g : ℤ → ℝ) (t : ℝ) (ht : 0 < 1+t) (k : ℤ) :
    HasDerivAt (fun s => countTilt g s k) (countTiltDerivative g t k) t := by
  simpa only [countTilt, countTiltDerivative, one_mul, id_eq] using
    (((hasDerivAt_id t).const_add 1).rpow_const (p := (k:ℝ)) (Or.inl ht.ne')).mul_const (g k)

theorem hasDerivAt_countTiltDerivative_zero (g : ℤ → ℝ) (k : ℤ) :
    HasDerivAt (fun t => countTiltDerivative g t k) (((k:ℝ)^2-k)*g k) 0 := by
  have hb : HasDerivAt (fun t : ℝ => 1+t) 1 0 := (hasDerivAt_id 0).const_add 1
  have H := ((hb.rpow_const (p := (k:ℝ)-1) (Or.inl (by norm_num))).const_mul (k:ℝ)).mul_const (g k)
  convert H using 1
  · rfl
  · simp only [add_zero, Real.one_rpow, mul_one, one_mul]
    ring

/-- Actual derivative of the finite tilted functional on its positive-edge neighborhood. -/
theorem hasDerivAt_countTilt_functional (q : ℝ) (n : ℕ) (g : ℤ → ℝ) (t : ℝ)
    (ht : 0 < 1+t) (hleft : g (-1)=0) (hright : g ((n:ℤ)+1)=0)
    (hs : ∀ k : Fin (n+2), 0 < countTilt g t ((k.val:ℤ)-1)+countTilt g t k.val) :
    HasDerivAt (fun t => finiteMassFunctional q n (countTilt g t))
      (massGradientPairing q n (countTilt g t) (countTiltDerivative g t)) t :=
  hasDerivAt_finiteMassFunctional_path q n (countTilt g) (countTiltDerivative g t) t
    (hasDerivAt_countTilt g t ht) hs (by simp [countTiltDerivative, hleft])
    (by simp [countTiltDerivative, hright])

/-- The actual second derivative of the geometric tilt is the Hessian plus
its factorial count moment, including the two zero exterior masses. -/
theorem hasDerivAt_countTilt_gradient (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1)=0) (hright : g ((n:ℤ)+1)=0)
    (hs : ∀ k : Fin (n+2), 0 < g ((k.val:ℤ)-1)+g k.val) :
    HasDerivAt (fun t => massGradientPairing q n (countTilt g t) (countTiltDerivative g t))
      (massHessian q n g (fun k : ℤ => (k:ℝ)*g k)+
        massGradientPairing q n g (fun k => ((k:ℝ)^2-k)*g k)) 0 := by
  have he (t : ℝ) := massGradientPairing_edges q n (countTilt g t) (countTiltDerivative g t)
    (by simp [countTiltDerivative, hleft]) (by simp [countTiltDerivative, hright])
  simp_rw [he]
  rw [massGradientPairing_edges q n g _ (by simp [hleft]) (by simp [hright])]
  unfold massHessian
  rw [← Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum
  intro k _
  have H := hasDerivAt_massEdge_path_gradient q
    (fun t => countTilt g t ((k.val:ℤ)-1)) (fun t => countTilt g t k.val)
    (fun t => countTiltDerivative g t ((k.val:ℤ)-1)) (fun t => countTiltDerivative g t k.val)
    _ _ (hasDerivAt_countTilt g 0 (by norm_num) _) (hasDerivAt_countTilt g 0 (by norm_num) _)
    (hasDerivAt_countTiltDerivative_zero g _) (hasDerivAt_countTiltDerivative_zero g _)
    (by simpa using hs k)
  simpa using H

/-- Local minimality of the genuine tilted path gives nonnegative curvature. -/
theorem countTilt_curvature_nonneg (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1)=0) (hright : g ((n:ℤ)+1)=0)
    (hs : ∀ k : Fin (n+2), 0 < g ((k.val:ℤ)-1)+g k.val)
    (hmin : IsLocalMin (fun t => finiteMassFunctional q n (countTilt g t)) 0) :
    0 ≤ massHessian q n g (fun k : ℤ => (k:ℝ)*g k)+
      massGradientPairing q n g (fun k => ((k:ℝ)^2-k)*g k) := by
  apply secondDerivative_nonneg_of_localMin (d := fun t =>
    massGradientPairing q n (countTilt g t) (countTiltDerivative g t)) _
    (hasDerivAt_countTilt_gradient q n g hleft hright hs) hmin
  have hbase : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+t :=
    (show ContinuousAt (fun t : ℝ => 1+t) 0 by fun_prop).eventually (isOpen_Ioi.mem_nhds (by norm_num))
  have hedge (k : Fin (n+2)) : ∀ᶠ t in 𝓝 (0:ℝ),
      0 < countTilt g t ((k.val:ℤ)-1)+countTilt g t k.val := by
    have hc := (hasDerivAt_countTilt g 0 (by norm_num) ((k.val:ℤ)-1)).continuousAt.add
      (hasDerivAt_countTilt g 0 (by norm_num) k.val).continuousAt
    exact hc.eventually (isOpen_Ioi.mem_nhds (by simpa using hs k))
  filter_upwards [hbase, Filter.eventually_all.mpr hedge] with t ht hs
  exact hasDerivAt_countTilt_functional q n g t ht hleft hright hs

/-- The real-power tilt agrees with the actual unnormalized Bernoulli tilt. -/
theorem countTilt_bernoulli_eq {n : ℕ} (p : Fin n → ℝ) (t : ℝ) :
    countTilt (bernoulliMass p) t = fun k => (1+t)^k.toNat*bernoulliMass p k := by
  funext k
  by_cases hk : 0 ≤ k
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp [countTilt, Real.rpow_natCast]
  · simp [countTilt, bernoulliMass_neg _ _ (lt_of_not_ge hk)]

/-- At an actual stationary zero minimum, the common-odds curvature is nonnegative. -/
theorem bernoulli_odds_curvature_nonneg {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i < 1/2)
    (hD : midpointFunctional q p = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) = 0)
    (hmin : ∀ r : Fin (n+1) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    0 ≤ massHessian q (n+1) (bernoulliMass p) (fun k : ℤ => (k:ℝ)*bernoulliMass p k)+
      quadraticMassMoment q (n+1) (bernoulliMass p) := by
  have hp₁ : ∀ i, p i < 1 := fun i => by linarith [hpHalf i]
  have hfirst := firstMassMoment_eq_zero_of_stationary q p hp hp₁ hD hstat
  have hlocal : IsLocalMin (fun t => finiteMassFunctional q (n+1) (countTilt (bernoulliMass p) t)) 0 := by
    simp_rw [countTilt_bernoulli_eq]
    exact oddsTilt_mass_localMin q p hp hpHalf hD hmin
  have hc := countTilt_curvature_nonneg q (n+1) (bernoulliMass p)
    (bernoulliMass_outer_left p) (bernoulliMass_outer_right p) (edgeSum_pos p hp hp₁) hlocal
  have he : massGradientPairing q (n+1) (bernoulliMass p)
      (fun k => ((k:ℝ)^2-k)*bernoulliMass p k) = quadraticMassMoment q (n+1) (bernoulliMass p) := by
    rw [show (fun k : ℤ => ((k:ℝ)^2-k)*bernoulliMass p k) =
      (fun k : ℤ => (k:ℝ)^2*bernoulliMass p k-(k:ℝ)*bernoulliMass p k) by funext k; ring,
      massGradientPairing_sub, hfirst, sub_zero]
    rfl
  rwa [he] at hc

/-- The second strict contact sign follows from actual coin minimality and M2<0. -/
theorem cubicEdgeKernel_neg_of_stationary_minimum {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i < 1/2)
    (hD : midpointFunctional q p = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) = 0)
    (hmin : ∀ r : Fin (n+1) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r)
    (hM : quadraticMassMoment q (n+1) (bernoulliMass p) < 0) :
    cubicEdgeKernel q (n+1) (bernoulliMass p) < 0 :=
  cubicEdgeKernel_neg_of_curvature q (n+1) _ hq₀ hq₁ (bernoulliMass_outer_left p)
    (bernoulliMass_outer_right p) (edgeSum_pos p hp (fun i => by linarith [hpHalf i])) hM
    (bernoulli_odds_curvature_nonneg q p hp hpHalf hD hstat hmin)

end RenyiMonotonicity
