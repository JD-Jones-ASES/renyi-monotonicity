module

public import RenyiMonotonicity.ContactCalculus

/-! Actual mass-edge Hessian identities used at an entropy contact. -/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Filter
namespace RenyiMonotonicity

/-- The quadratic form of the actual edge Hessian. -/
def massEdgeHessian (q a b u v : ℝ) : ℝ :=
  (q - 1) * (a + b) ^ (q - 3) *
    (2 * (u - v) * (u + v) * (a + b) + (q - 2) * (a - b) * (u + v) ^ 2)

/-- Differentiation of the actual scalar mass gradient in both mass arguments. -/
theorem hasDerivAt_massGradientScalar_pair (q : ℝ) (a b : ℝ → ℝ) (u v t : ℝ)
    (ha : HasDerivAt a u t) (hb : HasDerivAt b v t) (hs : 0 < a t + b t) :
    HasDerivAt (fun s => massGradientScalar q (a s) (b s))
      ((q * u + (2 - q) * v) * (a t + b t) ^ (q - 2) +
        (q * a t + (2 - q) * b t) * ((u + v) * (q - 2) * (a t + b t) ^ (q - 3))) t := by
  convert ((ha.const_mul q).add (hb.const_mul (2 - q))).mul
    ((ha.add hb).rpow_const (p := q - 2) (Or.inl hs.ne')) using 1
  · rfl
  · simp only [Pi.add_apply, show q - 2 - 1 = q - 3 by ring]

/-- This explicit Hessian is the derivative of the actual first directional
mass derivative, rather than an assumed curvature certificate. -/
theorem hasDerivAt_massEdge_first_direction (q a b u v : ℝ) (hs : 0 < a + b) :
    HasDerivAt (fun t : ℝ => u * massGradientScalar q (a + t * u) (b + t * v) -
      v * massGradientScalar q (b + t * v) (a + t * u))
      (massEdgeHessian q a b u v) 0 := by
  have ha : HasDerivAt (fun t : ℝ => a + t * u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add a
  have hb : HasDerivAt (fun t : ℝ => b + t * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add b
  have h₁ := (hasDerivAt_massGradientScalar_pair q _ _ u v 0 ha hb (by simpa using hs)).const_mul u
  have h₂ := (hasDerivAt_massGradientScalar_pair q _ _ v u 0 hb ha (by simpa [add_comm] using hs)).const_mul v
  convert h₁.sub h₂ using 1
  simp only [zero_mul, add_zero]
  have hp : (a + b) ^ (q - 2) = (a + b) ^ (q - 3) * (a + b) := by
    rw [← Real.rpow_add_one hs.ne']
    congr 1
    ring
  rw [add_comm b a, hp]
  unfold massEdgeHessian
  ring

/-- The exact interior-edge Hessian identity, where both mass denominators
are strictly positive. -/
theorem massEdgeHessian_identity (q a b u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    massEdgeHessian q a b u v =
      (q - 1) * (u ^ 2 / a * massGradientScalar q a b -
        v ^ 2 / b * massGradientScalar q b a) -
      (q - 1) * (q - 2) * (a - b) * (a + b) ^ (q - 3) *
        (b * u - a * v) ^ 2 / (a * b) := by
  have hs : 0 < a + b := add_pos ha hb
  have hp : (a + b) ^ (q - 2) = (a + b) ^ (q - 3) * (a + b) := by
    rw [← Real.rpow_add_one hs.ne']
    congr 1
    ring
  unfold massEdgeHessian massGradientScalar
  rw [add_comm b a, hp]
  field_simp
  ring

/-- The zero left edge is differentiated separately; the exterior direction
vanishes and no division by its zero mass is used. -/
theorem massEdgeHessian_left_edge (q b v : ℝ) (hb : 0 < b) :
    massEdgeHessian q 0 b 0 v = -(q * (q - 1) * b ^ (q - 2) * v ^ 2) := by
  have hp : b ^ (q - 2) = b ^ (q - 3) * b := by
    rw [← Real.rpow_add_one hb.ne']
    congr 1
    ring
  unfold massEdgeHessian
  simp only [zero_add, zero_sub]
  rw [hp]
  ring

/-- The zero right edge is the corresponding positive one-variable power. -/
theorem massEdgeHessian_right_edge (q a u : ℝ) (ha : 0 < a) :
    massEdgeHessian q a 0 u 0 = q * (q - 1) * a ^ (q - 2) * u ^ 2 := by
  have hp : a ^ (q - 2) = a ^ (q - 3) * a := by
    rw [← Real.rpow_add_one ha.ne']
    congr 1
    ring
  unfold massEdgeHessian
  simp only [add_zero, sub_zero]
  rw [hp]
  ring

/-- The full finite mass Hessian, summing both outer edges literally. -/
def massHessian (q : ℝ) (n : ℕ) (g h : ℤ → ℝ) : ℝ :=
  ∑ k : Fin (n + 2), massEdgeHessian q (g ((k.val : ℤ) - 1)) (g (k.val : ℤ))
    (h ((k.val : ℤ) - 1)) (h (k.val : ℤ))

/-- The cubic edge kernel; outer edges vanish through their product of masses. -/
def cubicEdgeKernel (q : ℝ) (n : ℕ) (g : ℤ → ℝ) : ℝ :=
  ∑ k : Fin (n + 2), (g ((k.val : ℤ) - 1) - g (k.val : ℤ)) *
    (g ((k.val : ℤ) - 1) + g (k.val : ℤ)) ^ (q - 3) *
      g ((k.val : ℤ) - 1) * g (k.val : ℤ)

/-- The quadratic weighted mass-gradient moment at contact. -/
def quadraticMassMoment (q : ℝ) (n : ℕ) (g : ℤ → ℝ) : ℝ :=
  massGradientPairing q n g (fun k => (k : ℝ) ^ 2 * g k)

/-- The first-moment mass direction has an exact division-free edge residual. -/
theorem massEdgeHessian_index_direction (q a b k : ℝ) (hs : 0 < a + b) :
    massEdgeHessian q a b ((k - 1) * a) (k * b) =
      (q - 1) * (((k - 1) ^ 2 * a) * massGradientScalar q a b -
        (k ^ 2 * b) * massGradientScalar q b a) -
      (q - 1) * (q - 2) * (a - b) * (a + b) ^ (q - 3) * a * b := by
  have hp : (a + b) ^ (q - 2) = (a + b) ^ (q - 3) * (a + b) := by
    rw [← Real.rpow_add_one hs.ne']
    congr 1
    ring
  unfold massEdgeHessian massGradientScalar
  rw [add_comm b a, hp]
  ring

/-- The exact finite C3 identity in the first-moment direction, valid through
both exterior zero masses. -/
theorem massHessian_index_direction (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    massHessian q n g (fun k => (k : ℝ) * g k) =
      (q - 1) * quadraticMassMoment q n g - (q - 1) * (q - 2) * cubicEdgeKernel q n g := by
  unfold quadraticMassMoment
  rw [massGradientPairing_edges q n g _ (by simp [hleft]) (by simp [hright])]
  unfold massHessian cubicEdgeKernel
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  simpa only [mul_assoc] using massEdgeHessian_index_direction q _ _ (k.val : ℝ) (hs k)

/-- The common odds-tilt curvature expression, after its scaling terms vanish. -/
theorem massHessian_add_quadratic (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    massHessian q n g (fun k => (k : ℝ) * g k) + quadraticMassMoment q n g =
      q * quadraticMassMoment q n g - (q - 1) * (q - 2) * cubicEdgeKernel q n g := by
  rw [massHessian_index_direction q n g hleft hright hs]
  ring

/-- Negative quadratic contact moment and nonnegative actual tilt curvature
force a strictly negative cubic edge kernel. -/
theorem cubicEdgeKernel_neg_of_curvature (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hM : quadraticMassMoment q n g < 0)
    (hcurv : 0 ≤ massHessian q n g (fun k => (k : ℝ) * g k) + quadraticMassMoment q n g) :
    cubicEdgeKernel q n g < 0 := by
  rw [massHessian_add_quadratic q n g hleft hright hs] at hcurv
  have hqM := mul_neg_of_pos_of_neg hq₀ hM
  have hprod : 0 < (q - 1) * (q - 2) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  by_contra hn
  have hc : 0 ≤ (q - 1) * (q - 2) * cubicEdgeKernel q n g := mul_nonneg hprod.le (le_of_not_gt hn)
  linarith

end RenyiMonotonicity
