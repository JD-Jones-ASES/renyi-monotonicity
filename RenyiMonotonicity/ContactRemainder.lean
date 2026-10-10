module

public import RenyiMonotonicity.ContactCurvature
public import RenyiMonotonicity.ContactLocalMin
public import Mathlib.Analysis.Analytic.Binomial

/-! Verified fourth-order remainder for the cubic splitting mass path. -/

@[expose] public section
noncomputable section
open scoped Topology
open Filter Asymptotics
namespace RenyiMonotonicity

/-- The real binomial series gives a genuine quadratic error bound. -/
theorem one_add_rpow_linear_remainder (r : ℝ) :
    (fun x : ℝ => (1 + x) ^ r - 1 - r * x) =O[𝓝 0] (fun x => x ^ 2) := by
  have h := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := r)).isBigO_sub_partialSum_pow 2
  simpa [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, binomialSeries_apply,
    Real.norm_eq_abs, sq_abs, sub_add_eq_sub_sub, binomialSeries, mul_comm] using h

/-- A quadratic-plus-cubic displacement is of quadratic order. -/
theorem quadratic_cubic_isBigO (u v : ℝ) :
    (fun t : ℝ => t ^ 2 * u + t ^ 3 * v) =O[𝓝 0] (fun t => t ^ 2) := by
  have hf : Tendsto (fun t : ℝ => u + t * v) (𝓝 0) (𝓝 u) := by
    simpa only [zero_mul, add_zero] using
      (show Continuous (fun t : ℝ => u + t * v) by fun_prop).tendsto 0
  have H := (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).mul (hf.isBigO_one (F := ℝ))
  convert H using 1 <;> ext t <;> ring

/-- The fractional power along a quadratic-cubic path has a fourth-order
remainder, derived from its convergent binomial series near the positive base. -/
theorem rpow_quadratic_cubic_remainder (r s u v : ℝ) (hs : 0 < s) :
    (fun t : ℝ => (s + t ^ 2 * u + t ^ 3 * v) ^ r - s ^ r -
      r * s ^ (r - 1) * (t ^ 2 * u + t ^ 3 * v)) =O[𝓝 0] (fun t => t ^ 4) := by
  let z : ℝ → ℝ := fun t => t ^ 2 * (u / s) + t ^ 3 * (v / s)
  have hz : Tendsto z (𝓝 0) (𝓝 0) := by
    have hc : Continuous z := by unfold z; fun_prop
    simpa [z] using hc.tendsto 0
  have hb : (fun t => (1 + z t) ^ r - 1 - r * z t) =O[𝓝 0] (fun t => t ^ 4) := by
    have H := ((one_add_rpow_linear_remainder r).comp_tendsto hz).trans
      ((quadratic_cubic_isBigO (u / s) (v / s)).pow 2)
    convert H using 1
    · rfl
    · ext t
      ring
  have he : (fun t : ℝ => (s + t ^ 2 * u + t ^ 3 * v) ^ r - s ^ r -
      r * s ^ (r - 1) * (t ^ 2 * u + t ^ 3 * v)) =ᶠ[𝓝 0]
      (fun t => s ^ r * ((1 + z t) ^ r - 1 - r * z t)) := by
    have hp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + z t := by
      have ht : Tendsto (fun t => 1 + z t) (𝓝 0) (𝓝 1) := by simpa using tendsto_const_nhds.add hz
      exact ht.eventually (eventually_gt_nhds zero_lt_one)
    filter_upwards [hp] with t ht
    have heq : s + t ^ 2 * u + t ^ 3 * v = s * (1 + z t) := by
      unfold z
      field_simp
      ring
    rw [heq, Real.mul_rpow hs.le ht.le, Real.rpow_sub_one hs.ne']
    unfold z
    field_simp
  exact (hb.const_mul_left (s ^ r)).congr' he.symm (Filter.EventuallyEq.refl _ _)

/-- Polynomially bounded coefficients preserve a fourth-order error. -/
private theorem continuous_mul_fourth (f : ℝ → ℝ) (hf : ContinuousAt f 0) :
    (fun t : ℝ => t ^ 4 * f t) =O[𝓝 0] (fun t => t ^ 4) := by
  simpa only [mul_one] using
    (isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).mul (hf.tendsto.isBigO_one (F := ℝ))

/-- One edge of the actual midpoint functional has the expected second- and
third-order coefficients on a quadratic-cubic mass path. -/
theorem massEdge_quadratic_cubic_remainder (q a b u v w z : ℝ) (hs : 0 < a + b) :
    (fun t : ℝ =>
      ((a + t ^ 2 * u + t ^ 3 * w) - (b + t ^ 2 * v + t ^ 3 * z)) *
        ((a + t ^ 2 * u + t ^ 3 * w) + (b + t ^ 2 * v + t ^ 3 * z)) ^ (q - 1) -
      (a - b) * (a + b) ^ (q - 1) -
      t ^ 2 * (u * massGradientScalar q a b - v * massGradientScalar q b a) -
      t ^ 3 * (w * massGradientScalar q a b - z * massGradientScalar q b a))
        =O[𝓝 0] (fun t => t ^ 4) := by
  let R : ℝ → ℝ := fun t => (a + b + t ^ 2 * (u + v) + t ^ 3 * (w + z)) ^ (q - 1) -
    (a + b) ^ (q - 1) - (q - 1) * (a + b) ^ (q - 2) * (t ^ 2 * (u + v) + t ^ 3 * (w + z))
  have hR : R =O[𝓝 0] (fun t : ℝ => t ^ 4) := by
    simpa only [R, show q - 1 - 1 = q - 2 by ring] using
      rpow_quadratic_cubic_remainder (q - 1) (a + b) (u + v) (w + z) hs
  have hd : Tendsto (fun t : ℝ => a - b + t ^ 2 * (u - v) + t ^ 3 * (w - z))
      (𝓝 0) (𝓝 (a - b)) := by
    simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), zero_pow (by omega : (3 : ℕ) ≠ 0), zero_mul, add_zero] using
      (show Continuous (fun t : ℝ => a - b + t ^ 2 * (u - v) + t ^ 3 * (w - z)) by fun_prop).tendsto 0
  have h₁ : (fun t : ℝ => (a - b + t ^ 2 * (u - v) + t ^ 3 * (w - z)) * R t) =O[𝓝 0] (fun t => t ^ 4) := by
    simpa only [one_mul] using (hd.isBigO_one (F := ℝ)).mul hR
  let P : ℝ → ℝ := fun t => (q - 1) * (a + b) ^ (q - 2) *
    ((u - v) * (u + v) + t * ((u - v) * (w + z) + (w - z) * (u + v)) + t ^ 2 * (w - z) * (w + z))
  have h₂ := continuous_mul_fourth P (by unfold P; fun_prop)
  have H := h₁.add h₂
  have hp : (a + b) ^ (q - 1) = (a + b) ^ (q - 2) * (a + b) := by
    rw [← Real.rpow_add_one hs.ne']
    congr 1
    ring
  convert H using 1
  · ext t
    unfold R P massGradientScalar
    rw [add_comm b a]
    rw [show a + t ^ 2 * u + t ^ 3 * w + (b + t ^ 2 * v + t ^ 3 * z) =
      a + b + t ^ 2 * (u + v) + t ^ 3 * (w + z) by ring, hp]
    ring

/-- The entire finite midpoint functional has the exact fourth-order remainder
for a quadratic-cubic mass path. -/
theorem finiteMass_quadratic_cubic_remainder (q : ℝ) (n : ℕ) (g u v : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hu₀ : u (-1) = 0) (hu₁ : u ((n : ℤ) + 1) = 0)
    (hv₀ : v (-1) = 0) (hv₁ : v ((n : ℤ) + 1) = 0) :
    (fun t : ℝ => finiteMassFunctional q n (fun k => g k + t ^ 2 * u k + t ^ 3 * v k) -
      finiteMassFunctional q n g - t ^ 2 * massGradientPairing q n g u -
        t ^ 3 * massGradientPairing q n g v) =O[𝓝 0] (fun t => t ^ 4) := by
  have H := Asymptotics.IsBigO.sum (s := Finset.univ)
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 2)))) =>
      massEdge_quadratic_cubic_remainder q (g ((k.val : ℤ) - 1)) (g (k.val : ℤ))
        (u ((k.val : ℤ) - 1)) (u (k.val : ℤ)) (v ((k.val : ℤ) - 1)) (v (k.val : ℤ)) (hs k))
  convert H using 1
  ext t
  rw [massGradientPairing_edges q n g u hu₀ hu₁, massGradientPairing_edges q n g v hv₀ hv₁]
  simp only [finiteMassFunctional, Finset.sum_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib]

/-- If the quadratic coefficient vanishes, the exact cubic quotient converges
to the actual cubic mass-gradient pairing. -/
theorem tendsto_finiteMass_cubic_quotient (q : ℝ) (n : ℕ) (g u v : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hu₀ : u (-1) = 0) (hu₁ : u ((n : ℤ) + 1) = 0)
    (hv₀ : v (-1) = 0) (hv₁ : v ((n : ℤ) + 1) = 0)
    (hU : massGradientPairing q n g u = 0) :
    Tendsto (fun t : ℝ => (finiteMassFunctional q n (fun k => g k + t ^ 2 * u k + t ^ 3 * v k) -
      finiteMassFunctional q n g) / t ^ 3) (𝓝[≠] 0) (𝓝 (massGradientPairing q n g v)) := by
  have hR := finiteMass_quadratic_cubic_remainder q n g u v hs hu₀ hu₁ hv₀ hv₁
  have hsmall := hR.trans_isLittleO (isLittleO_pow_pow (𝕜 := ℝ) (show 3 < 4 by omega))
  have hlim := hsmall.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have H := hlim.add_const (massGradientPairing q n g v)
  simp only [zero_add] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀ : t ≠ 0 := by simpa using ht
  rw [hU, mul_zero, sub_zero]
  field_simp
  ring

/-- A local minimum on the actual cubic splitting mass path annihilates its
cubic coefficient once its quadratic coefficient vanishes. -/
theorem cubicMassPairing_eq_zero_of_localMin (q : ℝ) (n : ℕ) (g u v : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hu₀ : u (-1) = 0) (hu₁ : u ((n : ℤ) + 1) = 0)
    (hv₀ : v (-1) = 0) (hv₁ : v ((n : ℤ) + 1) = 0)
    (hU : massGradientPairing q n g u = 0)
    (hmin : IsLocalMin (fun t : ℝ =>
      finiteMassFunctional q n (fun k => g k + t ^ 2 * u k + t ^ 3 * v k)) 0) :
    massGradientPairing q n g v = 0 := by
  apply cubic_limit_eq_zero_of_localMin hmin
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), zero_pow (by omega : (3 : ℕ) ≠ 0),
    zero_mul, add_zero] using tendsto_finiteMass_cubic_quotient q n g u v hs hu₀ hu₁ hv₀ hv₁ hU

end RenyiMonotonicity
