module

public import RenyiMonotonicity.ContactCurvature
public import RenyiMonotonicity.ContactContradiction

/-! Exact finite escort identities on the complete edge support. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

/-- The positive edge-power normalizer. -/
def escortPartition (q : ℝ) (n : ℕ) (g : ℤ → ℝ) : ℝ :=
  ∑ k : Fin (n + 2), (g ((k.val : ℤ) - 1) + g (k.val : ℤ)) ^ q

def escortWeight (q : ℝ) (n : ℕ) (g : ℤ → ℝ) (k : Fin (n + 2)) : ℝ :=
  (g ((k.val : ℤ) - 1) + g (k.val : ℤ)) ^ q / escortPartition q n g

def escortScore (n : ℕ) (g : ℤ → ℝ) (k : Fin (n + 2)) : ℝ :=
  (g ((k.val : ℤ) - 1) - g (k.val : ℤ)) /
    (g ((k.val : ℤ) - 1) + g (k.val : ℤ))

def escortPosition (n : ℕ) (k : Fin (n + 2)) : ℝ :=
  (k.val : ℝ) - ((n : ℝ) + 1) / 2

/-- Scalar first centered mass-direction identity, including individual zero masses. -/
theorem massEdge_first_escort (q a b x : ℝ) (hs : 0 < a + b) :
    ((x - 1 / 2) * a) * massGradientScalar q a b -
      ((x + 1 / 2) * b) * massGradientScalar q b a =
    (a + b) ^ q * (q * x * ((a - b) / (a + b)) -
      (1 - (1 - q) * ((a - b) / (a + b)) ^ 2) / 2) := by
  unfold massGradientScalar
  rw [add_comm b a, Real.rpow_sub hs, Real.rpow_two]
  field_simp
  ring

/-- Scalar second centered mass-direction identity. -/
theorem massEdge_second_escort (q a b x : ℝ) (hs : 0 < a + b) :
    ((x - 1 / 2) ^ 2 * a) * massGradientScalar q a b -
      ((x + 1 / 2) ^ 2 * b) * massGradientScalar q b a =
    (a + b) ^ q * (q * ((a - b) / (a + b)) * (x ^ 2 + 1 / 4) -
      x * (1 - (1 - q) * ((a - b) / (a + b)) ^ 2)) := by
  unfold massGradientScalar
  rw [add_comm b a, Real.rpow_sub hs, Real.rpow_two]
  field_simp
  ring

/-- The cubic edge kernel is exactly the score's first-minus-third moment. -/
theorem massEdge_cubic_escort (q a b : ℝ) (hs : 0 < a + b) :
    (a - b) * (a + b) ^ (q - 3) * a * b =
      (a + b) ^ q / 4 * (((a - b) / (a + b)) - ((a - b) / (a + b)) ^ 3) := by
  rw [Real.rpow_sub hs, Real.rpow_ofNat]
  field_simp
  ring

theorem escortPartition_pos (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    0 < escortPartition q n g := by
  apply Finset.sum_pos
  · intro k _
    exact Real.rpow_pos_of_pos (hs k) q
  · exact Finset.univ_nonempty

theorem escortWeight_pos (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (k : Fin (n + 2)) : 0 < escortWeight q n g k :=
  div_pos (Real.rpow_pos_of_pos (hs k) q) (escortPartition_pos q n g hs)

theorem sum_escortWeight (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    ∑ k, escortWeight q n g k = 1 := by
  unfold escortWeight
  rw [← Finset.sum_div, ← escortPartition, div_self (escortPartition_pos q n g hs).ne']

/-- Clearing the positive partition function in any escort expectation. -/
theorem escortPartition_mul_expectation (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (f : Fin (n + 2) → ℝ) :
    escortPartition q n g * expectation (escortWeight q n g) f =
      ∑ k : Fin (n + 2), (g ((k.val : ℤ) - 1) + g (k.val : ℤ)) ^ q * f k := by
  unfold expectation escortWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [(escortPartition_pos q n g hs).ne']

/-- The escort score mean is exactly the normalized midpoint functional. -/
theorem escortScore_mean (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    expectation (escortWeight q n g) (escortScore n g) =
      finiteMassFunctional q n g / escortPartition q n g := by
  apply (eq_div_iff (escortPartition_pos q n g hs).ne').mpr
  rw [mul_comm, escortPartition_mul_expectation q n g hs]
  apply Finset.sum_congr rfl
  intro k _
  unfold escortScore
  rw [Real.rpow_sub (hs k), Real.rpow_one]
  ring

/-- Exact cubic moment relation on the entire edge support. -/
theorem cubicEdgeKernel_escort (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    cubicEdgeKernel q n g / escortPartition q n g =
      (expectation (escortWeight q n g) (escortScore n g) -
        expectation (escortWeight q n g) (fun k => escortScore n g k ^ 3)) / 4 := by
  apply (div_eq_iff (escortPartition_pos q n g hs).ne').mpr
  have h₁ := escortPartition_mul_expectation q n g hs (escortScore n g)
  have h₃ := escortPartition_mul_expectation q n g hs (fun k => escortScore n g k ^ 3)
  have he : cubicEdgeKernel q n g =
      ((∑ k : Fin (n + 2), (g ((k.val : ℤ) - 1) + g (k.val : ℤ)) ^ q * escortScore n g k) -
       (∑ k : Fin (n + 2), (g ((k.val : ℤ) - 1) + g (k.val : ℤ)) ^ q * escortScore n g k ^ 3)) / 4 := by
    unfold cubicEdgeKernel
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [massEdge_cubic_escort q _ _ (hs k)]
    unfold escortScore
    ring
  rw [he, ← h₁, ← h₃]
  ring

/-- The cubic contact sign is transported without losing strictness. -/
theorem escortScore_third_pos (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hD : finiteMassFunctional q n g = 0) (hC : cubicEdgeKernel q n g < 0) :
    0 < expectation (escortWeight q n g) (fun k => escortScore n g k ^ 3) := by
  have he := cubicEdgeKernel_escort q n g hs
  rw [escortScore_mean q n g hs, hD, zero_div, zero_sub] at he
  have hh := div_neg_of_neg_of_pos hC (escortPartition_pos q n g hs)
  rw [he] at hh
  linarith

/-- Centering a weighted mass direction uses only linearity of the actual gradient. -/
theorem massGradientPairing_centered_first (q : ℝ) (n : ℕ) (g : ℤ → ℝ) :
    massGradientPairing q n g (fun k => ((k : ℝ) - (n : ℝ) / 2) * g k) =
      massGradientPairing q n g (fun k => (k : ℝ) * g k) -
        (n : ℝ) / 2 * massGradientPairing q n g g := by
  unfold massGradientPairing
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Centering the quadratic direction removes precisely its lower moments. -/
theorem massGradientPairing_centered_second (q : ℝ) (n : ℕ) (g : ℤ → ℝ) :
    massGradientPairing q n g (fun k => ((k : ℝ) - (n : ℝ) / 2) ^ 2 * g k) =
      quadraticMassMoment q n g - (n : ℝ) * massGradientPairing q n g (fun k => (k : ℝ) * g k) +
        (n : ℝ) ^ 2 / 4 * massGradientPairing q n g g := by
  unfold quadraticMassMoment massGradientPairing
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Summing the first scalar escort identity gives the actual centered pairing. -/
theorem centeredPairing_first_escort (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    massGradientPairing q n g (fun k => ((k : ℝ) - (n : ℝ) / 2) * g k) =
      escortPartition q n g * expectation (escortWeight q n g) (fun k =>
        q * escortPosition n k * escortScore n g k -
          (1 - (1 - q) * escortScore n g k ^ 2) / 2) := by
  rw [massGradientPairing_edges q n g _ (by simp [hleft]) (by simp [hright]),
    escortPartition_mul_expectation q n g hs]
  apply Finset.sum_congr rfl
  intro k _
  have hx₁ : (((k.val : ℤ) - 1 : ℤ) : ℝ) - (n : ℝ) / 2 = escortPosition n k - 1 / 2 := by
    unfold escortPosition
    push_cast
    ring
  have hx₂ : ((k.val : ℤ) : ℝ) - (n : ℝ) / 2 = escortPosition n k + 1 / 2 := by
    unfold escortPosition
    push_cast
    ring
  rw [hx₁, hx₂]
  exact massEdge_first_escort q _ _ _ (hs k)

/-- Summing the second scalar escort identity gives the actual squared pairing. -/
theorem centeredPairing_second_escort (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ)) :
    massGradientPairing q n g (fun k => ((k : ℝ) - (n : ℝ) / 2) ^ 2 * g k) =
      escortPartition q n g * expectation (escortWeight q n g) (fun k =>
        q * escortScore n g k * (escortPosition n k ^ 2 + 1 / 4) -
          escortPosition n k * (1 - (1 - q) * escortScore n g k ^ 2)) := by
  rw [massGradientPairing_edges q n g _ (by simp [hleft]) (by simp [hright]),
    escortPartition_mul_expectation q n g hs]
  apply Finset.sum_congr rfl
  intro k _
  have hx₁ : (((k.val : ℤ) - 1 : ℤ) : ℝ) - (n : ℝ) / 2 = escortPosition n k - 1 / 2 := by
    unfold escortPosition
    push_cast
    ring
  have hx₂ : ((k.val : ℤ) : ℝ) - (n : ℝ) / 2 = escortPosition n k + 1 / 2 := by
    unfold escortPosition
    push_cast
    ring
  rw [hx₁, hx₂]
  exact massEdge_second_escort q _ _ _ (hs k)

private theorem escort_expectation_first_expand {N : ℕ} (q : ℝ) (μ y x : Fin N → ℝ)
    (hμ : ∑ k, μ k = 1) :
    expectation μ (fun k => q * x k * y k - (1 - (1 - q) * y k ^ 2) / 2) =
      q * expectation μ (fun k => y k * x k) -
        (1 - (1 - q) * expectation μ (fun k => y k ^ 2)) / 2 := by
  have he (k : Fin N) : μ k * (q * x k * y k - (1 - (1 - q) * y k ^ 2) / 2) =
      q * (μ k * (y k * x k)) - μ k / 2 + (1 - q) / 2 * (μ k * y k ^ 2) := by ring
  unfold expectation
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, ← Finset.mul_sum, hμ]
  ring

private theorem escort_expectation_second_expand {N : ℕ} (q : ℝ) (μ y x : Fin N → ℝ) :
    expectation μ (fun k => q * y k * (x k ^ 2 + 1 / 4) - x k * (1 - (1 - q) * y k ^ 2)) =
      q * expectation μ (fun k => y k * x k ^ 2) + q / 4 * expectation μ y -
        expectation μ (fun k => x k * (1 - (1 - q) * y k ^ 2)) := by
  have he (k : Fin N) : μ k * (q * y k * (x k ^ 2 + 1 / 4) - x k * (1 - (1 - q) * y k ^ 2)) =
      q * (μ k * (y k * x k ^ 2)) + q / 4 * (μ k * y k) -
        μ k * (x k * (1 - (1 - q) * y k ^ 2)) := by ring
  unfold expectation
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- ES1's stationary first-moment identity is derived from actual Euler and
first mass-direction annihilations. -/
theorem escort_stationary_first (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hzero : massGradientPairing q n g g = 0)
    (hfirst : massGradientPairing q n g (fun k => (k : ℝ) * g k) = 0) :
    2 * q * expectation (escortWeight q n g) (fun k => escortScore n g k * escortPosition n k) =
      1 - (1 - q) * expectation (escortWeight q n g) (fun k => escortScore n g k ^ 2) := by
  have he := centeredPairing_first_escort q n g hleft hright hs
  rw [massGradientPairing_centered_first, hzero, hfirst, mul_zero, sub_self,
    escort_expectation_first_expand q _ _ _ (sum_escortWeight q n g hs)] at he
  have he' := (mul_eq_zero.mp he.symm).resolve_left (escortPartition_pos q n g hs).ne'
  linarith

/-- ES1's quadratic identity is exact, with all lower moments explicitly removed. -/
theorem escort_stationary_second (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1) = 0) (hright : g ((n : ℤ) + 1) = 0)
    (hs : ∀ k : Fin (n + 2), 0 < g ((k.val : ℤ) - 1) + g (k.val : ℤ))
    (hD : finiteMassFunctional q n g = 0)
    (hzero : massGradientPairing q n g g = 0)
    (hfirst : massGradientPairing q n g (fun k => (k : ℝ) * g k) = 0) :
    quadraticMassMoment q n g / escortPartition q n g =
      q * expectation (escortWeight q n g) (fun k => escortScore n g k * escortPosition n k ^ 2) -
        expectation (escortWeight q n g) (fun k => escortPosition n k *
          (1 - (1 - q) * escortScore n g k ^ 2)) := by
  have he := centeredPairing_second_escort q n g hleft hright hs
  rw [massGradientPairing_centered_second, hzero, hfirst, mul_zero, mul_zero, sub_zero, add_zero,
    escort_expectation_second_expand, escortScore_mean q n g hs, hD, zero_div, mul_zero, add_zero] at he
  apply (div_eq_iff (escortPartition_pos q n g hs).ne').mpr
  simpa only [mul_comm] using he

end RenyiMonotonicity
