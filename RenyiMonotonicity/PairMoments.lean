module
public import Mathlib

/-! Independent-copy polynomial identities for the inverse-score inequality. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

def expectation {n : ℕ} (μ z : Fin n → ℝ) : ℝ := ∑ i, μ i * z i

def doubleExpectation {n : ℕ} (μ : Fin n → ℝ) (F : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, μ i * μ j * F i j

theorem doubleExpectation_add {n : ℕ} (μ : Fin n → ℝ)
    (F G : Fin n → Fin n → ℝ) :
    doubleExpectation μ (fun i j => F i j + G i j) =
      doubleExpectation μ F + doubleExpectation μ G := by
  simp [doubleExpectation, mul_add, Finset.sum_add_distrib]

theorem doubleExpectation_sub {n : ℕ} (μ : Fin n → ℝ)
    (F G : Fin n → Fin n → ℝ) :
    doubleExpectation μ (fun i j => F i j - G i j) =
      doubleExpectation μ F - doubleExpectation μ G := by
  simp [doubleExpectation, mul_sub, Finset.sum_sub_distrib]

theorem doubleExpectation_smul {n : ℕ} (μ : Fin n → ℝ)
    (c : ℝ) (F : Fin n → Fin n → ℝ) :
    doubleExpectation μ (fun i j => c * F i j) = c * doubleExpectation μ F := by
  simp only [doubleExpectation]
  simp_rw [show ∀ i j, μ i * μ j * (c * F i j) = c * (μ i * μ j * F i j) by
    intros; ring]
  simp_rw [← Finset.mul_sum]

theorem doubleExpectation_product {n : ℕ} (μ f g : Fin n → ℝ) :
    doubleExpectation μ (fun i j => f i * g j) = expectation μ f * expectation μ g := by
  simp only [doubleExpectation, expectation, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem doubleExpectation_left {n : ℕ} (μ f : Fin n → ℝ)
    (hμ : ∑ i, μ i = 1) : doubleExpectation μ (fun i _ => f i) = expectation μ f := by
  have h := doubleExpectation_product μ f (fun _ => 1)
  simpa [expectation, hμ] using h

theorem doubleExpectation_right {n : ℕ} (μ f : Fin n → ℝ)
    (hμ : ∑ i, μ i = 1) : doubleExpectation μ (fun _ j => f j) = expectation μ f := by
  have h := doubleExpectation_product μ (fun _ => 1) f
  simpa [expectation, hμ] using h

/-- Twice the unordered-pair kernel mass, at zero node mean. -/
theorem pair_mass_identity {n : ℕ} (μ y : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) :
    doubleExpectation μ (fun i j => (y j - y i)^2 * (1 - α * y i * y j)) =
      2 * (expectation μ (fun i => y i ^ 2)) *
        (1 + α * expectation μ (fun i => y i ^ 2)) := by
  have expand : ∀ i j, (y j - y i)^2 * (1 - α * y i * y j) =
      y i^2 + y j^2 - 2 * (y i * y j) -
        α * (y i^3 * y j) - α * (y i * y j^3) +
        (2 * α) * (y i^2 * y j^2) := by intros; ring
  simp_rw [expand]
  simp only [doubleExpectation_add, doubleExpectation_sub, doubleExpectation_smul,
    doubleExpectation_product, doubleExpectation_left μ _ hμ,
    doubleExpectation_right μ _ hμ, hy]
  ring

/-- Twice the unordered-pair first center moment, at zero node mean. -/
theorem pair_center_identity {n : ℕ} (μ y : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) :
    doubleExpectation μ (fun i j =>
      (y i + y j) * (y j - y i)^2 * (1 - α * y i * y j)) =
      2 * (1 + α * expectation μ (fun i => y i^2)) *
        expectation μ (fun i => y i^3) := by
  have expand : ∀ i j,
      (y i + y j) * (y j - y i)^2 * (1 - α * y i * y j) =
      y i^3 + y j^3 - (y i^2 * y j) - (y i * y j^2) -
        α * (y i^4 * y j) - α * (y i * y j^4) +
        α * (y i^3 * y j^2) + α * (y i^2 * y j^3) := by intros; ring
  simp_rw [expand]
  simp only [doubleExpectation_add, doubleExpectation_sub, doubleExpectation_smul,
    doubleExpectation_product, doubleExpectation_left μ _ hμ,
    doubleExpectation_right μ _ hμ, hy]
  ring

/-- Twice the unordered-pair squared-slope moment, without any division. -/
theorem pair_square_identity {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) :
    doubleExpectation μ (fun i j =>
      (x j - x i)^2 * (1 - α * y i * y j)) =
      2 * (expectation μ (fun i => x i^2) - (expectation μ x)^2 +
        α * (expectation μ (fun i => y i * x i))^2) := by
  have expand : ∀ i j,
      (x j - x i)^2 * (1 - α * y i * y j) =
      x i^2 + x j^2 - 2 * (x i * x j) -
        α * ((y i * x i^2) * y j) - α * (y i * (y j * x j^2)) +
        (2 * α) * ((y i * x i) * (y j * x j)) := by intros; ring
  simp_rw [expand]
  simp only [doubleExpectation_add, doubleExpectation_sub, doubleExpectation_smul,
    doubleExpectation_product, doubleExpectation_left μ _ hμ,
    doubleExpectation_right μ _ hμ, hy]
  ring

/-- Twice the unordered-pair center times squared-slope moment. -/
theorem pair_center_square_identity {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) :
    doubleExpectation μ (fun i j =>
      (y i + y j) * (x j - x i)^2 * (1 - α * y i * y j)) =
      2 * ((1 - α * expectation μ (fun i => y i^2)) *
        expectation μ (fun i => y i * x i^2) -
        2 * expectation μ (fun i => y i * x i) *
          expectation μ (fun i => x i * (1 - α * y i^2))) := by
  have expand : ∀ i j,
      (y i + y j) * (x j - x i)^2 * (1 - α * y i * y j) =
      y i * x i^2 + y j * x j^2 + (y i * x j^2) + (x i^2 * y j) -
        2 * ((y i * x i) * x j) - 2 * (x i * (y j * x j)) -
        α * ((y i^2 * x i^2) * y j) - α * (y i * (y j^2 * x j^2)) -
        α * (y i^2 * (y j * x j^2)) - α * ((y i * x i^2) * y j^2) +
        (2 * α) * ((y i^2 * x i) * (y j * x j)) +
        (2 * α) * ((y i * x i) * (y j^2 * x j)) := by intros; ring
  simp_rw [expand]
  simp only [doubleExpectation_add, doubleExpectation_sub, doubleExpectation_smul,
    doubleExpectation_product, doubleExpectation_left μ _ hμ,
    doubleExpectation_right μ _ hμ, hy]
  have hv : expectation μ (fun i => x i * (1 - α * y i^2)) =
      expectation μ x - α * expectation μ (fun i => y i^2 * x i) := by
    simp only [expectation, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hv]
  ring

end RenyiMonotonicity
