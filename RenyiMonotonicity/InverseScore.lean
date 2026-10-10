module

public import RenyiMonotonicity.TriangularAssociation
public import RenyiMonotonicity.PairMoments

/-! The general finite inverse-score association inequality. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

/-- A sampled secant slope. Only values with `i < j` enter the theorem. -/
def secantSlope {n : ℕ} (y x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (x j - x i) / (y j - y i)

/-- The exact finite-data substitute for an increasing convex inverse score. -/
structure IncreasingSecants {n : ℕ} (y x : Fin n → ℝ) : Prop where
  nonneg : ∀ i j, i < j → 0 ≤ secantSlope y x i j
  left_mono : ∀ i i' j, i ≤ i' → i' < j → secantSlope y x i j ≤ secantSlope y x i' j
  right_mono : ∀ i j j', i < j → j ≤ j' → secantSlope y x i j ≤ secantSlope y x i j'

lemma IncreasingSecants.monotone {n : ℕ} {y x : Fin n → ℝ} (h : IncreasingSecants y x) :
    Monotone (fun p : OrderedPair n => secantSlope y x p.1.1 p.1.2) := by
  intro p q hpq
  exact (h.right_mono _ _ _ p.2 hpq.2).trans (h.left_mono _ _ _ hpq.1 q.2)

lemma IncreasingSecants.sq_monotone {n : ℕ} {y x : Fin n → ℝ} (h : IncreasingSecants y x) :
    Monotone (fun p : OrderedPair n => (secantSlope y x p.1.1 p.1.2)^2) := by
  intro p q hpq
  exact pow_le_pow_left₀ (h.nonneg _ _ p.2) (h.monotone hpq) 2

/-- Association of pair centers and squared sampled secants. -/
theorem inverseScore_pair_association {n : ℕ} {μ y x : Fin n → ℝ} {α : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1)
    (hym : StrictMono y) (hα : 0 ≤ α) (hα1 : α < 1) (hx : IncreasingSecants y x) :
    (∑ p : OrderedPair n, pairWeight μ y α p * (y p.1.1 + y p.1.2)) *
      (∑ p : OrderedPair n, pairWeight μ y α p * (secantSlope y x p.1.1 p.1.2)^2) ≤
    (∑ p : OrderedPair n, pairWeight μ y α p) *
      (∑ p : OrderedPair n, pairWeight μ y α p *
        ((y p.1.1 + y p.1.2) * (secantSlope y x p.1.1 p.1.2)^2)) := by
  have hF : Monotone (fun p : OrderedPair n => y p.1.1 + y p.1.2 + 2) := by
    intro p q hpq
    dsimp
    linarith [hym.monotone hpq.1, hym.monotone hpq.2]
  have hF0 : ∀ p : OrderedPair n, 0 ≤ y p.1.1 + y p.1.2 + 2 := by
    intro p
    linarith [(hy p.1.1).1, (hy p.1.2).1]
  have H := triangular_association_nonneg hμ hy hym hα hα1
    (fun p => y p.1.1 + y p.1.2 + 2)
    (fun p => (secantSlope y x p.1.1 p.1.2)^2)
    hF0 (fun _ => sq_nonneg _) hF hx.sq_monotone
  have hsum₁ : (∑ p : OrderedPair n, pairWeight μ y α p * (y p.1.1 + y p.1.2 + 2)) =
      (∑ p : OrderedPair n, pairWeight μ y α p * (y p.1.1 + y p.1.2)) +
        2 * (∑ p : OrderedPair n, pairWeight μ y α p) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hsum₂ : (∑ p : OrderedPair n, pairWeight μ y α p *
      ((y p.1.1 + y p.1.2 + 2) * (secantSlope y x p.1.1 p.1.2)^2)) =
      (∑ p : OrderedPair n, pairWeight μ y α p *
        ((y p.1.1 + y p.1.2) * (secantSlope y x p.1.1 p.1.2)^2)) +
      2 * (∑ p : OrderedPair n, pairWeight μ y α p * (secantSlope y x p.1.1 p.1.2)^2) := by
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsum₁, hsum₂] at H
  nlinarith only [H]

/-- Converting any symmetric zero-diagonal kernel between independent copies
and the triangular support. -/
lemma doubleExpectation_eq_twice_pairSum {n : ℕ} (μ : Fin n → ℝ)
    (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    doubleExpectation μ F =
      2 * ∑ p : OrderedPair n, μ p.1.1 * μ p.1.2 * F p.1.1 p.1.2 := by
  apply sum_symmetric_eq_twice_orderedPair
  · intro i j
    rw [hF i j]
    ring
  · intro i
    rw [hdiag]
    ring

lemma pairWeight_secant_sq {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hym : StrictMono y) (p : OrderedPair n) :
    pairWeight μ y α p * (secantSlope y x p.1.1 p.1.2)^2 =
      μ p.1.1 * μ p.1.2 * ((x p.1.2 - x p.1.1)^2 * (1 - α * y p.1.1 * y p.1.2)) := by
  have hn : y p.1.2 - y p.1.1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hym p.2))
  dsimp [pairWeight, pairKernel, secantSlope]
  field_simp

lemma pairWeight_mass {n : ℕ} (μ y : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) :
    (∑ p : OrderedPair n, pairWeight μ y α p) =
      expectation μ (fun i => y i^2) * (1 + α * expectation μ (fun i => y i^2)) := by
  have H := doubleExpectation_eq_twice_pairSum μ
    (fun i j => (y j - y i)^2 * (1 - α * y i * y j))
    (by intros; ring) (by intro i; simp)
  rw [pair_mass_identity μ y α hμ hy] at H
  change _ = 2 * ∑ p : OrderedPair n, pairWeight μ y α p at H
  linarith

lemma pairWeight_center {n : ℕ} (μ y : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) :
    (∑ p : OrderedPair n, pairWeight μ y α p * (y p.1.1 + y p.1.2)) =
      (1 + α * expectation μ (fun i => y i^2)) * expectation μ (fun i => y i^3) := by
  have H := doubleExpectation_eq_twice_pairSum μ
    (fun i j => (y i + y j) * (y j - y i)^2 * (1 - α * y i * y j))
    (by intros; ring) (by intro i; simp)
  rw [pair_center_identity μ y α hμ hy] at H
  have hs : (∑ p : OrderedPair n, μ p.1.1 * μ p.1.2 *
      ((y p.1.1 + y p.1.2) * (y p.1.2 - y p.1.1)^2 * (1 - α * y p.1.1 * y p.1.2))) =
      ∑ p : OrderedPair n, pairWeight μ y α p * (y p.1.1 + y p.1.2) := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp [pairWeight, pairKernel]
    ring
  rw [hs] at H
  linarith

lemma pairWeight_square {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) (hym : StrictMono y) :
    (∑ p : OrderedPair n, pairWeight μ y α p * (secantSlope y x p.1.1 p.1.2)^2) =
      expectation μ (fun i => x i^2) - (expectation μ x)^2 +
        α * (expectation μ (fun i => y i * x i))^2 := by
  simp_rw [pairWeight_secant_sq μ y x α hym]
  have H := doubleExpectation_eq_twice_pairSum μ
    (fun i j => (x j - x i)^2 * (1 - α * y i * y j))
    (by intros; ring) (by intro i; simp)
  rw [pair_square_identity μ y x α hμ hy] at H
  linarith

lemma pairWeight_center_square {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμ : ∑ i, μ i = 1) (hy : expectation μ y = 0) (hym : StrictMono y) :
    (∑ p : OrderedPair n, pairWeight μ y α p *
      ((y p.1.1 + y p.1.2) * (secantSlope y x p.1.1 p.1.2)^2)) =
      (1 - α * expectation μ (fun i => y i^2)) * expectation μ (fun i => y i * x i^2) -
        2 * expectation μ (fun i => y i * x i) *
          expectation μ (fun i => x i * (1 - α * y i^2)) := by
  have H := doubleExpectation_eq_twice_pairSum μ
    (fun i j => (y i + y j) * (x j - x i)^2 * (1 - α * y i * y j))
    (by intros; ring) (by intro i; simp)
  rw [pair_center_square_identity μ y x α hμ hy] at H
  have hs : (∑ p : OrderedPair n, μ p.1.1 * μ p.1.2 *
      ((y p.1.1 + y p.1.2) * (x p.1.2 - x p.1.1)^2 * (1 - α * y p.1.1 * y p.1.2))) =
      ∑ p : OrderedPair n, pairWeight μ y α p *
        ((y p.1.1 + y p.1.2) * (secantSlope y x p.1.1 p.1.2)^2) := by
    apply Finset.sum_congr rfl
    intro p _
    calc
      _ = (y p.1.1 + y p.1.2) *
          (μ p.1.1 * μ p.1.2 * ((x p.1.2 - x p.1.1)^2 * (1 - α * y p.1.1 * y p.1.2))) := by ring
      _ = _ := by rw [← pairWeight_secant_sq μ y x α hym p]; ring
  rw [hs] at H
  linarith

/-- The general finite inverse-score inequality (A1), for arbitrary positive finite laws.
Every association and moment identity is proved internally. -/
theorem inverse_score_association {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1)
    (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1) (hym : StrictMono y)
    (hymean : expectation μ y = 0) (hm2 : 0 < expectation μ (fun i => y i^2))
    (hα : 0 ≤ α) (hα1 : α < 1) (hx : IncreasingSecants y x) :
    (expectation μ (fun i => y i^3) / expectation μ (fun i => y i^2)) *
      (expectation μ (fun i => x i^2) - (expectation μ x)^2 +
        α * (expectation μ (fun i => y i * x i))^2) ≤
    (1 - α * expectation μ (fun i => y i^2)) * expectation μ (fun i => y i * x i^2) -
      2 * expectation μ (fun i => y i * x i) *
        expectation μ (fun i => x i * (1 - α * y i^2)) := by
  have H := inverseScore_pair_association (fun i => (hμpos i).le) hy hym hα hα1 hx
  rw [pairWeight_center μ y α hμsum hymean, pairWeight_square μ y x α hμsum hymean hym,
    pairWeight_mass μ y α hμsum hymean,
    pairWeight_center_square μ y x α hμsum hymean hym] at H
  have hpos : 0 < 1 + α * expectation μ (fun i => y i^2) := by positivity
  have H' := (mul_le_mul_iff_right₀ hpos).mp (show
      (1 + α * expectation μ (fun i => y i^2)) *
        (expectation μ (fun i => y i^3) *
          (expectation μ (fun i => x i^2) - (expectation μ x)^2 +
            α * (expectation μ (fun i => y i * x i))^2)) ≤
      (1 + α * expectation μ (fun i => y i^2)) *
        (expectation μ (fun i => y i^2) *
          ((1 - α * expectation μ (fun i => y i^2)) * expectation μ (fun i => y i * x i^2) -
            2 * expectation μ (fun i => y i * x i) *
              expectation μ (fun i => x i * (1 - α * y i^2)))) by nlinarith only [H])
  apply (mul_le_mul_iff_right₀ hm2).mp
  field_simp
  nlinarith only [H']

/-- Increasing convex functions have the exact sampled-slope hypotheses. -/
theorem increasingSecants_of_convexOn {n : ℕ} {y : Fin n → ℝ} {φ : ℝ → ℝ} {s : Set ℝ}
    (hy : ∀ i, y i ∈ s) (hym : StrictMono y) (hφm : MonotoneOn φ s)
    (hφc : ConvexOn ℝ s φ) : IncreasingSecants y (φ ∘ y) where
  nonneg i j hij := div_nonneg (sub_nonneg.mpr (hφm (hy i) (hy j) (hym.monotone hij.le)))
    (sub_nonneg.mpr (hym.monotone hij.le))
  left_mono i i' j hii' hi'j := by
    rcases eq_or_lt_of_le hii' with rfl | hii'
    · exact le_rfl
    · exact hφc.secant_mono_aux3 (hy i) (hy j) (hym hii') (hym hi'j)
  right_mono i j j' hij hjj' := by
    rcases eq_or_lt_of_le hjj' with rfl | hjj'
    · exact le_rfl
    · exact hφc.secant_mono_aux2 (hy i) (hy j') (hym hij) (hym hjj')

/-- Function form of the finite inverse-score inequality for any increasing convex score. -/
theorem inverse_score_association_convex {n : ℕ} (μ y : Fin n → ℝ) (φ : ℝ → ℝ) (α : ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1)
    (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1) (hym : StrictMono y)
    (hymean : expectation μ y = 0) (hm2 : 0 < expectation μ (fun i => y i^2))
    (hα : 0 ≤ α) (hα1 : α < 1)
    (hφm : MonotoneOn φ (Set.Icc (-1 : ℝ) 1))
    (hφc : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) φ) :
    (expectation μ (fun i => y i^3) / expectation μ (fun i => y i^2)) *
      (expectation μ (fun i => (φ (y i))^2) - (expectation μ (φ ∘ y))^2 +
        α * (expectation μ (fun i => y i * φ (y i)))^2) ≤
    (1 - α * expectation μ (fun i => y i^2)) * expectation μ (fun i => y i * (φ (y i))^2) -
      2 * expectation μ (fun i => y i * φ (y i)) *
        expectation μ (fun i => φ (y i) * (1 - α * y i^2)) :=
  inverse_score_association μ y (φ ∘ y) α hμpos hμsum hy hym hymean hm2 hα hα1
    (increasingSecants_of_convexOn hy hym hφm hφc)

/-- Strict variance for an arbitrary nonconstant finite law with positive atom weights. -/
theorem variance_pos_of_nonconstant {n : ℕ} (μ x : Fin n → ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1)
    (hx : ∃ i j, x i ≠ x j) :
    0 < expectation μ (fun i => x i^2) - (expectation μ x)^2 := by
  obtain ⟨i, j, hij⟩ := hx
  have hex : ∃ k, x k ≠ expectation μ x := by
    by_cases hi : x i = expectation μ x
    · exact ⟨j, fun hj => hij (hi.trans hj.symm)⟩
    · exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := hex
  have hp : 0 < ∑ i, μ i * (x i - expectation μ x)^2 := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hμpos i).le (sq_nonneg _)
    · exact ⟨k, Finset.mem_univ k, mul_pos (hμpos k) (sq_pos_of_ne_zero (sub_ne_zero.mpr hk))⟩
  have hid : (∑ i, μ i * (x i - expectation μ x)^2) =
      expectation μ (fun i => x i^2) - (expectation μ x)^2 := by
    have he : ∀ i, μ i * (x i - expectation μ x)^2 =
        μ i * x i^2 - 2 * expectation μ x * (μ i * x i) + (expectation μ x)^2 * μ i := by
      intro i; ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hμsum]
    change expectation μ (fun i => x i^2) - 2 * expectation μ x * expectation μ x +
      (expectation μ x)^2 * 1 = _
    ring
  rwa [hid] at hp

/-- A positive third node moment makes the inverse-score expression strictly positive
whenever the score is nonconstant. This is the strict sign used in the no-contact argument. -/
theorem inverse_score_strict {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1)
    (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1) (hym : StrictMono y)
    (hymean : expectation μ y = 0) (hm2 : 0 < expectation μ (fun i => y i^2))
    (hα : 0 ≤ α) (hα1 : α < 1) (hx : IncreasingSecants y x)
    (hm3 : 0 < expectation μ (fun i => y i^3)) (hxne : ∃ i j, x i ≠ x j) :
    0 < (1 - α * expectation μ (fun i => y i^2)) * expectation μ (fun i => y i * x i^2) -
      2 * expectation μ (fun i => y i * x i) *
        expectation μ (fun i => x i * (1 - α * y i^2)) := by
  apply lt_of_lt_of_le _ (inverse_score_association μ y x α hμpos hμsum hy hym hymean hm2 hα hα1 hx)
  apply mul_pos (div_pos hm3 hm2)
  exact add_pos_of_pos_of_nonneg (variance_pos_of_nonconstant μ x hμpos hμsum hxne)
    (mul_nonneg hα (sq_nonneg _))

end RenyiMonotonicity
