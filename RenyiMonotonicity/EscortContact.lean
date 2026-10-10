module

public import RenyiMonotonicity.EscortIdentities
public import RenyiMonotonicity.ContactStationarity
public import RenyiMonotonicity.ScoreSecants

/-! The complete finite escort contradiction for an actual positive Bernoulli law. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

theorem escortScore_bernoulli_eq {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) :
    escortScore n (bernoulliMass p) = bernoulliMixingScore p := by
  funext k
  exact (bernoulliMixingScore_eq_edgeRatio p hp hpHalf k).symm

/-- The actual escort score has positive second moment because its leftmost
value is minus one and its leftmost escort weight is positive. -/
theorem escortScore_second_pos {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) :
    0 < expectation (escortWeight q n (bernoulliMass p))
      (fun k => escortScore n (bernoulliMass p) k ^ 2) := by
  have hs := edgeSum_pos p hp hp₁
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (escortWeight_pos q n _ hs k).le (sq_nonneg _)
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    have hg : 0 < bernoulliMass p 0 := bernoulliMass_pos p hp hp₁ 0 (by omega) (by omega)
    have hy : escortScore n (bernoulliMass p) 0 = -1 := by
      simp [escortScore, hg.ne']
    dsimp only
    rw [hy]
    norm_num
    exact escortWeight_pos q n _ hs 0

/-- The centered integer-position variable is never constant on the complete
edge support, including the zero-background dimension. -/
theorem escortPosition_nonconstant (n : ℕ) :
    ∃ i j : Fin (n + 2), escortPosition n i ≠ escortPosition n j := by
  refine ⟨0, ⟨1, by omega⟩, ?_⟩
  simp only [escortPosition, Fin.val_zero, Nat.cast_zero, zero_sub, Nat.cast_one]
  intro he
  linarith

/-- Once the two strict curvature signs and first mass-direction stationarity
are supplied by contact analysis, the actual Bernoulli contact is impossible.
All score-grid and association hypotheses are derived internally. -/
theorem no_bernoulli_contact_of_strict_moments {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (hD : midpointFunctional q p = 0)
    (hfirst : massGradientPairing q n (bernoulliMass p) (fun k => (k : ℝ) * bernoulliMass p k) = 0)
    (hM : quadraticMassMoment q n (bernoulliMass p) < 0)
    (hC : cubicEdgeKernel q n (bernoulliMass p) < 0) : False := by
  have hp₁ : ∀ i, p i < 1 := by intro i; linarith [hpHalf i]
  have hs := edgeSum_pos p hp hp₁
  have hzero : massGradientPairing q n (bernoulliMass p) (bernoulliMass p) = 0 := by
    rw [massGradientPairing_euler q n _ (bernoulliMass_outer_left p)
      (bernoulliMass_outer_right p) hs, finiteMassFunctional_bernoulliMass, hD, mul_zero]
  have hD' : finiteMassFunctional q n (bernoulliMass p) = 0 := by
    simpa only [finiteMassFunctional_bernoulliMass] using hD
  have hmean : expectation (escortWeight q n (bernoulliMass p)) (escortScore n (bernoulliMass p)) = 0 := by
    rw [escortScore_mean q n _ hs, hD', zero_div]
  have hy : ∀ k, -1 ≤ escortScore n (bernoulliMass p) k ∧ escortScore n (bernoulliMass p) k ≤ 1 := by
    rw [escortScore_bernoulli_eq p hp hpHalf]
    intro k
    exact bernoulliMixingScore_mem_Icc p hp hpHalf k
  have hym : StrictMono (escortScore n (bernoulliMass p)) := by
    rw [escortScore_bernoulli_eq p hp hpHalf]
    exact bernoulliMixingScore_strictMono p hp hpHalf
  have hsec : IncreasingSecants (escortScore n (bernoulliMass p)) (escortPosition n) := by
    rw [escortScore_bernoulli_eq p hp hpHalf]
    exact bernoulliMixingScore_increasingSecants p hp hpHalf (((n : ℝ) + 1) / 2)
  have hstationary := escort_stationary_first q n (bernoulliMass p)
    (bernoulliMass_outer_left p) (bernoulliMass_outer_right p) hs hzero hfirst
  have hthird := escortScore_third_pos q n _ hs hD' hC
  have H := inverse_score_excludes_negative_contact
    (escortWeight q n (bernoulliMass p)) (escortScore n (bernoulliMass p)) (escortPosition n) q
    (escortWeight_pos q n _ hs) (sum_escortWeight q n _ hs) hy hym hmean
    (escortScore_second_pos q p hp hp₁) ⟨hq₀, hq₁⟩ hsec hthird (escortPosition_nonconstant n) hstationary
  rw [← escort_stationary_second q n _ (bernoulliMass_outer_left p)
    (bernoulliMass_outer_right p) hs hD' hzero hfirst] at H
  exact not_lt_of_ge (div_neg_of_neg_of_pos hM (escortPartition_pos q n _ hs)).le H

/-- The same actual-law contradiction with first moment stationarity derived
from the original coin-coordinate derivatives. -/
theorem no_bernoulli_contact_of_stationary_strict_moments {n : ℕ} (q : ℝ)
    (p : Fin (n + 1) → ℝ) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (hD : midpointFunctional q p = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) = 0)
    (hM : quadraticMassMoment q (n + 1) (bernoulliMass p) < 0)
    (hC : cubicEdgeKernel q (n + 1) (bernoulliMass p) < 0) : False :=
  no_bernoulli_contact_of_strict_moments q p hq₀ hq₁ hp hpHalf hD
    (firstMassMoment_eq_zero_of_stationary q p hp (fun i => by linarith [hpHalf i]) hD hstat) hM hC

end RenyiMonotonicity
