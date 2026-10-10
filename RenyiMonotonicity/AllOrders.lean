module
public import RenyiMonotonicity.CMBRatio
public import RenyiMonotonicity.OneBiasedSeries
public import RenyiMonotonicity.LowOrderReduction
public import RenyiMonotonicity.OrdersOneTwo

@[expose] public section
noncomputable section
open Set
namespace RenyiMonotonicity

/-- The remaining fair-face family has strictly positive actual midpoint. -/
theorem midpointFunctional_oneBiased_pos (m : ℕ) (hm : 1 ≤ m) (q p : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hpHalf : p < 1/2) :
    0 < midpointFunctional q (oneBiasedParameters m p) :=
  midpointFunctional_oneBiased_pos_of_ratio m q p hq0 hq1 hp0 hpHalf
    (cmbMomentRatio_antitone (m+2) (by omega) q hq0 hq1)

/-- Low-order normalized midpoint nonnegativity for the actual coefficient law,
in every finite dimension and including all support-changing faces. -/
theorem normalizedMidpointFunctional_nonneg_low {n : ℕ} (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0:ℝ) (1/2)) :
    0 ≤ normalizedMidpointFunctional q p := by
  apply normalizedMidpoint_nonneg_of_oneBiased_pos ?_ n q hq0 hq1 p hp
  intro m q a hm hq0 hq1 ha0 haHalf
  exact midpointFunctional_oneBiased_pos m (by omega) q a hq0 hq1 ha0 haHalf

/-- The sign supplied to coordinate concavity has no structural or analytic
premises beyond the real order and literal coin bounds. -/
theorem midpointFunctional_nonneg_low {n : ℕ} (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0:ℝ) (1/2)) : 0 ≤ midpointFunctional q p := by
  have hh := normalizedMidpointFunctional_nonneg_low q hq0 hq1 p hp
  rw [normalizedMidpointFunctional_eq q p hq1.ne (fun i => (hp i).1)
    (fun i => (hp i).2.trans (by norm_num))] at hh
  have h := (le_div_iff₀ (by linarith : 0 < 1-q)).mp hh
  simpa using h

/-- Full closed-cube Tsallis monotonicity in every finite dimension and every
real entropy order from zero through two. -/
theorem tsallis_monotone {n : ℕ} (p r : Fin n → ℝ) (q : ℝ)
    (hq : 0 ≤ q ∧ q ≤ 2) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ r i ∧ r i ≤ 1/2) :
    tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum r) := by
  rcases eq_or_lt_of_le hq.1 with hq0 | hq0
  · subst q
    exact tsallis_zero_monotone p r (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
  · rcases lt_or_ge q 1 with hq1 | hq1
    · apply tsallis_monotone_of_midpoint q hq0 hq1.ne ?_ p r
        (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
      intro m v hv hvHalf
      exact div_nonneg (midpointFunctional_nonneg_low q hq0 hq1 v (fun i => ⟨(hv i).le,hvHalf i⟩))
        (by linarith)
    · exact tsallis_monotone_of_one_le q hq1 hq.2 p r
        (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)

/-- Full closed-cube Rényi monotonicity, with literal support entropy at zero
and Shannon entropy at one. -/
theorem renyi_monotone {n : ℕ} (p r : Fin n → ℝ) (q : ℝ)
    (hq : 0 ≤ q ∧ q ≤ 2) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ r i ∧ r i ≤ 1/2) :
    renyi q (bernoulliSum p) ≤ renyi q (bernoulliSum r) := by
  rcases eq_or_lt_of_le hq.1 with hq0 | hq0
  · subst q
    exact renyi_zero_monotone p r (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
  · apply (renyi_le_iff_tsallis_le_probability q _ _ hq0
      (bernoulliSum_nonneg p (fun i => (hp i).1) (fun i => by linarith [(hp i).2.1,(hp i).2.2]))
      (bernoulliSum_nonneg r (fun i => (hp i).1.trans (hp i).2.1) (fun i => by linarith [(hp i).2.2]))
      (sum_bernoulliSum p) (sum_bernoulliSum r)).mpr
    exact tsallis_monotone p r q hq hp

end RenyiMonotonicity
