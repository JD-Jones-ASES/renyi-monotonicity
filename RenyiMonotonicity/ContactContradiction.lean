module
public import RenyiMonotonicity.InverseScore

/-! The finite-moment contradiction at a stationary entropy contact.
The analytic construction of such a contact is a separate proof obligation. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

theorem secondMoment_le_one {n : ℕ} (μ y : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hμsum : ∑ i, μ i = 1)
    (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1) :
    expectation μ (fun i => y i^2) ≤ 1 := by
  calc
    expectation μ (fun i => y i^2) ≤ ∑ i, μ i := by
      apply Finset.sum_le_sum
      intro i _
      have hsq : y i^2 ≤ 1 := by nlinarith [(hy i).1, (hy i).2]
      nlinarith [mul_nonneg (hμ i) (sub_nonneg.mpr hsq)]
    _ = 1 := hμsum

/-- The actual inverse-score hypotheses, a positive cubic moment and the exact
stationary first-moment identity exclude a negative scaled quadratic mass moment.
This theorem is the final finite step; it does not assume or assert localization. -/
theorem inverse_score_excludes_negative_contact {n : ℕ} (μ y x : Fin n → ℝ) (q : ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1)
    (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1) (hym : StrictMono y)
    (hymean : expectation μ y = 0) (hm2 : 0 < expectation μ (fun i => y i^2))
    (hq : 0 < q ∧ q < 1) (hx : IncreasingSecants y x)
    (hm3 : 0 < expectation μ (fun i => y i^3)) (hxne : ∃ i j, x i ≠ x j)
    (hstationary : 2*q*expectation μ (fun i => y i*x i) =
      1-(1-q)*expectation μ (fun i => y i^2)) :
    0 < q*expectation μ (fun i => y i*x i^2) -
      expectation μ (fun i => x i*(1-(1-q)*y i^2)) := by
  have hbound := secondMoment_le_one μ y (fun i => (hμpos i).le) hμsum hy
  have hA : 0 < 1-(1-q)*expectation μ (fun i => y i^2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.2.le) (sub_nonneg.mpr hbound)]
  have hc : 0 < expectation μ (fun i => y i*x i) := by
    have hprod : 0 < (2*q)*expectation μ (fun i => y i*x i) := by
      rw [hstationary]
      exact hA
    exact (mul_pos_iff_of_pos_left (by linarith : 0 < 2*q)).mp hprod
  have H := inverse_score_strict μ y x (1-q) hμpos hμsum hy hym hymean hm2
    (by linarith) (by linarith) hx hm3 hxne
  rw [← hstationary] at H
  have hid : 2*q*expectation μ (fun i => y i*x i)*expectation μ (fun i => y i*x i^2) -
      2*expectation μ (fun i => y i*x i)*expectation μ (fun i => x i*(1-(1-q)*y i^2)) =
      (2*expectation μ (fun i => y i*x i)) *
        (q*expectation μ (fun i => y i*x i^2) -
          expectation μ (fun i => x i*(1-(1-q)*y i^2))) := by ring
  rw [hid] at H
  exact (mul_pos_iff_of_pos_left (by positivity)).mp H

end RenyiMonotonicity
