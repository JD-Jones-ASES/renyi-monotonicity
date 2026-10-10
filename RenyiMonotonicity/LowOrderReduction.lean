module
public import RenyiMonotonicity.ContactAssembly
public import RenyiMonotonicity.ShannonBoundary
public import RenyiMonotonicity.SmallBackgrounds

@[expose] public section
noncomputable section
open Set
namespace RenyiMonotonicity

/-- The actual low-order sign follows from the one-biased-plus-fair lemma.
This intermediate theorem records the sole remaining analytic input explicitly. -/
theorem normalizedMidpoint_nonneg_of_oneBiased_pos
    (hfair : ∀ (m : ℕ) (q a : ℝ), 2 ≤ m → 0 < q → q < 1 → 0 < a → a < 1/2 →
      0 < midpointFunctional q (Fin.cons a (fun _ : Fin m => (1/2:ℝ)))) :
    ∀ (n : ℕ) (q : ℝ), 0 < q → q < 1 → ∀ p : Fin n → ℝ,
      (∀ i, p i ∈ Icc (0:ℝ) (1/2)) → 0 ≤ normalizedMidpointFunctional q p := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a ha0 ha1 v hv
    by_contra hneg
    have hJ : normalizedMidpointFunctional a v < 0 := lt_of_not_ge hneg
    have hD : midpointFunctional a v < 0 := by
      rw [normalizedMidpointFunctional_eq a v ha1.ne (fun i => (hv i).1)
        (fun i => (hv i).2.trans (by norm_num))] at hJ
      have h := (div_lt_iff₀ (by linarith : 0 < 1-a)).mp hJ
      simpa using h
    have hn := three_le_of_midpointFunctional_neg ⟨ha0,ha1⟩ v
      (fun i => (hv i).1) (fun i => (hv i).2) hD
    obtain ⟨m,rfl⟩ : ∃ m, n=m+3 := ⟨n-3,by omega⟩
    have hIH : ∀ k < m+3, ∀ q ∈ Icc a 1, ∀ r : Fin k → ℝ,
        (∀ i, r i ∈ Icc (0:ℝ) (1/2)) → 0 ≤ normalizedMidpointFunctional q r := by
      intro k hk q hq r hr
      rcases hq.2.eq_or_lt with he | he
      · subst q
        exact normalizedMidpointFunctional_one_nonneg r hr
      · exact ih k hk q (ha0.trans_le hq.1) he r hr
    obtain ⟨q,hq,p,hp,hbiased,hzero,hmin⟩ :=
      exists_normalized_contact_of_negative (m+2) a ha0 ha1 hIH v hv hJ
    have hDzero : midpointFunctional q p = 0 := by
      rw [normalizedMidpointFunctional_eq q p hq.2.ne (fun i => (hp i).1.le)
        (fun i => (hp i).2.trans (by norm_num))] at hzero
      exact (div_eq_zero_iff).mp hzero |>.resolve_right (by linarith [hq.2])
    have hDmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Icc (0:ℝ) (1/2)) →
        midpointFunctional q p ≤ midpointFunctional q r := by
      intro r hr
      rw [hDzero]
      have hh := hmin r hr
      rw [normalizedMidpointFunctional_eq q r hq.2.ne (fun i => (hr i).1)
        (fun i => (hr i).2.trans (by norm_num))] at hh
      have H := (le_div_iff₀ (by linarith [hq.2] : 0 < 1-q)).mp hh
      simpa using H
    exact no_positive_contact_of_oneBiased_pos m q (ha0.trans hq.1) hq.2
      (fun a ha haHalf => hfair (m+2) q a (by omega) (ha0.trans hq.1) hq.2 ha haHalf)
      p (fun i => (hp i).1) (fun i => (hp i).2) hbiased hDzero hDmin

end RenyiMonotonicity
