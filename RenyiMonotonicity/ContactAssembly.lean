module
public import RenyiMonotonicity.ContactClassification
public import RenyiMonotonicity.ContactExclusion
public import RenyiMonotonicity.LocalizedContact

@[expose] public section
noncomputable section
open Set Polynomial
set_option maxHeartbeats 1200000
namespace RenyiMonotonicity

/-- The complete contact exclusion reduces to the one-biased-plus-fair strict
positivity lemma. This explicit intermediate dependency is removed only when
that analytic lemma is supplied. -/
theorem no_positive_contact_of_oneBiased_pos (m : ℕ) (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hfair : ∀ a : ℝ, 0 < a → a < 1/2 →
      0 < midpointFunctional q (Fin.cons a (fun _ : Fin (m+2) => (1/2:ℝ))))
    (p : Fin (m+3) → ℝ) (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1/2)
    (hbiased : ∃ i, p i < 1/2) (hD : midpointFunctional q p = 0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) : False := by
  rcases contact_parameter_factorization q p hq0 hq1 hp hpHalf hD hmin with H | H
  · obtain ⟨b,hb,hbHalf,he⟩ := H
    obtain ⟨i,hi⟩ := hbiased
    have hbH : b < 1/2 := by simpa [he] using hi
    let P := tripleCoins b b b (fun _ : Fin m => b)
    have hP : P = p := by
      rw [he]
      funext j
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) j) j
    apply no_pure_binomial_contact m q b hq0 hq1 hb hbH
    · simpa only [← hP] using hD
    · intro j
      apply midpoint_deriv_zero_of_min q P
        (fun i => by rw [hP,he]; exact ⟨hb.le,hbHalf⟩) j
        (by rw [hP,he]; exact hb) (by rw [hP,he]; exact hbH)
      simpa only [← hP] using hmin
    · simpa only [← hP] using hmin
  · obtain ⟨e,a,b,ha,hab,hbHalf,he⟩ := H
    have hD' : midpointFunctional q (Fin.cons a (fun _ : Fin (m+2) => b)) = 0 := by
      rw [← he,midpointFunctional_comp_equiv]
      exact hD
    rcases hbHalf.eq_or_lt with hb | hb
    · subst b
      exact (ne_of_gt (hfair a ha hab)) hD'
    · let P := tripleCoins b b a (fun _ : Fin m => b)
      have hpoly : bernoulliPolynomial P = bernoulliPolynomial (Fin.cons a (fun _ : Fin (m+2) => b)) := by
        simp only [P,tripleCoins,bernoulliPolynomial_cons,bernoulliPolynomial_const]
        simp only [show m+2=m+1+1 by omega,pow_succ,coinFactor]
        ring
      have heD : midpointFunctional q P = midpointFunctional q (Fin.cons a (fun _ : Fin (m+2) => b)) := by
        simp only [midpointFunctional,edgeDifference,edgeSum,bernoulliMass,hpoly]
      have hDP : midpointFunctional q P = 0 := heD.trans hD'
      have hminP : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Icc (0:ℝ) (1/2)) →
          midpointFunctional q P ≤ midpointFunctional q r := by
        intro r hr
        rw [hDP,←hD]
        exact hmin r hr
      have hpP : ∀ i, 0 < P i := by
        intro i
        exact Fin.cases (ha.trans hab) (fun j => Fin.cases (ha.trans hab)
          (fun j => Fin.cases ha (fun _ => ha.trans hab) j) j) i
      have hhP : ∀ i, P i < 1/2 := by
        intro i
        exact Fin.cases hb (fun j => Fin.cases hb (fun j => Fin.cases (hab.trans hb) (fun _ => hb) j) j) i
      exact no_singleton_binomial_contact m q b a hq0 hq1 (ha.trans hab) hb ha
        (hab.le.trans hb.le) (ne_of_gt hab) hDP
        (fun i => midpoint_deriv_zero_of_min q P (fun j => ⟨(hpP j).le,(hhP j).le⟩) i (hpP i) (hhP i) hminP) hminP

end RenyiMonotonicity
