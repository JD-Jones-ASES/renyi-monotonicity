module
public import RenyiMonotonicity.BoundaryGain
public import RenyiMonotonicity.MixingGrid

@[expose] public section
noncomputable section
open Set
open scoped BigOperators Topology

namespace RenyiMonotonicity

def normalizedMassPair (q : ℝ) (g : ℤ → ℝ) (k : ℕ) : ℝ :=
  normalizedPair q (g ((k : ℤ) - 1)) (g (k : ℤ))

theorem normalizedMidpointFunctional_eq_pairs {n : ℕ} (q : ℝ) (p : Fin n → ℝ) :
    normalizedMidpointFunctional q p = ∑ k : Fin (n + 2), normalizedMassPair q (bernoulliMass p) k.val := rfl

theorem edgeSum_ge_core_lower {m : ℕ} (p : Fin m → ℝ) (c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hcore : ∀ i : Fin (m + 1), c ≤ bernoulliMass p (i.val : ℤ)) (k : Fin (m + 2)) :
    c ≤ edgeSum p k := by
  by_cases hk : k.val < m + 1
  · have h := hcore ⟨k.val, hk⟩
    have hn := bernoulliMass_nonneg p hp hp1 ((k.val : ℤ) - 1)
    dsimp [edgeSum]
    linarith
  · have he : k.val = m + 1 := by omega
    have h := hcore (Fin.last m)
    simpa [edgeSum, he] using h

theorem old_pair_perturbation_bound {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (haHalf : ∀ i, a i ≤ 1 / 2)
    (hsmall : ∑ i, a i ≤ 1 / 4)
    (hcore : ∀ i : Fin (m + 1), c ≤ bernoulliMass p (i.val : ℤ)) (k : Fin (m + 2)) :
    |normalizedMassPair q (bernoulliMass (Fin.append p a)) k.val -
        normalizedMassPair q (bernoulliMass p) k.val| ≤
      (4 / c) * (|bernoulliMass (Fin.append p a) ((k.val : ℤ) - 1) - bernoulliMass p ((k.val : ℤ) - 1)| +
        |bernoulliMass (Fin.append p a) (k.val : ℤ) - bernoulliMass p (k.val : ℤ)|) := by
  have ha1 : ∀ i, a i ≤ 1 := fun i => by linarith [haHalf i]
  have hg0 : ∀ i, 0 ≤ Fin.append p a i := by
    intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hp j
    · simpa only [Fin.append_right] using ha j
  have hg1 : ∀ i, Fin.append p a i ≤ 1 := by
    intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hp1 j
    · simpa only [Fin.append_right] using ha1 j
  let k' : Fin (m + n + 2) := ⟨k.val, by omega⟩
  have hcoreSum := edgeSum_ge_core_lower p c hp hp1 hcore k
  have hr : 1 / 2 ≤ bernoulliMass a 0 := by
    have hh := coeff_bernoulliPolynomial_zero_ge a ha ha1
    have hz : bernoulliMass a 0 = (bernoulliPolynomial a).coeff 0 := rfl
    rw [hz]
    linarith
  have hgSum : c / 2 ≤ edgeSum (Fin.append p a) k' := by
    have h₁ := bernoulliMass_append_ge_zero_component p a hp hp1 ha ha1 ((k.val : ℤ) - 1)
    have h₂ := bernoulliMass_append_ge_zero_component p a hp hp1 ha ha1 (k.val : ℤ)
    have hh := mul_le_mul_of_nonneg_left hcoreSum (show 0 ≤ bernoulliMass a 0 by linarith)
    dsimp [edgeSum, k'] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hc.le]
  have hh := normalizedPair_lipschitz hq0 hq1 (show 0 < c / 2 by positivity)
    (bernoulliMass_nonneg p hp hp1 ((k.val : ℤ) - 1)) (bernoulliMass_nonneg p hp hp1 (k.val : ℤ))
    (bernoulliMass_nonneg (Fin.append p a) hg0 hg1 ((k.val : ℤ) - 1))
    (bernoulliMass_nonneg (Fin.append p a) hg0 hg1 (k.val : ℤ))
    (show c / 2 ≤ edgeSum p k by linarith) hgSum
    (edgeSum_le_one p hp hp1 k) (edgeSum_le_one (Fin.append p a) hg0 hg1 k')
  convert hh using 1
  congr 1
  ring

/-- All old adjacent pairs lose at most sixteen times total added mass divided
by the minimum core mass, uniformly on the complete order interval `[0,1]`. -/
theorem old_pairs_loss_bound {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (haHalf : ∀ i, a i ≤ 1 / 2)
    (hsmall : ∑ i, a i ≤ 1 / 4)
    (hcore : ∀ i : Fin (m + 1), c ≤ bernoulliMass p (i.val : ℤ)) :
    normalizedMidpointFunctional q p - (16 / c) * (∑ i, a i) ≤
      ∑ k : Fin (m + 2), normalizedMassPair q (bernoulliMass (Fin.append p a)) k.val := by
  let f := fun j : ℤ => |bernoulliMass (Fin.append p a) j - bernoulliMass p j|
  have hs := sum_old_pair_perturbations_le f (fun _ => abs_nonneg _)
    (by simp [f]) (show m + 2 ≤ m + n + 2 by omega)
  have ht := bernoulliMass_append_sum_abs_sub_le p a hp hp1 ha
    (fun i => by linarith [haHalf i]) (show m + n + 1 ≤ m + n + 2 by omega)
  have he : (∑ k : Fin (m + 2), (f ((k.val : ℤ) - 1) + f (k.val : ℤ))) ≤ 4 * ∑ i, a i := by
    dsimp [f] at hs ⊢
    linarith
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 2))))
    (fun k _ => (abs_le.mp (old_pair_perturbation_bound p a q c hq0 hq1 hc hp hp1 ha haHalf hsmall hcore k)).1)
  change (∑ k : Fin (m + 2), -((4 / c) * (f ((k.val : ℤ) - 1) + f (k.val : ℤ)))) ≤
    ∑ k : Fin (m + 2), (normalizedMassPair q (bernoulliMass (Fin.append p a)) k.val - normalizedMassPair q (bernoulliMass p) k.val) at hb
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← normalizedMidpointFunctional_eq_pairs] at hb
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 / c by positivity)
  have halg : (4 / c) * (4 * ∑ i, a i) = (16 / c) * (∑ i, a i) := by ring
  rw [halg] at hh
  linarith

theorem normalizedMidpointFunctional_append_split {m n : ℕ}
    (q : ℝ) (p : Fin m → ℝ) (a : Fin n → ℝ) :
    normalizedMidpointFunctional q (Fin.append p a) =
      (∑ k : Fin (m + 2), normalizedMassPair q (bernoulliMass (Fin.append p a)) k.val) +
      ∑ j : Fin n, normalizedMassPair q (bernoulliMass (Fin.append p a)) (m + 2 + j.val) := by
  rw [normalizedMidpointFunctional_eq_pairs]
  simp only [Fin.sum_univ_eq_sum_range]
  rw [show m + n + 2 = (m + 2) + n by omega, Finset.sum_range_add]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => normalizedMassPair q (bernoulliMass (Fin.append p a)) (m + 2 + j)) n).symm

theorem append_new_pair_nonneg {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (q : ℝ) (hq1 : q ≤ 1) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (haHalf : ∀ i, a i ≤ 1 / 2)
    (hsmall : ∑ i, a i ≤ 1 / 4) (j : ℕ) :
    0 ≤ normalizedMassPair q (bernoulliMass (Fin.append p a)) (m + 2 + j) := by
  have hg0 : ∀ i, 0 ≤ Fin.append p a i := by
    intro i; refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using hp k
    · simpa only [Fin.append_right] using ha k
  have hg1 : ∀ i, Fin.append p a i ≤ 1 := by
    intro i; refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using hp1 k
    · simpa only [Fin.append_right] using (show a k ≤ 1 by linarith [haHalf k])
  have hn (k : ℤ) := bernoulliMass_nonneg (Fin.append p a) hg0 hg1 k
  have ht := bernoulliMass_append_tail_odds p a hp hp1 ha (fun i => by linarith [haHalf i]) (j + 1)
  have ho : oddsSum a ≤ 1 / 2 := (oddsSum_bounds a ha haHalf).2.trans (by linarith)
  have hm := mul_le_mul_of_nonneg_right ho (hn ((m : ℤ) + (j + 1)))
  have hdec : bernoulliMass (Fin.append p a) ((m : ℤ) + j + 2) ≤
      bernoulliMass (Fin.append p a) ((m : ℤ) + j + 1) := by
    simp only [Nat.cast_add, Nat.cast_one] at ht
    rw [show (m : ℤ) + (j + 1) = m + j + 1 by ring] at ht hm
    rw [show (m : ℤ) + j + 1 + 1 = m + j + 2 by ring] at ht
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [hn ((m : ℤ) + j + 1), hn ((m : ℤ) + j + 2), mul_nonneg hj (hn ((m : ℤ) + j + 2))]
  have hs := bernoulliMass_adjacent_le_one (Fin.append p a) hg0 hg1 (m + j + 1)
  have hh := normalizedPair_nonneg hq1 (hn ((m : ℤ) + j + 1))
    (hn ((m : ℤ) + j + 2)) hdec (by simpa only [Nat.cast_add, Nat.cast_one, show (m : ℤ) + j + 1 + 1 = m + j + 2 by ring] using hs)
  convert hh using 1
  simp only [normalizedMassPair, Nat.cast_add, Nat.cast_ofNat]
  congr 2 <;> ring

theorem append_first_pair_gain {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (q c : ℝ) (hq1 : q ≤ 1) (hc : 0 < c)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (haHalf : ∀ i, a i ≤ 1 / 2)
    (hε : 0 < ∑ i, a i) (hsmall : ∑ i, a i ≤ 1 / 4)
    (hcore : c ≤ bernoulliMass p m) :
    (c / 4) * (∑ i, a i) * (-Real.log (∑ i, a i)) ≤
      normalizedMassPair q (bernoulliMass (Fin.append p a)) (m + 2) := by
  let g := bernoulliMass (Fin.append p a)
  have ha1 : ∀ i, a i ≤ 1 := fun i => by linarith [haHalf i]
  have hg0 : ∀ i, 0 ≤ Fin.append p a i := by
    intro i; refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using hp k
    · simpa only [Fin.append_right] using ha k
  have hg1 : ∀ i, Fin.append p a i ≤ 1 := by
    intro i; refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simpa only [Fin.append_left] using hp1 k
    · simpa only [Fin.append_right] using ha1 k
  have hn (k : ℤ) : 0 ≤ g k := bernoulliMass_nonneg _ hg0 hg1 k
  have hfirst : c * (∑ i, a i) / 2 ≤ g (m + 1) := by
    have hr := coeff_bernoulliPolynomial_one_ge a ha haHalf
    have hr' : (∑ i, a i) / 2 ≤ bernoulliMass a 1 := by
      have he : bernoulliMass a 1 = (bernoulliPolynomial a).coeff 1 := rfl
      rw [he]
      nlinarith [mul_nonneg hε.le (show 0 ≤ 1 / 2 - ∑ i, a i by linarith)]
    have hh := mul_le_mul hcore hr' (by positivity : 0 ≤ (∑ i, a i) / 2)
      (bernoulliMass_nonneg p hp hp1 m)
    have ht := bernoulliMass_append_first_new_ge p a hp hp1 ha ha1
    dsimp [g]
    nlinarith
  have hratio : g (m + 2) ≤ g (m + 1) / 2 := by
    have ht := bernoulliMass_append_tail_odds p a hp hp1 ha (fun i => by linarith [haHalf i]) 1
    have ho : oddsSum a ≤ 1 := (oddsSum_bounds a ha haHalf).2.trans (by linarith)
    have hh := mul_le_mul_of_nonneg_right ho (hn (m + 1))
    norm_num only [Nat.cast_one] at ht
    change 2 * g ((m : ℤ) + 1 + 1) ≤ oddsSum a * g (m + 1) at ht
    rw [show (m : ℤ) + 1 + 1 = m + 2 by ring] at ht
    nlinarith
  have hsum := bernoulliMass_append_first_pair_le p a hp hp1 ha ha1
  have hh := normalizedPair_first_gain hq1 hc hε (show ∑ i, a i ≤ 1 by linarith)
    (hn (m + 2)) hfirst hratio hsum
  convert hh using 1
  simp only [normalizedMassPair, Nat.cast_add, Nat.cast_ofNat]
  congr 2
  ring

/-- Uniform support-change estimate. Every assumption concerns the literal
core coefficients and added Bernoulli parameters. -/
theorem normalizedMidpointFunctional_append_lower_bound {m n : ℕ}
    (p : Fin m → ℝ) (a : Fin n → ℝ) (q c : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (haHalf : ∀ i, a i ≤ 1 / 2)
    (hε : 0 < ∑ i, a i) (hsmall : ∑ i, a i ≤ 1 / 4)
    (hcore : ∀ i : Fin (m + 1), c ≤ bernoulliMass p (i.val : ℤ)) :
    normalizedMidpointFunctional q p - (16 / c) * (∑ i, a i) +
      (c / 4) * (∑ i, a i) * (-Real.log (∑ i, a i)) ≤
        normalizedMidpointFunctional q (Fin.append p a) := by
  cases n with
  | zero => simp at hε
  | succ n =>
    rw [normalizedMidpointFunctional_append_split]
    conv_rhs => rhs; rw [Fin.sum_univ_succ]
    have hold := old_pairs_loss_bound p a q c hq0 hq1 hc hp hp1 ha haHalf hsmall hcore
    have hfirst := append_first_pair_gain p a q c hq1 hc hp hp1 ha haHalf hε hsmall (hcore (Fin.last m))
    have htail : 0 ≤ ∑ j : Fin n,
        normalizedMassPair q (bernoulliMass (Fin.append p a)) (m + 2 + j.succ.val) :=
      Finset.sum_nonneg (fun j _ => append_new_pair_nonneg p a q hq1 hp hp1 ha haHalf hsmall (j.val + 1))
    simp only [Fin.val_zero, add_zero]
    linarith

theorem normalizedMidpointFunctional_append_zero {m n : ℕ} (q : ℝ)
    (p : Fin m → ℝ) (a : Fin n → ℝ) (ha : ∀ i, a i = 0) :
    normalizedMidpointFunctional q (Fin.append p a) = normalizedMidpointFunctional q p := by
  have ha0 : a = fun _ => 0 := funext ha
  have hpoly : bernoulliPolynomial a = 1 := by rw [ha0]; exact bernoulliPolynomial_zero
  have hg (k : ℤ) : bernoulliMass (Fin.append p a) k = bernoulliMass p k := by
    simp only [bernoulliMass, bernoulliPolynomial_append, hpoly, mul_one]
  rw [normalizedMidpointFunctional_append_split]
  simp only [normalizedMassPair, hg]
  have htail : (∑ j : Fin n, normalizedPair q (bernoulliMass p ((m + 2 + j.val : ℕ) - 1))
      (bernoulliMass p (m + 2 + j.val))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have h₁ := bernoulliMass_eq_zero_above p ((m + 2 + j.val : ℕ) - 1) (by omega)
    have h₂ := bernoulliMass_eq_zero_above p (m + 2 + j.val) (by omega)
    simp only [h₁, h₂, normalizedPair, sub_self, zero_mul]
  have htail' : (∑ j : Fin n, normalizedPair q (bernoulliMass p (((m + 2 + j.val : ℕ) : ℤ) - 1))
      (bernoulliMass p (m + 2 + j.val))) = 0 := by
    exact htail
  simp only [Nat.cast_add, Nat.cast_ofNat] at htail' ⊢
  rw [htail', add_zero]
  rfl

/-- Adding a sufficiently small positive block of coins strictly increases the
normalized midpoint functional, uniformly over orders zero through one. -/
theorem normalizedMidpointFunctional_append_gt {m n : ℕ}
    (p : Fin m → ℝ) (a : Fin n → ℝ) (q c : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 < c)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (haHalf : ∀ i, a i ≤ 1 / 2)
    (hε : 0 < ∑ i, a i) (hsmall : ∑ i, a i ≤ 1 / 4)
    (hexp : ∑ i, a i ≤ Real.exp (-128 / c ^ 2))
    (hcore : ∀ i : Fin (m + 1), c ≤ bernoulliMass p (i.val : ℤ)) :
    normalizedMidpointFunctional q p < normalizedMidpointFunctional q (Fin.append p a) := by
  have h := normalizedMidpointFunctional_append_lower_bound p a q c hq0 hq1 hc hp hp1 ha haHalf hε hsmall hcore
  have hg := boundary_gain_dominates hc hε hexp
  linarith

end RenyiMonotonicity
