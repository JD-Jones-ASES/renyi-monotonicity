module

public import RenyiMonotonicity.MassGradientCalculus
public import RenyiMonotonicity.RealRootedDifferences
public import RenyiMonotonicity.SignBlocks

/-! Reflection and sign propagation for the actual finite mass gradient. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace RenyiMonotonicity

/-- Complementing every Bernoulli coin reflects its entire integer-extended mass law. -/
theorem bernoulliMass_complement {n : ℕ} (p : Fin n → ℝ) (k : ℤ) :
    bernoulliMass (fun i => 1-p i) k = bernoulliMass p ((n : ℤ)-k) := by
  induction n generalizing k with
  | zero =>
    by_cases hk : k = 0
    · subst k
      simp [bernoulliMass, bernoulliPolynomial]
    · simp only [Nat.cast_zero, zero_sub]
      by_cases h₀ : 0 ≤ k
      · have hkpos : 0 < k := lt_of_le_of_ne h₀ (Ne.symm hk)
        rw [bernoulliMass_neg _ _ (neg_neg_of_pos hkpos)]
        simp [bernoulliMass, h₀, bernoulliPolynomial, Polynomial.coeff_one, show k.toNat ≠ 0 by omega]
      · rw [bernoulliMass_neg _ _ (lt_of_not_ge h₀)]
        have hkpos : 0 < -k := by omega
        simp [bernoulliMass, bernoulliPolynomial, Polynomial.coeff_one, show (-k).toNat ≠ 0 by omega]
  | succ n ih =>
    have hp : p = Fin.cons (p 0) (Fin.tail p) := (Fin.cons_self_tail p).symm
    rw [hp]
    have he : (fun i => 1 - Fin.cons (p 0) (Fin.tail p) i) =
        Fin.cons (1-p 0) (fun i => 1-Fin.tail p i) := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rw [he, bernoulliMass_cons, bernoulliMass_cons, ih (Fin.tail p) k, ih (Fin.tail p) (k-1)]
    rw [show (n : ℤ)-(k-1)=(n+1:ℕ)-k by omega,
      show ((n+1:ℕ):ℤ)-k-1=(n:ℤ)-k by omega]
    ring

/-- Reflection reverses and negates the actual mass gradient. -/
theorem bernoulliMassGradient_complement {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (k : ℤ) :
    bernoulliMassGradient q (fun i => 1-p i) k = -bernoulliMassGradient q p ((n : ℤ)-k) := by
  simp only [bernoulliMassGradient, bernoulliMass_complement]
  rw [show (n:ℤ)-(k-1)=(n:ℤ)-k+1 by omega, show (n:ℤ)-(k+1)=(n:ℤ)-k-1 by omega]
  unfold massGradientEntry
  ring

/-- Strict log-concavity propagates an increasing step one position left. -/
lemma increase_left_of_strict_logconcave {a b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    (hlog : a*c < b^2) : a < b := by
  by_contra hab
  have hab' : b ≤ a := le_of_not_gt hab
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hbc)]

/-- Strict log-concavity propagates a decreasing step one position right. -/
lemma decrease_right_of_strict_logconcave {a b c : ℝ} (hb : 0 < b) (hab : b ≤ a)
    (hlog : a*c < b^2) : c < b := by
  exact increase_left_of_strict_logconcave hb hab (by simpa [mul_comm] using hlog)

/-- An increasing step in the actual law forces every preceding adjacent step to increase. -/
theorem bernoulliMass_increase_left {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) (hinc : bernoulliMass p k ≤ bernoulliMass p (k+1)) :
    bernoulliMass p (k-1) < bernoulliMass p k :=
  increase_left_of_strict_logconcave (bernoulliMass_pos p hp hp1 k hk0 hkn) hinc
    (bernoulliMass_strict_logconcave p hp hp1 k hk0 hkn)

/-- A decreasing step in the actual law forces the next adjacent step to decrease. -/
theorem bernoulliMass_decrease_right {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) (hdec : bernoulliMass p k ≤ bernoulliMass p (k-1)) :
    bernoulliMass p (k+1) < bernoulliMass p k :=
  decrease_right_of_strict_logconcave (bernoulliMass_pos p hp hp1 k hk0 hkn) hdec
    (bernoulliMass_strict_logconcave p hp hp1 k hk0 hkn)

/-- At a (possibly non-strict) mode, the gradient compares the two neighbouring masses. -/
theorem massGradientEntry_mode_pos_iff {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hb : 0 < b) (ha : a ∈ Icc 0 b) (hc : c ∈ Icc 0 b) :
    0 < massGradientEntry q a b c ↔ a < c := by
  exact sub_pos.trans ((massGradientScalar_strictMonoOn hq0 hq1 hb).lt_iff_lt ha hc)

/-- The central equality case is exactly equality of the two neighbours. -/
theorem massGradientEntry_mode_zero_iff {q a b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hb : 0 < b) (ha : a ∈ Icc 0 b) (hc : c ∈ Icc 0 b) :
    massGradientEntry q a b c = 0 ↔ c = a := by
  exact sub_eq_zero.trans ((massGradientScalar_strictMonoOn hq0 hq1 hb).eq_iff_eq hc ha)

/-- The first entry at a flat two-point mode is positive. -/
theorem massGradientEntry_plateau_left_pos {q a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 ≤ a) (hab : a < b) : 0 < massGradientEntry q a b b := by
  exact (massGradientEntry_mode_pos_iff hq0 hq1 (by linarith) ⟨ha,hab.le⟩ ⟨by linarith,le_rfl⟩).mpr hab

/-- The second entry at a flat two-point mode is negative. -/
theorem massGradientEntry_plateau_right_neg {q b c : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hc : 0 ≤ c) (hcb : c < b) : massGradientEntry q b b c < 0 := by
  have H := massGradientEntry_plateau_left_pos hq0 hq1 hc hcb
  unfold massGradientEntry at *
  linarith

/-- Positive first differences satisfying log-concavity cannot restart positive curvature. -/
lemma curvature_nonpos_step {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hlc : (b-a)*(d-c) ≤ (c-b)^2) (hJ : a-2*b+c ≤ 0) : b-2*c+d ≤ 0 := by
  have hr : 0 < b-a := sub_pos.mpr hab
  have ht : 0 < c-b := sub_pos.mpr hbc
  have hs : 0 < d-c := sub_pos.mpr hcd
  by_contra h
  have h' : 0 < b-2*c+d := lt_of_not_ge h
  nlinarith [mul_nonneg (show 0 ≤ b-a-(c-b) by linarith) hs.le]

/-- On consecutive increasing triples, a nonnegative actual gradient becomes strictly positive.
The only extra local premise is first-difference log-concavity. -/
theorem bernoulliMassGradient_increasing_step_of_diff_logconcave {n : ℕ} (q : ℝ)
    (p : Fin (n+1) → ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : ℤ) (hk0 : 0 ≤ k) (hkn : k ≤ n)
    (hinc : bernoulliMass p k < bernoulliMass p (k+1))
    (hnext : bernoulliMass p (k+1) ≤ bernoulliMass p (k+2))
    (hlc : (bernoulliMass p k-bernoulliMass p (k-1)) *
      (bernoulliMass p (k+2)-bernoulliMass p (k+1)) ≤
      (bernoulliMass p (k+1)-bernoulliMass p k)^2)
    (hB : 0 ≤ bernoulliMassGradient q p k) :
    0 < bernoulliMassGradient q p (k+1) := by
  have ha := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) (k-1)
  have hb := bernoulliMass_pos p hp hp1 k hk0 (by omega)
  have hab := bernoulliMass_increase_left p hp hp1 k hk0 (by omega) hinc.le
  have ht : 0 ≤ bernoulliMass p (k+1) := (bernoulliMass_pos p hp hp1 (k+1) (by omega) (by omega)).le
  change 0 < massGradientEntry q (bernoulliMass p (k+1-1)) (bernoulliMass p (k+1)) (bernoulliMass p (k+1+1))
  rw [show k+1-1=k by omega, show k+1+1=k+2 by omega]
  rcases lt_or_eq_of_le hnext with hnext | hnext
  · by_cases hJ' : 0 < bernoulliMass p k - 2*bernoulliMass p (k+1) + bernoulliMass p (k+2)
    · have hJ : 0 < bernoulliMass p (k-1) - 2*bernoulliMass p k + bernoulliMass p (k+1) := by
        by_contra h
        exact not_le_of_gt hJ' (curvature_nonpos_step hab hinc hnext hlc (le_of_not_gt h))
      have hg : 0 ≤ bernoulliGradientThresholdGap q p k := by
        by_contra h
        have hneg := (massGradientEntry_neg_iff hq0 hq1 ha hab hinc hJ).mpr
          (sub_neg.mp (lt_of_not_ge h))
        exact not_lt_of_ge hB hneg
      have hgap := bernoulliGradientThresholdGap_step_lt q p hq0 hq1 hp hp1 k hk0 hkn hab hinc hJ hJ'
      have hg' : 0 < bernoulliGradientThresholdGap q p (k+1) := lt_of_le_of_lt hg hgap
      unfold bernoulliGradientThresholdGap at hg'
      rw [show k+1-1=k by omega, show k+1+1=k+2 by omega] at hg'
      exact (massGradientEntry_pos_iff hq0 hq1 hb.le hinc hnext hJ').mpr (sub_pos.mp hg')
    · exact massGradientEntry_pos_of_curvature_nonpos hq0 hq1 hb.le hinc hnext.le (le_of_not_gt hJ')
  · rw [← hnext]
    exact massGradientEntry_plateau_left_pos hq0 hq1 hb.le hinc

/-- The actual Bernoulli product supplies the first-difference premise, so sign
propagation on the increasing side needs only the parameters and adjacent order. -/
theorem bernoulliMassGradient_increasing_step {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (k : ℤ) (hk0 : 0 ≤ k) (hkn : k < n)
    (hinc : bernoulliMass p k < bernoulliMass p (k+1))
    (hnext : bernoulliMass p (k+1) ≤ bernoulliMass p (k+2))
    (hB : 0 ≤ bernoulliMassGradient q p k) : 0 < bernoulliMassGradient q p (k+1) := by
  cases n with
  | zero => omega
  | succ n =>
    exact bernoulliMassGradient_increasing_step_of_diff_logconcave q p hq0 hq1 hp hp1 k hk0
      (by omega) hinc hnext (bernoulli_firstDifference_strict_logconcave p k hk0
        (sub_ne_zero.mpr hinc.ne')).le hB

/-- Strict log-concavity propagates the increasing side back to the zero-extension edge. -/
theorem bernoulliMass_increase_before {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i j : ℤ)
    (hi0 : 0 ≤ i) (hij : i ≤ j) (hjn : j ≤ n)
    (hinc : bernoulliMass p j ≤ bernoulliMass p (j+1)) :
    bernoulliMass p (i-1) < bernoulliMass p i := by
  induction i, hij using Int.leInductionDown with
  | base => exact bernoulliMass_increase_left p hp hp1 j hi0 hjn hinc
  | pred k hkj ih =>
    have H := ih (by omega)
    exact bernoulliMass_increase_left p hp hp1 (k-1) hi0 (by omega)
      (by simpa only [sub_add_cancel] using H.le)

/-- A nonnegative gradient on the increasing side forces every later increasing-side
entry to be strictly positive, including the first entry of a plateau. -/
theorem bernoulliMassGradient_increasing_before {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (i j : ℤ) (hi0 : 0 ≤ i) (hij : i < j) (hjn : j ≤ n)
    (hinc : bernoulliMass p j ≤ bernoulliMass p (j+1))
    (hB : 0 ≤ bernoulliMassGradient q p i) : 0 < bernoulliMassGradient q p j := by
  have hstep (k : ℤ) (hik : i ≤ k) (hkj : k < j) (hk : 0 ≤ bernoulliMassGradient q p k) :
      0 < bernoulliMassGradient q p (k+1) := by
    have ha := bernoulliMass_increase_before p hp hp1 (k+1) j (by omega) (by omega) hjn hinc
    have hb : bernoulliMass p (k+1) ≤ bernoulliMass p (k+2) := by
      by_cases he : k+1=j
      · simpa only [← he, show k+1+1=k+2 by omega] using hinc
      · have H := bernoulliMass_increase_before p hp hp1 (k+2) j (by omega) (by omega) hjn hinc
        simpa only [show k+2-1=k+1 by omega] using H.le
    apply bernoulliMassGradient_increasing_step q p hq0 hq1 hp hp1 k (by omega) (by omega) _ hb hk
    simpa only [add_sub_cancel_right] using ha
  have hprop (k : ℤ) (hik : i ≤ k) : k ≤ j → 0 ≤ bernoulliMassGradient q p k := by
    induction k, hik using Int.leInduction with
    | base => intro _; exact hB
    | succ k hik ih =>
      intro hkj
      exact (hstep k hik (by omega) (ih (by omega))).le
  have H := hstep (j-1) (by omega) (by omega) (hprop (j-1) (by omega) (by omega))
  simpa only [sub_add_cancel] using H

/-- Reflection gives the same negative-to-positive orientation on the decreasing side. -/
theorem bernoulliMassGradient_decreasing_after {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (i j : ℤ) (hi0 : 0 ≤ i) (hij : i < j) (hjn : j ≤ n)
    (hdec : bernoulliMass p i ≤ bernoulliMass p (i-1))
    (hB : 0 ≤ bernoulliMassGradient q p i) : 0 < bernoulliMassGradient q p j := by
  by_contra h
  have H := bernoulliMassGradient_increasing_before q (fun k => 1-p k) hq0 hq1
    (fun k => by linarith [hp1 k]) (fun k => by linarith [hp k])
    ((n:ℤ)-j) ((n:ℤ)-i) (by omega) (by omega) (by omega)
  have hinc : bernoulliMass (fun k => 1-p k) ((n:ℤ)-i) ≤
      bernoulliMass (fun k => 1-p k) ((n:ℤ)-i+1) := by
    simpa only [bernoulliMass_complement, show (n:ℤ)-((n:ℤ)-i)=i by omega,
      show (n:ℤ)-((n:ℤ)-i+1)=i-1 by omega] using hdec
  have hB' : 0 ≤ bernoulliMassGradient q (fun k => 1-p k) ((n:ℤ)-j) := by
    rw [bernoulliMassGradient_complement, show (n:ℤ)-((n:ℤ)-j)=j by omega]
    linarith
  specialize H hinc hB'
  rw [bernoulliMassGradient_complement, show (n:ℤ)-((n:ℤ)-i)=i by omega] at H
  linarith

/-- Every positive finite Bernoulli law has a mode, with its two zero-extended neighbours below it. -/
theorem bernoulliMass_exists_mode {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    ∃ m : Fin (n+1), bernoulliMass p ((m.val:ℤ)-1) ≤ bernoulliMass p m.val ∧
      bernoulliMass p ((m.val:ℤ)+1) ≤ bernoulliMass p m.val := by
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin (n+1) => bernoulliMass p i.val) Finset.univ_nonempty
  refine ⟨m, ?_, ?_⟩
  · by_cases h : m.val = 0
    · simpa [h] using (bernoulliMass_pos p hp hp1 0 (by omega) (by omega)).le
    · have H := hm ⟨m.val-1, by omega⟩ (Finset.mem_univ _)
      simpa only [show ((m.val-1:ℕ):ℤ)=(m.val:ℤ)-1 by omega] using H
  · by_cases h : m.val = n
    · simpa [h] using (bernoulliMass_pos p hp hp1 n (by omega) (by omega)).le
    · have H := hm ⟨m.val+1, by omega⟩ (Finset.mem_univ _)
      simpa only [Nat.cast_add, Nat.cast_one] using H

/-- Before a mode every step is increasing, with equality possible only at the mode edge. -/
theorem bernoulliMass_before_mode {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (m i : ℤ)
    (hi0 : 0 ≤ i) (him : i < m) (hmn : m ≤ n)
    (hm : bernoulliMass p (m-1) ≤ bernoulliMass p m) :
    bernoulliMass p i ≤ bernoulliMass p (i+1) := by
  by_cases he : i+1=m
  · simpa only [← he, add_sub_cancel_right] using hm
  · have H := bernoulliMass_increase_before p hp hp1 (i+1) (m-1) (by omega) (by omega) (by omega)
      (by simpa only [sub_add_cancel] using hm)
    simpa only [add_sub_cancel_right] using H.le

/-- After a mode every step is decreasing, with equality possible only at the mode edge. -/
theorem bernoulliMass_after_mode {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (m i : ℤ)
    (hm0 : 0 ≤ m) (hmi : m < i) (hin : i ≤ n)
    (hm : bernoulliMass p (m+1) ≤ bernoulliMass p m) :
    bernoulliMass p i ≤ bernoulliMass p (i-1) := by
  have H := bernoulliMass_before_mode (fun k => 1-p k)
    (fun k => by linarith [hp1 k]) (fun k => by linarith [hp k]) ((n:ℤ)-m) ((n:ℤ)-i)
    (by omega) (by omega) (by omega)
  have hm' : bernoulliMass (fun k => 1-p k) ((n:ℤ)-m-1) ≤
      bernoulliMass (fun k => 1-p k) ((n:ℤ)-m) := by
    simpa only [bernoulliMass_complement, show (n:ℤ)-((n:ℤ)-m-1)=m+1 by omega,
      show (n:ℤ)-((n:ℤ)-m)=m by omega] using hm
  specialize H hm'
  simpa only [bernoulliMass_complement, show (n:ℤ)-((n:ℤ)-i)=i by omega,
    show (n:ℤ)-((n:ℤ)-i+1)=i-1 by omega] using H

/-- The actual gradient has the four oriented sign blocks `−,+,−,+` for every positive
Bernoulli product and every order strictly between zero and one. Empty blocks and zeros
are allowed, and no half-cube restriction is required. -/
theorem bernoulliMassGradient_fourSignBlocks {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    FourSignBlocks (fun i : Fin (n+1) => bernoulliMassGradient q p i.val) := by
  obtain ⟨m, hmleft, hmright⟩ := bernoulliMass_exists_mode p hp hp1
  have hleft (i j : Fin (n+1)) (hij : i.val < j.val) (hjm : j.val < m.val)
      (hi : 0 < bernoulliMassGradient q p i.val) : 0 ≤ bernoulliMassGradient q p j.val := by
    exact (bernoulliMassGradient_increasing_before q p hq0 hq1 hp hp1 i.val j.val
      (by omega) (by omega) (by omega) (bernoulliMass_before_mode p hp hp1 m.val j.val
        (by omega) (by omega) (by omega) hmleft) hi.le).le
  have hright (i j : Fin (n+1)) (hmi : m.val < i.val) (hij : i.val < j.val)
      (hi : 0 < bernoulliMassGradient q p i.val) : 0 ≤ bernoulliMassGradient q p j.val := by
    exact (bernoulliMassGradient_decreasing_after q p hq0 hq1 hp hp1 i.val j.val
      (by omega) (by omega) (by omega) (bernoulliMass_after_mode p hp hp1 m.val i.val
        (by omega) (by omega) (by omega) hmright) hi.le).le
  by_cases hm : 0 ≤ bernoulliMassGradient q p m.val
  · apply fourSignBlocks_of_split _ (m.val+1) (by omega)
    · intro i j hij hj hi
      by_cases he : j = m
      · simpa only [he] using hm
      · exact hleft i j hij (by have := Fin.val_ne_of_ne he; omega) hi
    · intro i j hi hij hpos
      exact hright i j (by omega) hij hpos
  · apply fourSignBlocks_of_split _ m.val (by omega)
    · exact hleft
    · intro i j hi hij hpos
      by_cases he : i = m
      · subst i
        exact False.elim (hm hpos.le)
      · exact hright i j (by have := Fin.val_ne_of_ne he; omega) hij hpos

/-- The actual finite mass-gradient list has at most three sign changes after deleting zeros. -/
theorem bernoulliMassGradient_signVariations_le_three {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    (List.ofFn (fun i : Fin (n+1) => bernoulliMassGradient q p i.val)).signVariations ≤ 3 :=
  (bernoulliMassGradient_fourSignBlocks q p hq0 hq1 hp hp1).signVariations_le_three

end RenyiMonotonicity
