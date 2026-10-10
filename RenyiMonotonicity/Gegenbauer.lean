module

public import RenyiMonotonicity.PolynomialRootSigns

@[expose] public section

open Polynomial

namespace RenyiMonotonicity

/-- Positive Jacobi-recurrence coefficient for the monic Gegenbauer family. -/
noncomputable def gegenbauerRecurrenceCoefficient (a : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (n + 2 * a) / (4 * (n + a) * (n + a + 1))

/-- The monic Gegenbauer polynomials, defined by their explicit three-term
recurrence rather than assumed orthogonality or a root-location certificate. -/
noncomputable def monicGegenbauer (a : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * monicGegenbauer a (n + 1) -
      C (gegenbauerRecurrenceCoefficient a n) * monicGegenbauer a n

@[simp] theorem monicGegenbauer_zero (a : ℝ) : monicGegenbauer a 0 = 1 := rfl
@[simp] theorem monicGegenbauer_one (a : ℝ) : monicGegenbauer a 1 = X := rfl

theorem monicGegenbauer_recurrence (a : ℝ) (n : ℕ) :
    monicGegenbauer a (n + 2) = X * monicGegenbauer a (n + 1) -
      C (gegenbauerRecurrenceCoefficient a n) * monicGegenbauer a n := rfl

theorem gegenbauerRecurrenceCoefficient_pos (a : ℝ) (ha : 0 < a) (n : ℕ) :
    0 < gegenbauerRecurrenceCoefficient a n := by
  dsimp [gegenbauerRecurrenceCoefficient]
  positivity

/-- Exact degree and monicity follow from the recurrence at every index. -/
theorem monicGegenbauer_monic_degree (a : ℝ) (n : ℕ) :
    (monicGegenbauer a n).Monic ∧ (monicGegenbauer a n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
      have hm : (X * monicGegenbauer a (n + 1)).Monic := monic_X.mul ih₁.1
      have hd : (X * monicGegenbauer a (n + 1)).natDegree = n + 2 := by
        rw [natDegree_X_mul ih₁.1.ne_zero, ih₁.2]
      have hlt : (C (gegenbauerRecurrenceCoefficient a n) * monicGegenbauer a n).natDegree <
          (X * monicGegenbauer a (n + 1)).natDegree := by
        rw [hd]
        exact (natDegree_C_mul_le _ _).trans_lt (by omega)
      rw [monicGegenbauer_recurrence]
      exact ⟨hm.sub_of_left (degree_lt_degree hlt),
        (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩

/-- At `1`, consecutive endpoint values have the explicit positive ratio. -/
theorem monicGegenbauer_eval_one_step (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (monicGegenbauer a (n + 1)).eval 1 =
      ((n : ℝ) + 2 * a) / (2 * (n + a)) * (monicGegenbauer a n).eval 1 := by
  induction n with
  | zero => simp; field_simp
  | succ n ih =>
      have hna : (n : ℝ) + a ≠ 0 := by positivity
      have hna1 : (n : ℝ) + a + 1 ≠ 0 := by positivity
      have hna2 : (n : ℝ) + 2 * a ≠ 0 := by positivity
      rw [show n + 1 + 1 = n + 2 by omega, monicGegenbauer_recurrence]
      simp only [eval_sub, eval_mul, eval_X, eval_C, one_mul]
      rw [ih]
      dsimp [gegenbauerRecurrenceCoefficient]
      push_cast
      field_simp
      ring

theorem monicGegenbauer_eval_one_pos (a : ℝ) (ha : 0 < a) (n : ℕ) :
    0 < (monicGegenbauer a n).eval 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [monicGegenbauer_eval_one_step a ha n]
      exact mul_pos (by positivity) ih

/-- Parity is also an exact recurrence identity. -/
theorem monicGegenbauer_eval_neg (a : ℝ) (n : ℕ) (x : ℝ) :
    (monicGegenbauer a n).eval (-x) = (-1 : ℝ) ^ n * (monicGegenbauer a n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
      rw [monicGegenbauer_recurrence]
      simp only [eval_sub, eval_mul, eval_X, eval_C, ih₀, ih₁, pow_succ]
      ring

/-- Every pair of consecutive Gegenbauer polynomials has simple roots in
`(-1,1)` which strictly interlace. The proof constructs them by recurrence
signs and the intermediate value theorem. -/
theorem monicGegenbauer_interlacing (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ r : RealRootList (monicGegenbauer a n) n,
    ∃ s : RealRootList (monicGegenbauer a (n + 1)) (n + 1),
      (∀ j, -1 < r.root j ∧ r.root j < 1) ∧
      (∀ j, -1 < s.root j ∧ s.root j < 1) ∧
      (∀ j : Fin n, s.root j.castSucc < r.root j ∧ r.root j < s.root j.succ) := by
  induction n with
  | zero =>
      let r : RealRootList (monicGegenbauer a 0) 0 :=
        ⟨by simp, by simp, Fin.elim0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩
      let s : RealRootList (monicGegenbauer a 1) 1 :=
        ⟨by simp, by simp, fun _ => 0, by intro i j hij; have := i.isLt; have := j.isLt; omega,
          by intro j; simp⟩
      refine ⟨r, s, ?_, ?_, ?_⟩
      · intro j; exact Fin.elim0 j
      · intro j; change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1; norm_num
      · intro j; exact Fin.elim0 j
  | succ n ih =>
      obtain ⟨r, s, hr, hs, hinter⟩ := ih
      have hQ := monicGegenbauer_monic_degree a (n + 2)
      have hL : 0 < (-1 : ℝ) ^ (n + 1 + 1) * (monicGegenbauer a (n + 2)).eval (-1) := by
        rw [monicGegenbauer_eval_neg a (n + 2) 1]
        have ht : (-1 : ℝ) ^ (n + 2) * (-1 : ℝ) ^ (n + 2) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
        rw [← mul_assoc, show n + 1 + 1 = n + 2 by omega, ht, one_mul]
        exact monicGegenbauer_eval_one_pos a ha _
      have hnode (j : Fin (n + 1)) :
          0 < (-1 : ℝ) ^ (n + 1 - j.val) *
            (monicGegenbauer a (n + 2)).eval (s.root j) := by
        have hR := r.sign_between j.val (by omega) (s.root j)
          (fun l hl => (hinter l).2.trans_le (s.increasing.monotone (by
            simp only [Fin.le_iff_val_le_val, Fin.val_succ]; omega)))
          (fun l hl => (s.increasing.monotone (show j ≤ l.castSucc from hl)).trans_lt (hinter l).1)
        rw [monicGegenbauer_recurrence]
        simp only [eval_sub, eval_mul, eval_X, eval_C, s.isRoot, mul_zero, zero_sub]
        rw [show n + 1 - j.val = (n - j.val) + 1 by omega, pow_succ]
        have he : (-1 : ℝ) ^ (n - j.val) * -1 *
              -(gegenbauerRecurrenceCoefficient a n * (monicGegenbauer a n).eval (s.root j)) =
            gegenbauerRecurrenceCoefficient a n *
              ((-1 : ℝ) ^ (n - j.val) * (monicGegenbauer a n).eval (s.root j)) := by ring
        rw [he]
        exact mul_pos (gegenbauerRecurrenceCoefficient_pos a ha n) hR
      obtain ⟨t, ht, hit⟩ := s.interlacing_of_alternating_signs hQ.1 hQ.2 (-1) 1 (by norm_num)
        (fun j => (hs j).1) (fun j => (hs j).2) hL (monicGegenbauer_eval_one_pos a ha _) hnode
      exact ⟨s, t, hs, ht, hit⟩

/-- In particular, the actual finite polynomials split over the reals. -/
theorem monicGegenbauer_splits (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (monicGegenbauer a n).Splits := by
  obtain ⟨r, _⟩ := monicGegenbauer_interlacing a ha n
  exact r.splits

end RenyiMonotonicity
