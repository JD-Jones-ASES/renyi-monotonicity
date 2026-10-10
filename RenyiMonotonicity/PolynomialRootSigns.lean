module

public import RenyiMonotonicity.RealRootedDifferences
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

open scoped BigOperators
open Polynomial Set

namespace RenyiMonotonicity

/-- A complete ordered list of simple real roots, recorded without any
orthogonal-polynomial or analytic certificate. -/
structure RealRootList (P : ℝ[X]) (n : ℕ) where
  monic : P.Monic
  degree : P.natDegree = n
  root : Fin n → ℝ
  increasing : StrictMono root
  isRoot : ∀ i, P.eval (root i) = 0

namespace RealRootList

variable {P : ℝ[X]} {n : ℕ}

theorem roots_eq (r : RealRootList P n) : P.roots = (Finset.univ.image r.root).val := by
  classical
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact r.isRoot i
  · rw [Finset.card_image_of_injective _ r.increasing.injective, Finset.card_univ,
      Fintype.card_fin, r.degree]
  · exact r.monic.ne_zero

theorem splits (r : RealRootList P n) : P.Splits := by
  classical
  apply Polynomial.splits_iff_card_roots.mpr
  rw [r.roots_eq]
  simp only [Finset.card_val, Finset.card_image_of_injective _ r.increasing.injective,
    Finset.card_univ, Fintype.card_fin, r.degree]

theorem eval_product (r : RealRootList P n) (x : ℝ) :
    P.eval x = ∏ i, (x - r.root i) := by
  classical
  rw [r.splits.eval_eq_prod_roots_of_monic r.monic, r.roots_eq]
  change (∏ y ∈ Finset.univ.image r.root, (x - y)) = _
  rw [Finset.prod_image]
  intro a _ b _ hab
  exact r.increasing.injective hab

/-- The sign on any interval between consecutive roots, including the two
outer intervals, follows from the complete factorization. -/
theorem sign_between (r : RealRootList P n) (i : ℕ) (hi : i ≤ n) (x : ℝ)
    (hl : ∀ j : Fin n, j.val < i → r.root j < x)
    (hr : ∀ j : Fin n, i ≤ j.val → x < r.root j) :
    0 < (-1 : ℝ) ^ (n - i) * P.eval x := by
  classical
  have hc : (Finset.univ.filter (fun j : Fin n => i ≤ j.val)).card = n - i := by
    rcases lt_or_eq_of_le hi with hi | rfl
    · have he : Finset.univ.filter (fun j : Fin n => i ≤ j.val) = Finset.Ici ⟨i, hi⟩ := by
        ext j
        simp
        rfl
      rw [he, Fin.card_Ici]
    · simp
  have hs : (∏ j : Fin n, if i ≤ j.val then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (n - i) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, hc, one_pow, mul_one]
  rw [r.eval_product, ← hs, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro j _
  by_cases hij : i ≤ j.val
  · simp only [hij, ↓reduceIte, neg_one_mul]
    linarith [hr j hij]
  · simp only [hij, ↓reduceIte, one_mul]
    exact sub_pos.mpr (hl j (by omega))

end RealRootList

/-- A strict sign change of a real polynomial gives an interior zero. -/
theorem polynomial_zero_between (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hs : P.eval a * P.eval b < 0) : ∃ x ∈ Ioo a b, P.eval x = 0 := by
  have ha : P.eval a ≠ 0 := by intro h; rw [h, zero_mul] at hs; exact lt_irrefl _ hs
  have hb : P.eval b ≠ 0 := by intro h; rw [h, mul_zero] at hs; exact lt_irrefl _ hs
  have hz : ∃ x ∈ Icc a b, P.eval x = 0 := by
    rcases mul_neg_iff.mp hs with h | h
    · exact (mem_image _ _ _).mp (intermediate_value_Icc' hab.le P.continuous.continuousOn
        ⟨h.2.le, h.1.le⟩)
    · exact (mem_image _ _ _).mp (intermediate_value_Icc hab.le P.continuous.continuousOn
        ⟨h.1.le, h.2.le⟩)
  obtain ⟨x, hx, hx0⟩ := hz
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hx0⟩
  · intro h; exact ha (h ▸ hx0)
  · intro h; exact hb (h ▸ hx0)

namespace RealRootList

noncomputable def intervalLeft {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (a : ℝ) (i : Fin (n + 1)) : ℝ :=
  if h : i.val = 0 then a else r.root ⟨i.val - 1, by omega⟩

noncomputable def intervalRight {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (b : ℝ) (i : Fin (n + 1)) : ℝ :=
  if h : i.val < n then r.root ⟨i.val, h⟩ else b

theorem interval_order {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (a b : ℝ) (hab : a < b) (ha : ∀ j, a < r.root j) (hb : ∀ j, r.root j < b)
    (i : Fin (n + 1)) : r.intervalLeft a i < r.intervalRight b i := by
  dsimp [intervalLeft, intervalRight]
  split_ifs with h₀ h₁ h₁
  · exact ha _
  · exact hab
  · exact r.increasing (by simp only [Fin.mk_lt_mk]; omega)
  · exact hb _

theorem interval_separation {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (a b : ℝ) {i j : Fin (n + 1)} (hij : i < j) :
    r.intervalRight b i ≤ r.intervalLeft a j := by
  have hi : i.val < n := by omega
  have hj : j.val ≠ 0 := by omega
  simp only [intervalLeft, intervalRight, hi, hj, ↓reduceDIte]
  exact r.increasing.monotone (by simp only [Fin.mk_le_mk]; omega)

/-- Interior sign changes in the `n+1` complementary intervals produce all
roots of a monic degree `n+1` polynomial and prove strict interlacing. -/
theorem interlacing_of_sign_changes {P Q : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (hQ : Q.Monic) (hd : Q.natDegree = n + 1) (a b : ℝ) (hab : a < b)
    (ha : ∀ j, a < r.root j) (hb : ∀ j, r.root j < b)
    (hs : ∀ i, Q.eval (r.intervalLeft a i) * Q.eval (r.intervalRight b i) < 0) :
    ∃ t : RealRootList Q (n + 1),
      (∀ j, a < t.root j ∧ t.root j < b) ∧
      (∀ j : Fin n, t.root j.castSucc < r.root j ∧ r.root j < t.root j.succ) := by
  classical
  have he (i : Fin (n + 1)) := polynomial_zero_between Q _ _
    (r.interval_order a b hab ha hb i) (hs i)
  choose x hx hz using he
  have hm : StrictMono x := by
    intro i j hij
    exact (hx i).2.trans_le ((r.interval_separation a b hij).trans (hx j).1.le)
  let t : RealRootList Q (n + 1) := ⟨hQ, hd, x, hm, hz⟩
  refine ⟨t, ?_, ?_⟩
  · intro j
    change a < x j ∧ x j < b
    constructor
    · have h : a ≤ r.intervalLeft a j := by
        dsimp [intervalLeft]
        split_ifs <;> (first | exact le_rfl | exact (ha _).le)
      exact h.trans_lt (hx j).1
    · have h : r.intervalRight b j ≤ b := by
        dsimp [intervalRight]
        split_ifs <;> (first | exact le_rfl | exact (hb _).le)
      exact (hx j).2.trans_le h
  · intro j
    change x j.castSucc < r.root j ∧ r.root j < x j.succ
    constructor
    · simpa [intervalRight, j.isLt] using (hx j.castSucc).2
    · simpa [intervalLeft] using (hx j.succ).1

private theorem alternating_sign_product (k : ℕ) (A B : ℝ)
    (hA : 0 < (-1 : ℝ) ^ (k + 1) * A) (hB : 0 < (-1 : ℝ) ^ k * B) :
    A * B < 0 := by
  have ht : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have he : ((-1 : ℝ) ^ (k + 1) * A) * ((-1 : ℝ) ^ k * B) = -(A * B) := by
    rw [pow_succ]
    calc
      _ = -((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (A * B) := by ring
      _ = -(A * B) := by rw [ht]; ring
  have hp := mul_pos hA hB
  rw [he] at hp
  linarith

/-- Alternating recurrence values suffice to construct the next full root
list by the intermediate value theorem. -/
theorem interlacing_of_alternating_signs {P Q : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (hQ : Q.Monic) (hd : Q.natDegree = n + 1) (a b : ℝ) (hab : a < b)
    (ha : ∀ j, a < r.root j) (hb : ∀ j, r.root j < b)
    (hQa : 0 < (-1 : ℝ) ^ (n + 1) * Q.eval a) (hQb : 0 < Q.eval b)
    (hQr : ∀ j : Fin n, 0 < (-1 : ℝ) ^ (n - j.val) * Q.eval (r.root j)) :
    ∃ t : RealRootList Q (n + 1),
      (∀ j, a < t.root j ∧ t.root j < b) ∧
      (∀ j : Fin n, t.root j.castSucc < r.root j ∧ r.root j < t.root j.succ) := by
  apply r.interlacing_of_sign_changes hQ hd a b hab ha hb
  intro i
  have hl : 0 < (-1 : ℝ) ^ (n + 1 - i.val) * Q.eval (r.intervalLeft a i) := by
    by_cases hi : i.val = 0
    · simpa [intervalLeft, hi] using hQa
    · have h := hQr ⟨i.val - 1, by omega⟩
      simpa only [intervalLeft, hi, ↓reduceDIte,
        show n - (i.val - 1) = n + 1 - i.val by omega] using h
  have hr : 0 < (-1 : ℝ) ^ (n - i.val) * Q.eval (r.intervalRight b i) := by
    by_cases hi : i.val < n
    · simpa only [intervalRight, hi, ↓reduceDIte] using hQr ⟨i.val, hi⟩
    · have he : i.val = n := by omega
      simpa [intervalRight, hi, he] using hQb
  rw [show n + 1 - i.val = (n - i.val) + 1 by omega] at hl
  exact alternating_sign_product _ _ _ hl hr

end RealRootList

end RenyiMonotonicity
