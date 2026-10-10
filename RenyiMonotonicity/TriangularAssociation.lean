module

public import RenyiMonotonicity.WeightedPairs

/-! Association on the strict upper triangle, viewed as a finite distributive lattice.
The proof uses Mathlib's proved finite FKG theorem; no conditional-association hypothesis
is part of the inverse-score result. -/

@[expose] public section

namespace RenyiMonotonicity

/-- Strictly ordered pairs form a sublattice under coordinatewise minimum and maximum. -/
def orderedPairLattice (n : ℕ) : Sublattice (Fin n × Fin n) where
  carrier := {p | p.1 < p.2}
  supClosed' := by
    intro p hp q hq
    change max p.1 q.1 < max p.2 q.2
    exact max_lt_max hp hq
  infClosed' := by
    intro p hp q hq
    change min p.1 q.1 < min p.2 q.2
    exact min_lt_min hp hq

/-- The support of unordered distinct samples, represented once in increasing order. -/
abbrev OrderedPair (n : ℕ) := orderedPairLattice n

noncomputable instance (n : ℕ) : Fintype (OrderedPair n) := Fintype.ofFinite _

/-- Pair weights of a finite law. -/
def pairWeight {n : ℕ} (μ y : Fin n → ℝ) (α : ℝ) (p : OrderedPair n) : ℝ :=
  μ p.1.1 * μ p.1.2 * pairKernel α (y p.1.1) (y p.1.2)

lemma pairWeight_nonneg {n : ℕ} {μ y : Fin n → ℝ} {α : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1)
    (hα : 0 ≤ α) (hα1 : α < 1) (p : OrderedPair n) : 0 ≤ pairWeight μ y α p :=
  mul_nonneg (mul_nonneg (hμ _) (hμ _)) (pairKernel_nonneg hα hα1 (hy _) (hy _))

/-- Log-supermodularity on the triangular support, including its boundary and one-point rows. -/
theorem pairWeight_lattice {n : ℕ} {μ y : Fin n → ℝ} {α : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1)
    (hym : StrictMono y) (hα : 0 ≤ α) (hα1 : α < 1)
    (p q : OrderedPair n) :
    pairWeight μ y α p * pairWeight μ y α q ≤
      pairWeight μ y α (p ⊓ q) * pairWeight μ y α (p ⊔ q) := by
  change (μ p.1.1 * μ p.1.2 * pairKernel α (y p.1.1) (y p.1.2)) *
      (μ q.1.1 * μ q.1.2 * pairKernel α (y q.1.1) (y q.1.2)) ≤
    (μ (min p.1.1 q.1.1) * μ (min p.1.2 q.1.2) *
      pairKernel α (y (min p.1.1 q.1.1)) (y (min p.1.2 q.1.2))) *
    (μ (max p.1.1 q.1.1) * μ (max p.1.2 q.1.2) *
      pairKernel α (y (max p.1.1 q.1.1)) (y (max p.1.2 q.1.2)))
  by_cases h₁ : p.1.1 ≤ q.1.1 <;> by_cases h₂ : p.1.2 ≤ q.1.2
  · simp only [min_eq_left h₁, min_eq_left h₂, max_eq_right h₁, max_eq_right h₂, le_refl]
  · have h₂' := le_of_not_ge h₂
    simp only [min_eq_left h₁, min_eq_right h₂', max_eq_right h₁, max_eq_left h₂']
    have ht := pairKernel_tp2 hα hα1 (hy p.1.1).1 (hym.monotone h₁)
      (hym q.2) (hym.monotone h₂') (hy p.1.2).2
    have hn : 0 ≤ μ p.1.1 * μ p.1.2 * μ q.1.1 * μ q.1.2 := mul_nonneg (mul_nonneg (mul_nonneg (hμ _) (hμ _)) (hμ _)) (hμ _)
    convert mul_le_mul_of_nonneg_left ht hn using 1 <;> ring
  · have h₁' := le_of_not_ge h₁
    simp only [min_eq_right h₁', min_eq_left h₂, max_eq_left h₁', max_eq_right h₂]
    have ht := pairKernel_tp2 hα hα1 (hy q.1.1).1 (hym.monotone h₁')
      (hym p.2) (hym.monotone h₂) (hy q.1.2).2
    have hn : 0 ≤ μ p.1.1 * μ p.1.2 * μ q.1.1 * μ q.1.2 := mul_nonneg (mul_nonneg (mul_nonneg (hμ _) (hμ _)) (hμ _)) (hμ _)
    convert mul_le_mul_of_nonneg_left ht hn using 1 <;> ring
  · have h₁' := le_of_not_ge h₁
    have h₂' := le_of_not_ge h₂
    simp only [min_eq_right h₁', min_eq_right h₂', max_eq_left h₁', max_eq_left h₂']
    exact le_of_eq (mul_comm _ _)

/-- Finite weighted association for nonnegative coordinatewise increasing functions
on the strict upper triangle. The kernel hypotheses are proved sufficient by TP2. -/
theorem triangular_association_nonneg {n : ℕ} {μ y : Fin n → ℝ} {α : ℝ}
    (hμ : ∀ i, 0 ≤ μ i) (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1)
    (hym : StrictMono y) (hα : 0 ≤ α) (hα1 : α < 1)
    (F G : OrderedPair n → ℝ) (hF0 : ∀ p, 0 ≤ F p) (hG0 : ∀ p, 0 ≤ G p)
    (hF : Monotone F) (hG : Monotone G) :
    (∑ p, pairWeight μ y α p * F p) * (∑ p, pairWeight μ y α p * G p) ≤
      (∑ p, pairWeight μ y α p) * (∑ p, pairWeight μ y α p * (F p * G p)) := by
  exact fkg F G (pairWeight μ y α)
    (pairWeight_nonneg hμ hy hα hα1) hF0 hG0 hF hG
    (pairWeight_lattice hμ hy hym hα hα1)

/-- A sum on the triangular subtype written with an indicator on the full square. -/
lemma sum_orderedPair_eq {n : ℕ} (F : Fin n → Fin n → ℝ) :
    (∑ p : OrderedPair n, F p.1.1 p.1.2) =
      ∑ i, ∑ j, if i < j then F i j else 0 := by
  classical
  have h := Finset.sum_subtype (F := inferInstance) (p := fun p => p ∈ orderedPairLattice n) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (fun p => by simp [orderedPairLattice]) (fun p : Fin n × Fin n => F p.1 p.2)
  rw [← h, Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- A symmetric zero-diagonal double sum counts each ordered pair exactly twice. -/
theorem sum_symmetric_eq_twice_orderedPair {n : ℕ} (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    (∑ i, ∑ j, F i j) = 2 * ∑ p : OrderedPair n, F p.1.1 p.1.2 := by
  classical
  rw [sum_orderedPair_eq]
  have split : ∀ i j, F i j =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr hij.le]
    · subst j; simp [hdiag]
    · simp [hij, not_lt.mpr hij.le, hF]
  calc
    (∑ i, ∑ j, F i j) =
        (∑ i, ∑ j, if i < j then F i j else 0) +
        (∑ i, ∑ j, if j < i then F j i else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => split i j)
    _ = 2 * ∑ i, ∑ j, if i < j then F i j else 0 := by
      rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
      ring

end RenyiMonotonicity
