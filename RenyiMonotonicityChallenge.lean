module
public import Mathlib

/-! Literal full mathematical contract. The three statement placeholders are intentional;
Solution must supply every proof before the full Comparator contract can pass.
Monotonicity concerns Bernoulli parameters, not the entropy order. -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

/-- Probability generating polynomial for a finite family of Bernoulli coins. -/
noncomputable def bernoulliPolynomial {n : ℕ} (p : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.C (1 - p i) + Polynomial.C (p i) * Polynomial.X)

/-- The actual coefficient law, including all `n + 1` possible counts. -/
noncomputable def bernoulliSum {n : ℕ} (p : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun k => (bernoulliPolynomial p).coeff k.val

/-- Integer extension makes every negative-index mass zero. -/
noncomputable def bernoulliMass {n : ℕ} (p : Fin n → ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k then (bernoulliPolynomial p).coeff k.toNat else 0

/-- A success set has its independent product Bernoulli probability. -/
noncomputable def bernoulliWeight {n : ℕ} (p : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  (∏ i ∈ s, p i) * ∏ i ∈ Finset.univ \ s, (1 - p i)

/-- Number of strictly positive atoms. Zero padding is therefore harmless at order zero. -/
noncomputable def supportCard {m : ℕ} (g : Fin m → ℝ) : ℕ :=
  (Finset.univ.filter (fun k => 0 < g k)).card

noncomputable def powerSum {m : ℕ} (q : ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ k, Real.rpow (g k) q

/-- Shannon entropy, with the continuous convention at a zero atom. -/
noncomputable def shannon {m : ℕ} (g : Fin m → ℝ) : ℝ :=
  ∑ k, Real.negMulLog (g k)

/-- Rényi entropy with explicit support and Shannon endpoint branches. -/
noncomputable def renyi {m : ℕ} (q : ℝ) (g : Fin m → ℝ) : ℝ :=
  if q = 0 then Real.log (supportCard g : ℝ)
  else if q = 1 then shannon g
  else Real.log (powerSum q g) / (1 - q)

/-- Tsallis entropy with explicit support and Shannon endpoint branches. -/
noncomputable def tsallis {m : ℕ} (q : ℝ) (g : Fin m → ℝ) : ℝ :=
  if q = 0 then (supportCard g : ℝ) - 1
  else if q = 1 then shannon g
  else (powerSum q g - 1) / (1 - q)


def expectation {n : ℕ} (μ z : Fin n → ℝ) : ℝ := ∑ i, μ i * z i

/-- A sampled secant slope. Only values with `i < j` enter the theorem. -/
def secantSlope {n : ℕ} (y x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (x j - x i) / (y j - y i)

/-- The exact finite-data substitute for an increasing convex inverse score. -/
structure IncreasingSecants {n : ℕ} (y x : Fin n → ℝ) : Prop where
  nonneg : ∀ i j, i < j → 0 ≤ secantSlope y x i j
  left_mono : ∀ i i' j, i ≤ i' → i' < j → secantSlope y x i j ≤ secantSlope y x i' j
  right_mono : ∀ i j j', i < j → j ≤ j' → secantSlope y x i j ≤ secantSlope y x i j'


/-- Full closed-cube Rényi monotonicity in every finite dimension and real order in [0,2]. -/
theorem renyi_monotone {n : ℕ} (p r : Fin n → ℝ) (q : ℝ)
    (hq : 0 ≤ q ∧ q ≤ 2) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ r i ∧ r i ≤ 1/2) :
    renyi q (bernoulliSum p) ≤ renyi q (bernoulliSum r) := by
  sorry

/-- Full closed-cube Tsallis monotonicity, including support and Shannon orders. -/
theorem tsallis_monotone {n : ℕ} (p r : Fin n → ℝ) (q : ℝ)
    (hq : 0 ≤ q ∧ q ≤ 2) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ r i ∧ r i ≤ 1/2) :
    tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum r) := by
  sorry

/-- The finite convex-inverse-score moment inequality, with its actual hypotheses. -/
theorem inverse_score_association {n : ℕ} (μ y x : Fin n → ℝ) (α : ℝ)
    (hμpos : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1)
    (hy : ∀ i, -1 ≤ y i ∧ y i ≤ 1) (hym : StrictMono y)
    (hymean : expectation μ y = 0) (hm2 : 0 < expectation μ (fun i => y i^2))
    (hα : 0 ≤ α) (hα1 : α < 1) (hx : IncreasingSecants y x) :
    (expectation μ (fun i => y i^3) / expectation μ (fun i => y i^2)) *
      (expectation μ (fun i => x i^2) - (expectation μ x)^2 +
        α*(expectation μ (fun i => y i*x i))^2) ≤
    (1-α*expectation μ (fun i => y i^2))*expectation μ (fun i => y i*x i^2) -
      2*expectation μ (fun i => y i*x i)*expectation μ (fun i => x i*(1-α*y i^2)) := by
  sorry

/-- Concrete Bernoulli probability polynomial; body checked by Comparator. -/
theorem bernoulliPolynomial_spec {n : ℕ} (p : Fin n → ℝ) :
    bernoulliPolynomial p = ∏ i, (Polynomial.C (1-p i) + Polynomial.C (p i)*Polynomial.X) := rfl

/-- Concrete finite coefficient law, including zero padding. -/
theorem bernoulliSum_spec {n : ℕ} (p : Fin n → ℝ) (k : Fin (n+1)) :
    bernoulliSum p k = (bernoulliPolynomial p).coeff k.val := rfl

/-- Order-zero support counts positive masses only. -/
theorem supportCard_spec {m : ℕ} (g : Fin m → ℝ) :
    supportCard g = (Finset.univ.filter (fun k => 0 < g k)).card := rfl

/-- The ordinary real power sum. -/
theorem powerSum_spec {m : ℕ} (q : ℝ) (g : Fin m → ℝ) :
    powerSum q g = ∑ k, Real.rpow (g k) q := rfl

/-- Shannon entropy with the continuous zero-atom convention. -/
theorem shannon_spec {m : ℕ} (g : Fin m → ℝ) :
    shannon g = ∑ k, Real.negMulLog (g k) := rfl

/-- The complete Rényi definition, including both exceptional orders. -/
theorem renyi_spec {m : ℕ} (q : ℝ) (g : Fin m → ℝ) :
    renyi q g = if q=0 then Real.log (supportCard g : ℝ) else if q=1 then shannon g
      else Real.log (powerSum q g)/(1-q) := rfl

/-- The complete Tsallis definition, including both exceptional orders. -/
theorem tsallis_spec {m : ℕ} (q : ℝ) (g : Fin m → ℝ) :
    tsallis q g = if q=0 then (supportCard g : ℝ)-1 else if q=1 then shannon g
      else (powerSum q g-1)/(1-q) := rfl

/-- The finite weighted expectation used in the association statement. -/
theorem expectation_spec {n : ℕ} (μ z : Fin n → ℝ) :
    expectation μ z = ∑ i, μ i*z i := rfl

end RenyiMonotonicity
