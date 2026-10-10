module

public import Mathlib

@[expose] public section

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

@[simp] theorem renyi_zero {m : ℕ} (g : Fin m → ℝ) :
    renyi 0 g = Real.log (supportCard g : ℝ) := by simp [renyi]

@[simp] theorem tsallis_zero {m : ℕ} (g : Fin m → ℝ) :
    tsallis 0 g = (supportCard g : ℝ) - 1 := by simp [tsallis]

@[simp] theorem renyi_one {m : ℕ} (g : Fin m → ℝ) : renyi 1 g = shannon g := by
  simp [renyi]

@[simp] theorem tsallis_one {m : ℕ} (g : Fin m → ℝ) : tsallis 1 g = shannon g := by
  simp [tsallis]

end RenyiMonotonicity
