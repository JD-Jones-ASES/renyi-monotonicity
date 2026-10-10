module
public import RenyiMonotonicity.Definitions
public import RenyiMonotonicity.PairMoments

@[expose] public section
noncomputable section
open scoped BigOperators
namespace RenyiMonotonicity

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
