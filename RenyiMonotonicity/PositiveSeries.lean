module

public import RenyiMonotonicity.Definitions
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

open scoped BigOperators

namespace RenyiMonotonicity

/-- A finite word of positive-degree monomial choices. Keeping this countable
index avoids an unnecessary rearrangement by total degree. -/
def PositiveSeriesWord : ℕ → Type
  | 0 => Unit
  | n + 1 => ℕ × PositiveSeriesWord n

instance (n : ℕ) : Countable (PositiveSeriesWord n) := by
  induction n with
  | zero => change Countable Unit; infer_instance
  | succ n ih => change Countable (ℕ × PositiveSeriesWord n); infer_instance

/-- Product coefficient attached to a finite word. -/
noncomputable def positiveWordCoefficient (b : ℕ → ℝ) : (n : ℕ) → PositiveSeriesWord n → ℝ
  | 0, _ => 1
  | n + 1, w => b w.1 * positiveWordCoefficient b n w.2

/-- Half the even monomial degree attached to a finite word. -/
def positiveWordDegree : (n : ℕ) → PositiveSeriesWord n → ℕ
  | 0, _ => 0
  | n + 1, w => w.1 + 1 + positiveWordDegree n w.2

theorem positiveWordCoefficient_nonneg (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (n : ℕ) (w : PositiveSeriesWord n) : 0 ≤ positiveWordCoefficient b n w := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hb w.1) (ih w.2)

/-- A finite power of a convergent series equals its absolutely convergent
word expansion. This includes the empty word. -/
theorem hasSum_positiveWords (b : ℕ → ℝ) (y B : ℝ)
    (hb : HasSum (fun n : ℕ => b n * y ^ (2 * n + 2)) B) (r : ℕ) :
    HasSum (fun w : PositiveSeriesWord r =>
      positiveWordCoefficient b r w * y ^ (2 * positiveWordDegree r w)) (B ^ r) := by
  induction r with
  | zero =>
      simp [PositiveSeriesWord, positiveWordCoefficient, positiveWordDegree]
  | succ r ih =>
      have hs := hb.mul ih (summable_mul_of_summable_norm hb.summable.norm ih.summable.norm)
      change HasSum (fun w : ℕ × PositiveSeriesWord r =>
        (b w.1 * positiveWordCoefficient b r w.2) *
          y ^ (2 * (w.1 + 1 + positiveWordDegree r w.2))) (B ^ (r + 1))
      convert hs using 1
      · ext w
        change (b w.1 * positiveWordCoefficient b r w.2) *
          y ^ (2 * (w.1 + 1 + positiveWordDegree r w.2)) =
            (b w.1 * y ^ (2 * w.1 + 2)) *
              (positiveWordCoefficient b r w.2 * y ^ (2 * positiveWordDegree r w.2))
        rw [show 2 * (w.1 + 1 + positiveWordDegree r w.2) =
          (2 * w.1 + 2) + 2 * positiveWordDegree r w.2 by omega, pow_add]
        ring
      · rw [pow_succ']

/-- Countable monomial index for a geometric series of positive even series. -/
abbrev PositiveSeriesIndex := (r : ℕ) × PositiveSeriesWord r

/-- Geometric inversion expressed as an absolutely convergent nonnegative
monomial family, with no formal-coefficient rearrangement hypothesis. -/
theorem hasSum_positiveWord_geometric (b : ℕ → ℝ) (y B : ℝ)
    (hb₀ : ∀ n, 0 ≤ b n) (hB₀ : 0 ≤ B) (hB₁ : B < 1)
    (hb : HasSum (fun n : ℕ => b n * y ^ (2 * n + 2)) B) :
    HasSum (fun w : PositiveSeriesIndex => positiveWordCoefficient b w.1 w.2 *
      y ^ (2 * positiveWordDegree w.1 w.2)) (1 - B)⁻¹ := by
  let f : PositiveSeriesIndex → ℝ := fun w => positiveWordCoefficient b w.1 w.2 *
    y ^ (2 * positiveWordDegree w.1 w.2)
  have hw := hasSum_positiveWords b y B hb
  have hg := hasSum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hB₀])
  have hs : Summable f := by
    apply (summable_sigma_of_nonneg (fun w => ?_)).mpr
    · exact ⟨fun r => (hw r).summable, hg.summable.congr (fun r => (hw r).tsum_eq.symm)⟩
    · exact mul_nonneg (positiveWordCoefficient_nonneg b hb₀ w.1 w.2)
        (Even.pow_nonneg (even_two_mul _) _)
  have heq := (hs.hasSum.sigma hw).unique hg
  rw [← heq]
  exact hs.hasSum

end RenyiMonotonicity
