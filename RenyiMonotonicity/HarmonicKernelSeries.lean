module

public import RenyiMonotonicity.HarmonicSeries
public import RenyiMonotonicity.HarmonicGap

@[expose] public section

open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- Simultaneous odd and even parts of an even binomial power, as polynomials in
its first argument squared. The recurrence makes coefficient positivity explicit. -/
noncomputable def harmonicPolynomialPair (b : ℝ) : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (0, 1)
  | m + 1 =>
      let uv := harmonicPolynomialPair b m
      ((X + C (b ^ 2)) * uv.1 + C (2 * b) * uv.2,
        (X + C (b ^ 2)) * uv.2 + C (2 * b) * X * uv.1)

private theorem polynomial_coeff_mul_nonneg (p r : Polynomial ℝ)
    (hp : ∀ n, 0 ≤ p.coeff n) (hr : ∀ n, 0 ≤ r.coeff n) (n : ℕ) :
    0 ≤ (p * r).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hp v.1) (hr v.2)

/-- Both binomial-parity polynomials have nonnegative coefficients. -/
theorem harmonicPolynomialPair_coeff_nonneg (b : ℝ) (hb : 0 ≤ b) (m n : ℕ) :
    0 ≤ (harmonicPolynomialPair b m).1.coeff n ∧
      0 ≤ (harmonicPolynomialPair b m).2.coeff n := by
  induction m generalizing n with
  | zero => simp [harmonicPolynomialPair, coeff_one]; positivity
  | succ m ih =>
      have hx (n : ℕ) : 0 ≤ (X : Polynomial ℝ).coeff n := by simp [coeff_X]; positivity
      have hc (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : 0 ≤ (C a).coeff n := by
        simp only [coeff_C]
        split_ifs <;> positivity
      have hbase (n : ℕ) : 0 ≤ (X + C (b ^ 2) : Polynomial ℝ).coeff n := by
        rw [coeff_add]
        exact add_nonneg (hx n) (hc _ (sq_nonneg b) n)
      simp only [harmonicPolynomialPair, coeff_add]
      constructor
      · exact add_nonneg
          (polynomial_coeff_mul_nonneg _ _ hbase (fun n => (ih n).1) n)
          (polynomial_coeff_mul_nonneg _ _ (hc _ (by positivity)) (fun n => (ih n).2) n)
      · exact add_nonneg
          (polynomial_coeff_mul_nonneg _ _ hbase (fun n => (ih n).2) n)
          (polynomial_coeff_mul_nonneg _ _
            (polynomial_coeff_mul_nonneg _ _ (hc _ (by positivity)) hx) (fun n => (ih n).1) n)

/-- Exact even-power identities for the two positive polynomial recurrences. -/
theorem harmonicPolynomialPair_eval (b a : ℝ) (m : ℕ) :
    (a + b) ^ (2 * m) - (a - b) ^ (2 * m) =
      2 * a * (harmonicPolynomialPair b m).1.eval (a ^ 2) ∧
    (a + b) ^ (2 * m) + (a - b) ^ (2 * m) =
      2 * (harmonicPolynomialPair b m).2.eval (a ^ 2) := by
  induction m with
  | zero => norm_num [harmonicPolynomialPair]
  | succ m ih =>
      have he : 2 * (m + 1) = 2 * m + 2 := by omega
      simp only [he, pow_add, harmonicPolynomialPair, eval_add, eval_mul, eval_X, eval_C]
      constructor
      · calc
          (a + b) ^ (2 * m) * (a + b) ^ 2 - (a - b) ^ (2 * m) * (a - b) ^ 2 =
              (a ^ 2 + b ^ 2) * ((a + b) ^ (2 * m) - (a - b) ^ (2 * m)) +
                2 * a * b * ((a + b) ^ (2 * m) + (a - b) ^ (2 * m)) := by ring
          _ = _ := by rw [ih.1, ih.2]; ring
      · calc
          (a + b) ^ (2 * m) * (a + b) ^ 2 + (a - b) ^ (2 * m) * (a - b) ^ 2 =
              (a ^ 2 + b ^ 2) * ((a + b) ^ (2 * m) + (a - b) ^ (2 * m)) +
                2 * a * b * ((a + b) ^ (2 * m) - (a - b) ^ (2 * m)) := by ring
          _ = _ := by rw [ih.1, ih.2]; ring

/-- The constant terms include the exact removable-center coefficient. -/
theorem harmonicPolynomialPair_eval_zero (b : ℝ) (m : ℕ) :
    (harmonicPolynomialPair b m).1.eval 0 = (2 * m : ℕ) * b ^ (2 * m - 1) ∧
      (harmonicPolynomialPair b m).2.eval 0 = b ^ (2 * m) := by
  induction m with
  | zero => norm_num [harmonicPolynomialPair]
  | succ m ih =>
      simp only [harmonicPolynomialPair, eval_add, eval_mul, eval_X, eval_C, zero_add,
        mul_zero, zero_mul, add_zero, ih.1, ih.2]
      by_cases hm : m = 0
      · subst m
        norm_num
      have he : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have h₁ : b ^ 2 * b ^ (2 * m - 1) = b ^ (2 * m + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have h₂ : b * b ^ (2 * m) = b ^ (2 * m + 1) := by rw [pow_succ']
      constructor
      · rw [he]
        push_cast
        calc
          b ^ 2 * ((2 * (m : ℝ)) * b ^ (2 * m - 1)) + 2 * b * b ^ (2 * m) =
              (2 * (m : ℝ)) * (b ^ 2 * b ^ (2 * m - 1)) + 2 * (b * b ^ (2 * m)) := by ring
          _ = _ := by rw [h₁, h₂]; ring
      · rw [← pow_add]
        congr 1
        omega

/-- Polynomial evaluation viewed as a finitely supported, hence absolutely
convergent, series. -/
theorem hasSum_polynomial_even_eval (p : Polynomial ℝ) (x : ℝ) :
    HasSum (fun n : ℕ => p.coeff n * x ^ (2 * n)) (p.eval (x ^ 2)) := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := p.support)
    (f := fun n : ℕ => p.coeff n * x ^ (2 * n)) (fun n hn => by
      rw [notMem_support_iff.mp hn, zero_mul])
  convert hs using 1
  simp only [eval_eq_sum, Polynomial.sum, pow_mul]

/-- Exact factorization of the completed lowering kernel into its positive even
kernel and a finite polynomial. The identity includes the removable center. -/
theorem harmonicLoweringKernel_eq_evenPolynomial (m : ℕ) (q δ x : ℝ) :
    harmonicLoweringKernel (2 * m) q δ x =
      harmonicEvenKernel q x * ((1 - δ) / (1 - δ) ^ q) *
        (harmonicPolynomialPair (δ / 2) m).1.eval (((1 - δ) * x) ^ 2) := by
  by_cases hx : x = 0
  · subst x
    simp only [harmonicLoweringKernel, harmonicEvenKernel, ite_true,
      mul_zero, zero_pow (by decide : 2 ≠ 0), harmonicPolynomialPair_eval_zero]
    unfold harmonicCenterValue
    have hhalf : (1 / 2 : ℝ) ^ (q - 1) = ((2 : ℝ) ^ (q - 1))⁻¹ := by
      rw [one_div, Real.inv_rpow (by norm_num)]
    rw [hhalf]
    have hs : (2 : ℝ) ^ (q - 1) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    push_cast
    ring
  · simp only [harmonicLoweringKernel, harmonicEvenKernel, ite_eq_right hx]
    unfold harmonicLoweringQuotient harmonicOddDenominator
    rw [(harmonicPolynomialPair_eval (δ / 2) ((1 - δ) * x) m).1]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Countable index for the finite polynomial times the positive even-kernel family. -/
abbrev HarmonicLoweringSeriesIndex := ℕ × PositiveSeriesIndex

/-- Half the even degree of a lowering-kernel monomial. -/
def harmonicLoweringSeriesDegree (w : HarmonicLoweringSeriesIndex) : ℕ :=
  w.1 + positiveWordDegree w.2.1 w.2.2

/-- The actual lowering-kernel coefficient, zero outside the finite polynomial
support in its first index. -/
noncomputable def harmonicLoweringSeriesCoefficient (m : ℕ) (q δ : ℝ)
    (w : HarmonicLoweringSeriesIndex) : ℝ :=
  ((1 - δ) / (1 - δ) ^ q) * (harmonicPolynomialPair (δ / 2) m).1.coeff w.1 *
    (1 - δ) ^ (2 * w.1) * harmonicEvenSeriesCoefficient q w.2

/-- Every lowering-kernel coefficient is nonnegative in the exact parameter range. -/
theorem harmonicLoweringSeriesCoefficient_nonneg (m : ℕ) (q δ : ℝ)
    (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (w : HarmonicLoweringSeriesIndex) : 0 ≤ harmonicLoweringSeriesCoefficient m q δ w := by
  have hA : 0 < 1 - δ := sub_pos.mpr hδ₁
  have hp := (harmonicPolynomialPair_coeff_nonneg (δ / 2) (by positivity) m w.1).1
  have he := harmonicEvenSeriesCoefficient_nonneg q hq₁ hq₂ w.2
  unfold harmonicLoweringSeriesCoefficient
  positivity

/-- Absolutely convergent positive even-monomial expansion of the actual
completed lowering kernel on the entire closed interval, including its center. -/
theorem hasSum_harmonicLoweringKernel (m : ℕ) (q δ : ℝ)
    (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    HasSum (fun w : HarmonicLoweringSeriesIndex => harmonicLoweringSeriesCoefficient m q δ w *
      x ^ (2 * harmonicLoweringSeriesDegree w)) (harmonicLoweringKernel (2 * m) q δ x) := by
  have hp := hasSum_polynomial_even_eval (harmonicPolynomialPair (δ / 2) m).1 ((1 - δ) * x)
  have he := hasSum_harmonicEvenKernel q hq₁ hq₂ x hx
  have hprod := hp.mul he (summable_mul_of_summable_norm hp.summable.norm he.summable.norm)
  have hs := hprod.mul_left ((1 - δ) / (1 - δ) ^ q)
  rw [harmonicLoweringKernel_eq_evenPolynomial]
  convert hs using 1
  · ext w
    simp only [harmonicLoweringSeriesCoefficient, harmonicLoweringSeriesDegree, mul_pow,
      Nat.mul_add, pow_add]
    ring
  · ring

/-- Endpoint convergence provides the summable majorant for every subsequent
finite difference and summation-by-parts interchange. -/
theorem summable_harmonicLoweringKernel_endpoint (m : ℕ) (q δ : ℝ)
    (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    Summable (fun w : HarmonicLoweringSeriesIndex => harmonicLoweringSeriesCoefficient m q δ w *
      (1 / 2 : ℝ) ^ (2 * harmonicLoweringSeriesDegree w)) :=
  (hasSum_harmonicLoweringKernel m q δ hq₁ hq₂ (1 / 2) (by norm_num)).summable

end RenyiMonotonicity
