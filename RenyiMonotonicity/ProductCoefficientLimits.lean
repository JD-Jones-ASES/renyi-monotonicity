module

public import RenyiMonotonicity.ProductCoefficientComparison

@[expose] public section

open scoped Topology
open Filter Polynomial

namespace RenyiMonotonicity

/-- Each fixed coefficient is continuous in the finitely many factor
parameters. No topology on the polynomial space is needed. -/
theorem continuous_linearFactorProduct_coeff {α : Type*} [TopologicalSpace α]
    {n : ℕ} (u : α → Fin n → ℝ) (hu : ∀ i, Continuous (fun x => u x i)) (k : ℕ) :
    Continuous (fun x => (linearFactorProduct (u x)).coeff k) := by
  induction n generalizing k with
  | zero => simpa using (continuous_const : Continuous (fun _ : α => (1 : ℝ[X]).coeff k))
  | succ n ih =>
      cases k with
      | zero => simpa using (continuous_const : Continuous (fun _ : α => (1 : ℝ)))
      | succ k =>
          have htail (j : Fin n) : Continuous (fun x => Fin.tail (u x) j) := hu j.succ
          have H := (ih (fun x => Fin.tail (u x)) htail (k + 1)).add
            ((hu 0).mul (ih (fun x => Fin.tail (u x)) htail k))
          convert H using 1
          funext x
          nth_rw 1 [← Fin.cons_self_tail (u x)]
          rw [linearFactorProduct_cons, coeff_mul_positiveFactor_succ]
          rfl

/-- The coefficient comparison extends to zero factors by a positive
parameter approximation, after clearing the denominators. -/
theorem linearFactorProduct_cross_nonneg {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (huv : ∀ i, u i ≤ v i) (k : ℕ) (hk : k < n) :
    (linearFactorProduct u).coeff (k + 1) * (linearFactorProduct v).coeff k ≤
      (linearFactorProduct u).coeff k * (linearFactorProduct v).coeff (k + 1) := by
  have huc (j : ℕ) := continuous_linearFactorProduct_coeff
    (fun ε : ℝ => fun i => u i + ε) (fun i => continuous_const.add continuous_id) j
  have hvc (j : ℕ) := continuous_linearFactorProduct_coeff
    (fun ε : ℝ => fun i => v i + ε) (fun i => continuous_const.add continuous_id) j
  have hl := (((huc (k + 1)).mul (hvc k)).continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hr := (((huc k).mul (hvc (k + 1))).continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto (by simpa using hl) (by simpa using hr)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp (i) : 0 < u i + ε := add_pos_of_nonneg_of_pos (hu i) hε
  have ho (i) : u i + ε ≤ v i + ε := by linarith [huv i]
  have H := linearFactorProduct_ratio_mono (fun i => u i + ε) (fun i => v i + ε) hp ho k hk
  have h₀ := linearFactorProduct_coeff_pos (fun i => u i + ε) hp k hk.le
  have h₁ := linearFactorProduct_coeff_pos (fun i => v i + ε)
    (fun i => (hp i).trans_le (ho i)) k hk.le
  rw [div_le_div_iff₀ h₀ h₁] at H
  simpa only [Pi.mul_apply, mul_comm] using H

end RenyiMonotonicity
