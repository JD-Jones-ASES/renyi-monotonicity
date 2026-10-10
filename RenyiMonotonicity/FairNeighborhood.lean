module
public import RenyiMonotonicity.ShannonFair
public import RenyiMonotonicity.FairDerivative

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RenyiMonotonicity

theorem normalizedCoinDerivative_all_half_neg (n : ℕ) (i : Fin (n + 1))
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    normalizedCoinDerivative q (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) i < 0 := by
  rcases hq1.eq_or_lt with hq | hq
  · subst q
    exact normalizedCoinDerivative_all_half_one_neg n i
  let v : Fin (n + 1) → ℝ := fun _ => 1 / 2
  have hs := edgeSum_pos v (fun _ => by norm_num [v]) (fun _ => by norm_num [v])
  have he : (fun t => normalizedMidpointFunctional q (Function.update v i t)) =ᶠ[𝓝 (1 / 2)]
      (fun t => midpointFunctional q (Function.update v i t) / (1 - q)) := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_lt_nhds (by norm_num : (1 / 2 : ℝ) < 1)] with t ht0 ht1
    apply normalizedMidpointFunctional_eq q _ hq.ne
    · intro j; by_cases h : j = i <;> simp [Function.update, h, v, ht0.le]
    · intro j; by_cases h : j = i <;> norm_num [Function.update, h, v, ht1.le]
  have hd : HasDerivAt (fun t => midpointFunctional q (Function.update v i t))
      (deriv (fun t => midpointFunctional q (Function.update v i t)) (1 / 2)) (1 / 2) := by
    have hcons := hasDerivAt_midpointFunctional_cons_half q (omitCoin v i)
      (fun _ => by norm_num [omitCoin, v]) (fun _ => by norm_num [omitCoin, v])
    have hfun : (fun t => midpointFunctional q (Function.update v i t)) =
        (fun t => midpointFunctional q (Fin.cons t (omitCoin v i))) := by
      funext t
      simp only [midpointFunctional, edgeDifference, edgeSum, bernoulliMass,
        bernoulliPolynomial_update_eq_cons]
    rw [hfun]
    exact hcons.differentiableAt.hasDerivAt
  have hsame := (hasDerivAt_normalizedMidpointFunctional_update q v i hs).unique
    ((hd.div_const (1 - q)).congr_of_eventuallyEq he)
  rw [hsame]
  exact div_neg_of_neg_of_pos
    (deriv_midpointFunctional_update_half_neg q v i hq0 hq
      (fun _ _ => by norm_num [v]) (fun _ _ => by norm_num [v])) (by linarith)

/-- On each compact positive order band, every normalized coordinate derivative
is negative throughout a common neighborhood of the fair vector. -/
theorem eventually_normalizedCoinDerivative_all_half_neg (n : ℕ) (a : ℝ)
    (ha : 0 < a) :
    ∀ᶠ p : Fin (n + 1) → ℝ in 𝓝 (fun _ => (1 / 2 : ℝ)),
      ∀ q ∈ Icc a 1, ∀ i, normalizedCoinDerivative q p i < 0 := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro q hq
  apply Filter.eventually_all.mpr
  intro i
  have hc := continuousAt_normalizedCoinDerivative q (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) i
    (edgeSum_pos _ (fun _ => by norm_num) (fun _ => by norm_num))
  have hs : ContinuousAt (fun z : (Fin (n + 1) → ℝ) × ℝ =>
      normalizedCoinDerivative z.2 z.1 i) ((fun _ => (1 / 2 : ℝ)), q) :=
    ContinuousAt.comp (x := ((fun _ : Fin (n + 1) => (1 / 2 : ℝ)), q))
      (f := fun z : (Fin (n + 1) → ℝ) × ℝ => (z.2, z.1))
      hc (continuousAt_snd.prodMk continuousAt_fst)
  exact hs.eventually (eventually_lt_nhds
    (normalizedCoinDerivative_all_half_neg n i q (ha.trans_le hq.1) hq.2))

end RenyiMonotonicity
