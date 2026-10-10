module
public import RenyiMonotonicity.NormalizedMidpoint

@[expose] public section
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RenyiMonotonicity

def coinMassDerivative {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (k : ℤ) : ℝ :=
  bernoulliMass (omitCoin p i) (k - 1) - bernoulliMass (omitCoin p i) k

def normalizedCoinDerivative {n : ℕ} (q : ℝ) (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k : Fin (n + 3),
    ((coinMassDerivative p i ((k.val : ℤ) - 1) - coinMassDerivative p i (k.val : ℤ)) *
      entropyOrderKernel q (edgeSum p k) -
    edgeDifference p k * (edgeSum p k) ^ (q - 2) *
      (coinMassDerivative p i ((k.val : ℤ) - 1) + coinMassDerivative p i (k.val : ℤ)))

/-- Actual normalized coordinate differentiation is valid at order one as well
as on both sides of it, whenever all adjacent masses are positive. -/
theorem hasDerivAt_normalizedMidpointFunctional_update {n : ℕ} (q : ℝ)
    (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hs : ∀ k, 0 < edgeSum p k) :
    HasDerivAt (fun t => normalizedMidpointFunctional q (Function.update p i t))
      (normalizedCoinDerivative q p i) (p i) := by
  classical
  have hd (k : Fin (n + 3)) :
      HasDerivAt (fun t => edgeDifference (Function.update p i t) k *
        entropyOrderKernel q (edgeSum (Function.update p i t) k))
        ((coinMassDerivative p i ((k.val : ℤ) - 1) - coinMassDerivative p i (k.val : ℤ)) *
          entropyOrderKernel q (edgeSum p k) - edgeDifference p k * (edgeSum p k) ^ (q - 2) *
          (coinMassDerivative p i ((k.val : ℤ) - 1) + coinMassDerivative p i (k.val : ℤ))) (p i) := by
    have h₁ := hasDerivAt_bernoulliMass_update p i (p i) ((k.val : ℤ) - 1)
    have h₂ := hasDerivAt_bernoulliMass_update p i (p i) (k.val : ℤ)
    have hsum : HasDerivAt (fun t => edgeSum (Function.update p i t) k)
        (coinMassDerivative p i ((k.val : ℤ) - 1) + coinMassDerivative p i (k.val : ℤ)) (p i) :=
      h₁.add h₂
    have hdiff : HasDerivAt (fun t => edgeDifference (Function.update p i t) k)
        (coinMassDerivative p i ((k.val : ℤ) - 1) - coinMassDerivative p i (k.val : ℤ)) (p i) :=
      h₁.sub h₂
    have hh := hdiff.mul ((hasDerivAt_entropyOrderKernel (q := q)
      (show 0 < edgeSum (Function.update p i (p i)) k by simpa using hs k)).comp (p i) hsum)
    convert hh using 1
    · ext t; rfl
    · simp only [Function.update_eq_self, Function.comp_apply]
      ring
  simpa only [normalizedMidpointFunctional, normalizedCoinDerivative] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hd k)

theorem continuous_coinMassDerivative {n : ℕ} (i : Fin (n + 1)) (k : ℤ) :
    Continuous (fun p : Fin (n + 1) → ℝ => coinMassDerivative p i k) := by
  have ho : Continuous (fun p : Fin (n + 1) → ℝ => omitCoin p i) :=
    continuous_pi (fun j => continuous_apply (i.succAbove j))
  exact ((continuous_bernoulliMass_coordinate (k - 1)).comp ho).sub
    ((continuous_bernoulliMass_coordinate k).comp ho)

/-- The actual normalized gradient is jointly continuous in entropy order and
the positive law, including the removable Shannon slice. -/
theorem continuousAt_normalizedCoinDerivative {n : ℕ} (q : ℝ)
    (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hs : ∀ k, 0 < edgeSum p k) :
    ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => normalizedCoinDerivative z.1 z.2 i) (q, p) := by
  unfold normalizedCoinDerivative
  apply tendsto_finsetSum
  intro k _
  have h₁ : ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => coinMassDerivative z.2 i ((k.val : ℤ) - 1)) (q, p) :=
    (continuous_coinMassDerivative i ((k.val : ℤ) - 1)).continuousAt.comp continuousAt_snd
  have h₂ : ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => coinMassDerivative z.2 i (k.val : ℤ)) (q, p) :=
    (continuous_coinMassDerivative i (k.val : ℤ)).continuousAt.comp continuousAt_snd
  have hsum : ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => edgeSum z.2 k) (q, p) :=
    (continuous_edgeSum k).continuousAt.comp continuousAt_snd
  have hdiff : ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => edgeDifference z.2 k) (q, p) :=
    (continuous_edgeDifference k).continuousAt.comp continuousAt_snd
  have hker : ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => entropyOrderKernel z.1 (edgeSum z.2 k)) (q, p) :=
    ContinuousAt.comp (x := (q, p)) (f := fun z : ℝ × (Fin (n + 1) → ℝ) => (z.1, edgeSum z.2 k))
      (continuousAt_entropyOrderKernel (q := q) (hs k)) (continuousAt_fst.prodMk hsum)
  have hpow : ContinuousAt (fun z : ℝ × (Fin (n + 1) → ℝ) => (edgeSum z.2 k) ^ (z.1 - 2)) (q, p) :=
    ContinuousAt.comp (x := (q, p)) (f := fun z : ℝ × (Fin (n + 1) → ℝ) => (edgeSum z.2 k, z.1 - 2))
      (Real.continuousAt_rpow (edgeSum p k, q - 2) (Or.inl (hs k).ne'))
      (hsum.prodMk (continuousAt_fst.sub continuousAt_const))
  exact ((h₁.sub h₂).mul hker).sub ((hdiff.mul hpow).mul (h₁.add h₂))

end RenyiMonotonicity
