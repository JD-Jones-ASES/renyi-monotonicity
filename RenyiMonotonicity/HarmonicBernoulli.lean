module

public import RenyiMonotonicity.HarmonicLowering
public import RenyiMonotonicity.MixingConcavity
public import RenyiMonotonicity.MidpointFunctional

@[expose] public section

open scoped Topology
open Filter

namespace RenyiMonotonicity

/-- The actual positive half-cube count law satisfies every finite-sequence
hypothesis used in harmonic lowering. -/
noncomputable def bernoulliHarmonicSequence {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) : HarmonicSequence n where
  mass k := bernoulliMass p (k : ℤ)
  node k := mixingCoefficient p (k : ℤ)
  mass_pos k hk := bernoulliMass_pos p hp (fun i => by linarith [hpHalf i]) k (by omega) (by omega)
  node_zero := by simp
  node_last := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      mixingCoefficient_outer_right p hp (fun i => by linarith [hpHalf i])
  node_step k hk := by
    have h := mixingCoefficient_gap_pos p hp (fun i => by linarith [hpHalf i]) k (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using sub_pos.mp h
  concave k hk := by
    cases n with
    | zero => omega
    | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        mixingCoefficient_gap_antitone_step p hp hpHalf k (by omega) (by omega)
  balance k hk := by
    have h₀ := bernoulliMass_pos p hp (fun i => by linarith [hpHalf i]) k (by omega) (by omega)
    have h₁ := bernoulliMass_pos p hp (fun i => by linarith [hpHalf i]) (k + 1) (by omega) (by omega)
    have hd : bernoulliMass p k + bernoulliMass p (k + 1) ≠ 0 := by positivity
    simp only [mixingCoefficient, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    field_simp
    ring

@[simp] theorem bernoulliHarmonicSequence_mass {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (k : ℕ) :
    (bernoulliHarmonicSequence p hp hpHalf).mass k = bernoulliMass p (k : ℤ) := rfl

@[simp] theorem bernoulliHarmonicSequence_node {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (k : ℕ) :
    (bernoulliHarmonicSequence p hp hpHalf).node k = mixingCoefficient p (k : ℤ) := rfl

/-- Actual Bernoulli even-moment inequalities, with no structural certificate
in the hypotheses and no bound on the moment index. -/
theorem bernoulli_harmonic_moment_nonpos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) (m : ℕ) :
    (∑ k ∈ Finset.range (n + 1), bernoulliMass p (k : ℤ) ^ q *
      ((mixingCoefficient p ((k + 1 : ℕ) : ℤ) - 1 / 2) ^ (2 * m) -
        (mixingCoefficient p (k : ℤ) - 1 / 2) ^ (2 * m))) ≤ 0 :=
  HarmonicSequence.moment_nonpos q hq₁ hq₂ (bernoulliHarmonicSequence p hp hpHalf) m

/-- The even kernel cancels the escort-power difference at a single adjacent
pair, including a vanishing individual mass and the equal-mass center. -/
theorem harmonicEvenKernel_mass_identity (q a b : ℝ) (hq : 0 < q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    (a ^ q - b ^ q) * harmonicEvenKernel q (a / (a + b) - 1 / 2) =
      (a - b) * (a + b) ^ (q - 1) := by
  have hs : a + b ≠ 0 := ne_of_gt hab
  by_cases he : a = b
  · simp [he]
  have hx : a / (a + b) - 1 / 2 ≠ 0 := by
    intro hz
    have hz' : a / (a + b) = 1 / 2 := sub_eq_zero.mp hz
    rw [div_eq_iff hs] at hz'
    exact he (by linarith)
  have hdiff : a ^ q - b ^ q ≠ 0 := by
    intro hz
    exact he ((Real.rpow_left_inj ha hb (ne_of_gt hq)).mp (sub_eq_zero.mp hz))
  have hpow : (a + b) ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hab q)
  have hp : 1 / 2 + (a / (a + b) - 1 / 2) = a / (a + b) := by ring
  have hm : 1 / 2 - (a / (a + b) - 1 / 2) = b / (a + b) := by field_simp; ring
  simp only [harmonicEvenKernel, hx, ↓reduceIte, hp, hm]
  rw [Real.div_rpow ha hab.le, Real.div_rpow hb hab.le, Real.rpow_sub hab, Real.rpow_one]
  field_simp
  ring

/-- The actual midpoint functional is the finite weighted increment of the
harmonic even kernel, after an exact summation by parts at both outer edges. -/
theorem midpointFunctional_eq_harmonicFunctional {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (q : ℝ) (hq : 0 < q) :
    midpointFunctional q p =
      (bernoulliHarmonicSequence p hp hpHalf).functional q (harmonicEvenKernel q) := by
  let F : ℕ → ℝ := fun k => harmonicEvenKernel q (mixingCoefficient p (k : ℤ) - 1 / 2)
  have hid (k : Fin (n + 2)) :
      edgeDifference p k * edgeSum p k ^ (q - 1) =
      (bernoulliMass p ((k.val : ℤ) - 1) ^ q - bernoulliMass p (k.val : ℤ) ^ q) * F k.val := by
    exact (harmonicEvenKernel_mass_identity q _ _ hq
      (bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => by linarith [hpHalf i]) _)
      (bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => by linarith [hpHalf i]) _)
      (edgeSum_pos p hp (fun i => by linarith [hpHalf i]) k)).symm
  simp only [midpointFunctional, hid, sub_mul, Finset.sum_sub_distrib]
  have hl : (∑ k : Fin (n + 2), bernoulliMass p ((k.val : ℤ) - 1) ^ q * F k.val) =
      ∑ k : Fin (n + 1), bernoulliMass p (k.val : ℤ) ^ q * F (k.val + 1) := by
    rw [Fin.sum_univ_succ]
    simp [Nat.cast_add, Nat.cast_one, Real.zero_rpow (ne_of_gt hq)]
  have hr : (∑ k : Fin (n + 2), bernoulliMass p (k.val : ℤ) ^ q * F k.val) =
      ∑ k : Fin (n + 1), bernoulliMass p (k.val : ℤ) ^ q * F k.val := by
    rw [Fin.sum_univ_castSucc]
    simp [Nat.cast_add, Nat.cast_one, Real.zero_rpow (ne_of_gt hq)]
  rw [hl, hr, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => bernoulliMass p (k : ℤ) ^ q * (F (k + 1) - F k)) (n + 1)

/-- Harmonic lowering resolves the actual midpoint sign throughout `[1,2]`
for every strictly positive half-cube Bernoulli parameter vector. -/
theorem midpointFunctional_nonpos_of_one_le_of_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) : midpointFunctional q p ≤ 0 := by
  rw [midpointFunctional_eq_harmonicFunctional p hp hpHalf q (by linarith)]
  exact HarmonicSequence.functional_harmonicEvenKernel_nonpos _ q hq₁ hq₂

/-- Continuity through support loss extends the harmonic midpoint sign to the
entire closed parameter half cube, including every zero-coin face. -/
theorem midpointFunctional_nonpos_of_one_le {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) : midpointFunctional q p ≤ 0 := by
  let pε : ℝ → Fin n → ℝ := fun ε i => (1 - ε) * p i + ε / 2
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with ε hε0 hε1
    exact ⟨hε0, hε1⟩
  have hpos (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (i : Fin n) : 0 < pε ε i := by
    dsimp [pε]
    have := mul_nonneg (show 0 ≤ 1 - ε by linarith) (hp i)
    linarith
  have hhalf (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (i : Fin n) : pε ε i ≤ 1 / 2 := by
    dsimp [pε]
    nlinarith [hpHalf i]
  have hpath : Continuous (fun ε : ℝ => (q, pε ε)) := by dsimp [pε]; fun_prop
  have hmap : Tendsto (fun ε : ℝ => (q, pε ε)) (𝓝[>] 0)
      (𝓝[{z : ℝ × (Fin n → ℝ) | 0 < z.1 ∧ ∀ i, z.2 i ∈ Set.Icc (0 : ℝ) (1 / 2)}] (q, p)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [pε] using (hpath.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    · filter_upwards [hε] with ε hε
      exact ⟨by linarith, fun i => ⟨(hpos ε hε.1 hε.2 i).le, hhalf ε hε.1.le hε.2.le i⟩⟩
  have hlim := (continuousOn_midpointFunctional_halfCube (q, p)
    (show (q, p) ∈ {z : ℝ × (Fin n → ℝ) | 0 < z.1 ∧ ∀ i, z.2 i ∈ Set.Icc (0 : ℝ) (1 / 2)}
      from ⟨by linarith, fun i => ⟨hp i, hpHalf i⟩⟩)).tendsto.comp hmap
  apply le_of_tendsto hlim
  filter_upwards [hε] with ε hε
  exact midpointFunctional_nonpos_of_one_le_of_pos (pε ε) (hpos ε hε.1 hε.2)
    (hhalf ε hε.1.le hε.2.le) q hq₁ hq₂

end RenyiMonotonicity
