module

public import RenyiMonotonicity.HarmonicBernoulli
public import RenyiMonotonicity.InverseScore

@[expose] public section

namespace RenyiMonotonicity

namespace HarmonicSequence

/-- Summing bounded adjacent increments bounds every longer chord. -/
theorem chord_le_of_gap_le {n : ℕ} (s : HarmonicSequence n)
    {i j : ℕ} (hij : i ≤ j) (g : ℝ)
    (hg : ∀ k, i ≤ k → k < j → s.gap k ≤ g) :
    s.node j - s.node i ≤ ((j : ℝ) - i) * g := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h₁ := ih (fun k hi hk => hg k hi (by omega))
    have h₂ := hg j hij (by omega)
    dsimp [gap] at h₂
    push_cast
    nlinarith

/-- The companion lower chord estimate. -/
theorem chord_ge_of_le_gap {n : ℕ} (s : HarmonicSequence n)
    {i j : ℕ} (hij : i ≤ j) (g : ℝ)
    (hg : ∀ k, i ≤ k → k < j → g ≤ s.gap k) :
    ((j : ℝ) - i) * g ≤ s.node j - s.node i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have h₁ := ih (fun k hi hk => hg k hi (by omega))
    have h₂ := hg j hij (by omega)
    dsimp [gap] at h₂
    push_cast
    nlinarith

/-- Concave adjacent gaps imply the exact three-point chord inequality. -/
theorem chord_concavity {n : ℕ} (s : HarmonicSequence n)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k ≤ n + 1) :
    ((j : ℝ) - i) * (s.node k - s.node j) ≤
      ((k : ℝ) - j) * (s.node j - s.node i) := by
  have h₁ := s.chord_ge_of_le_gap hij.le (s.gap j) (fun l hi hl =>
    s.gap_antitone (by omega : l ≤ j) (by omega))
  have h₂ := s.chord_le_of_gap_le hjk.le (s.gap j) (fun l hj hl =>
    s.gap_antitone hj (by omega))
  have hij' : 0 ≤ (j : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hij.le)
  have hjk' : 0 ≤ (k : ℝ) - j := sub_nonneg.mpr (by exact_mod_cast hjk.le)
  have h₃ := mul_le_mul_of_nonneg_left h₂ hij'
  have h₄ := mul_le_mul_of_nonneg_left h₁ hjk'
  nlinarith

/-- A strictly increasing concave grid has an increasing convex inverse on
its sampled points. The center of the position coordinate is immaterial. -/
theorem increasingSecants {n : ℕ} (s : HarmonicSequence n) (c : ℝ) :
    IncreasingSecants (fun k : Fin (n + 2) => 2 * s.node k.val - 1)
      (fun k => (k.val : ℝ) - c) where
  nonneg i j hij := by
    have hy := s.node_strict (show i.val < j.val from hij) (by omega)
    dsimp [secantSlope]
    apply div_nonneg
    · have : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij.le
      linarith
    · linarith
  left_mono i i' j hii hij := by
    by_cases he : i = i'
    · subst i'; rfl
    have hii' : i.val < i'.val := lt_of_le_of_ne hii (fun h => he (Fin.ext h))
    have hy₁ := s.node_strict hii' (by omega)
    have hy₂ := s.node_strict (show i'.val < j.val from hij) (by omega)
    have hc := s.chord_concavity hii' (show i'.val < j.val from hij) (by omega)
    dsimp [secantSlope]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  right_mono i j j' hij hjj := by
    by_cases he : j = j'
    · subst j'; rfl
    have hjj' : j.val < j'.val := lt_of_le_of_ne hjj (fun h => he (Fin.ext h))
    have hy₁ := s.node_strict (show i.val < j.val from hij) (by omega)
    have hy₂ := s.node_strict hjj' (by omega)
    have hc := s.chord_concavity (show i.val < j.val from hij) hjj' (by omega)
    dsimp [secantSlope]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

end HarmonicSequence

/-- The actual normalized adjacent-mass score. -/
noncomputable def bernoulliMixingScore {n : ℕ} (p : Fin n → ℝ)
    (k : Fin (n + 2)) : ℝ := 2 * mixingCoefficient p (k.val : ℤ) - 1

theorem bernoulliMixingScore_eq_edgeRatio {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (k : Fin (n + 2)) :
    bernoulliMixingScore p k = edgeDifference p k / edgeSum p k := by
  have hs := (edgeSum_pos p hp (fun i => by linarith [hpHalf i]) k).ne'
  dsimp [bernoulliMixingScore, mixingCoefficient, edgeDifference, edgeSum] at *
  field_simp
  ring

theorem bernoulliMixingScore_strictMono {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) :
    StrictMono (bernoulliMixingScore p) := by
  intro i j hij
  have h := (bernoulliHarmonicSequence p hp hpHalf).node_strict
    (show i.val < j.val from hij) (by omega)
  change mixingCoefficient p i.val < mixingCoefficient p j.val at h
  dsimp [bernoulliMixingScore]
  linarith

theorem bernoulliMixingScore_mem_Icc {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (k : Fin (n + 2)) :
    -1 ≤ bernoulliMixingScore p k ∧ bernoulliMixingScore p k ≤ 1 := by
  have h₀ := (bernoulliHarmonicSequence p hp hpHalf).node_nonneg (k := k.val) (by omega)
  have h₁ := (bernoulliHarmonicSequence p hp hpHalf).node_le_one (k := k.val) (by omega)
  change 0 ≤ mixingCoefficient p k.val at h₀
  change mixingCoefficient p k.val ≤ 1 at h₁
  dsimp [bernoulliMixingScore]
  constructor <;> linarith

/-- The inverse-score association hypothesis for the literal Bernoulli count
law, with every structural premise discharged on the positive half cube. -/
theorem bernoulliMixingScore_increasingSecants {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) (c : ℝ) :
    IncreasingSecants (bernoulliMixingScore p) (fun k => (k.val : ℝ) - c) :=
  (bernoulliHarmonicSequence p hp hpHalf).increasingSecants c

end RenyiMonotonicity
