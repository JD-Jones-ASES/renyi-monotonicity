module
public import RenyiMonotonicity.ShannonStrict
public import RenyiMonotonicity.NormalizedCalculus
public import RenyiMonotonicity.MidpointSymmetry
public import RenyiMonotonicity.ContactLocalMin

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RenyiMonotonicity

theorem shannon_midpoint_ge_first_gap {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) :
    (2 / 3) * (bernoulliMass p 0 * (1 - mixingCoefficient p 1)) *
      ((mixingCoefficient p 1 - mixingCoefficient p 0) -
        (mixingCoefficient p 2 - mixingCoefficient p 1)) ≤ normalizedMidpointFunctional 1 p := by
  let s := bernoulliHarmonicSequence p hp hpHalf
  have hfirst : s.moment 1 1 ≤ s.lower.mass 0 * (s.gap 1 - s.gap 0) := by
    rw [HarmonicSequence.moment_one_one_eq, Finset.sum_range_succ']
    have htail : (∑ k ∈ Finset.range n, s.lower.mass (k + 1) * (s.gap (k + 1 + 1) - s.gap (k + 1))) ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      exact mul_nonpos_of_nonneg_of_nonpos (s.lower.mass_pos (k + 1) (by omega)).le
        (sub_nonpos.mpr (s.gap_antitone (by omega) (by omega)))
    linarith
  have hb := normalizedMidpointFunctional_one_ge_cubic p hp hpHalf
  have hbound : -(2 / 3) * (s.lower.mass 0 * (s.gap 1 - s.gap 0)) ≤ normalizedMidpointFunctional 1 p := by
    dsimp [s] at hfirst ⊢
    linarith
  simp only [HarmonicSequence.lower_mass, HarmonicSequence.gap, s,
    bernoulliHarmonicSequence_mass, bernoulliHarmonicSequence_node,
    Nat.cast_zero, Nat.cast_one, zero_add, one_add_one_eq_two, Nat.cast_ofNat] at hbound
  nlinarith

def shannonFairWeight (n : ℕ) (t : ℝ) : ℝ :=
  let p := Fin.cons t (fun _ : Fin n => (1 / 2 : ℝ))
  (2 / 3) * bernoulliMass p 1 * t * (1 - t) *
    bernoulliMass (fun _ : Fin n => (1 / 2 : ℝ)) 0 ^ 3 /
    ((bernoulliMass p 0 + bernoulliMass p 1) ^ 2 * (bernoulliMass p 1 + bernoulliMass p 2))

theorem shannon_cons_fair_lower (n : ℕ) (t : ℝ) (ht : 0 < t) (htHalf : t ≤ 1 / 2) :
    (1 - 2 * t) * shannonFairWeight n t ≤
      normalizedMidpointFunctional 1 (Fin.cons t (fun _ : Fin n => (1 / 2 : ℝ))) := by
  let b := fun _ : Fin n => (1 / 2 : ℝ)
  let p : Fin (n + 1) → ℝ := Fin.cons t b
  have hp : ∀ i, 0 < p i := by intro i; refine Fin.cases ht (fun _ => by norm_num [p, b]) i
  have hpHalf : ∀ i, p i ≤ 1 / 2 := by intro i; refine Fin.cases htHalf (fun _ => le_rfl) i
  have hp1 : ∀ i, p i < 1 := fun i => by linarith [hpHalf i]
  have hg0 := bernoulliMass_pos p hp hp1 0 (by omega) (by omega)
  have hg1 := bernoulliMass_pos p hp hp1 1 (by omega) (by omega)
  have hg2 := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) 2
  have hgap := mixingCoefficient_curvature_identity_of_pos p hp hp1 0 (by omega) (by omega)
  have hsum : (∑ i, p i * (1 - p i) * (1 - 2 * p i) * omittedToeplitzCubic p i 0) =
      t * (1 - t) * (1 - 2 * t) * bernoulliMass b 0 ^ 3 := by
    rw [Fin.sum_univ_succ]
    simp [p, b, omittedToeplitzCubic_zero, omitCoin]
  rw [hsum] at hgap
  norm_num only [zero_add, bernoulliMass_outer_left, add_zero, zero_sub] at hgap
  have hb := shannon_midpoint_ge_first_gap p hp hpHalf
  rw [hgap] at hb
  have he : (1 - 2 * t) * shannonFairWeight n t =
      (2 / 3) * (bernoulliMass p 0 * (1 - mixingCoefficient p 1)) *
        (t * (1 - t) * (1 - 2 * t) * bernoulliMass b 0 ^ 3 /
          (bernoulliMass p 0 * (bernoulliMass p 0 + bernoulliMass p 1) *
            (bernoulliMass p 1 + bernoulliMass p 2))) := by
    change (1 - 2 * t) * ((2 / 3) * bernoulliMass p 1 * t * (1 - t) * bernoulliMass b 0 ^ 3 /
      ((bernoulliMass p 0 + bernoulliMass p 1) ^ 2 * (bernoulliMass p 1 + bernoulliMass p 2))) =
      (2 / 3) * (bernoulliMass p 0 * (1 - bernoulliMass p 0 / (bernoulliMass p 0 + bernoulliMass p 1))) *
        (t * (1 - t) * (1 - 2 * t) * bernoulliMass b 0 ^ 3 /
          (bernoulliMass p 0 * (bernoulliMass p 0 + bernoulliMass p 1) * (bernoulliMass p 1 + bernoulliMass p 2)))
    field_simp [hg0.ne', (add_pos hg0 hg1).ne', (add_pos_of_pos_of_nonneg hg1 hg2).ne']
    ring
  rw [he]
  exact hb

theorem shannonFairWeight_pos (n : ℕ) : 0 < shannonFairWeight n (1 / 2) := by
  let b : Fin n → ℝ := fun _ => 1 / 2
  let p : Fin (n + 1) → ℝ := Fin.cons (1 / 2) b
  have hp : ∀ i, 0 < p i := by intro i; refine Fin.cases (by norm_num [p, b]) (fun _ => by norm_num [p, b]) i
  have hp1 : ∀ i, p i < 1 := by intro i; refine Fin.cases (by norm_num [p, b]) (fun _ => by norm_num [p, b]) i
  have h₀ := bernoulliMass_pos p hp hp1 0 (by omega) (by omega)
  have h₁ := bernoulliMass_pos p hp hp1 1 (by omega) (by omega)
  have h₂ := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) 2
  have hb := bernoulliMass_pos b (fun _ => by norm_num [b]) (fun _ => by norm_num [b]) 0 (by omega) (by omega)
  change 0 < (2 / 3) * bernoulliMass p 1 * (1 / 2) * (1 - 1 / 2) * bernoulliMass b 0 ^ 3 /
    ((bernoulliMass p 0 + bernoulliMass p 1) ^ 2 * (bernoulliMass p 1 + bernoulliMass p 2))
  positivity

theorem differentiableAt_shannonFairWeight (n : ℕ) : DifferentiableAt ℝ (shannonFairWeight n) (1 / 2) := by
  let b : Fin n → ℝ := fun _ => 1 / 2
  let p : Fin (n + 1) → ℝ := Fin.cons (1 / 2) b
  have hp : ∀ i, 0 < p i := by intro i; refine Fin.cases (by norm_num [p, b]) (fun _ => by norm_num [p, b]) i
  have hp1 : ∀ i, p i < 1 := by intro i; refine Fin.cases (by norm_num [p, b]) (fun _ => by norm_num [p, b]) i
  have h₀ := bernoulliMass_pos p hp hp1 0 (by omega) (by omega)
  have h₁ := bernoulliMass_pos p hp hp1 1 (by omega) (by omega)
  have h₂ := bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le) 2
  have hd (k : ℤ) : DifferentiableAt ℝ (fun t => bernoulliMass (Fin.cons t b) k) (1 / 2) := by
    simp only [bernoulliMass_cons]
    fun_prop
  exact (((((hd 1).const_mul (2 / 3)).mul differentiableAt_id).mul
    (differentiableAt_const (1 : ℝ) |>.sub differentiableAt_id)).mul_const (bernoulliMass b 0 ^ 3)).div
    (((hd 0).add (hd 1)).pow 2 |>.mul ((hd 1).add (hd 2))) (by change (bernoulliMass p 0 + bernoulliMass p 1) ^ 2 * (bernoulliMass p 1 + bernoulliMass p 2) ≠ 0; positivity)

/-- Every coordinate of the normalized Shannon midpoint has strictly negative
derivative at the fair vector. The lower bound is a single actual cubic-gap
term, so the proof uses no order-one infinite-series derivative. -/
theorem normalizedCoinDerivative_all_half_one_neg (n : ℕ) (i : Fin (n + 1)) :
    normalizedCoinDerivative 1 (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) i < 0 := by
  let b : Fin n → ℝ := fun _ => 1 / 2
  let v : Fin (n + 1) → ℝ := fun _ => 1 / 2
  let D := normalizedCoinDerivative 1 v i
  have he (t : ℝ) : normalizedMidpointFunctional 1 (Function.update v i t) =
      normalizedMidpointFunctional 1 (Fin.cons t b) := by
    have hpoly : bernoulliPolynomial (Function.update v i t) = bernoulliPolynomial (Fin.cons t b) := by
      rw [bernoulliPolynomial_update_eq_cons]
      rfl
    simp only [normalizedMidpointFunctional, edgeDifference, edgeSum, bernoulliMass, hpoly]
  have hJ : HasDerivAt (fun t => normalizedMidpointFunctional 1 (Fin.cons t b)) D (1 / 2) := by
    have h := hasDerivAt_normalizedMidpointFunctional_update 1 v i
      (edgeSum_pos v (fun _ => by norm_num [v]) (fun _ => by norm_num [v]))
    simpa only [he] using h
  have hφ : HasDerivAt (fun t : ℝ => 1 / 2 - t) (-1) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 / 2 : ℝ)).sub (hasDerivAt_id 0) using 1 <;> simp
    rfl
  let f := fun t : ℝ => normalizedMidpointFunctional 1 (Fin.cons (1 / 2 - t) b) -
    (2 * t) * shannonFairWeight n (1 / 2 - t)
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
    convert (hasDerivAt_id (0 : ℝ)).const_mul 2 using 1 <;> simp
  have hf : HasDerivAt f (-D - 2 * shannonFairWeight n (1 / 2)) 0 := by
    have hj := (show HasDerivAt _ D ((1 / 2 : ℝ) - 0) by simpa using hJ).comp 0 hφ
    have hw := (show HasDerivAt (shannonFairWeight n) (deriv (shannonFairWeight n) (1 / 2)) ((1 / 2 : ℝ) - 0) by
      simpa using (differentiableAt_shannonFairWeight n).hasDerivAt).comp 0 hφ
    convert hj.sub (hlin.mul hw) using 1 <;> simp [f]
    rfl
  have hv : Fin.cons (1 / 2) b = v := by funext j; exact Fin.cases rfl (fun _ => rfl) j
  have hf0 : f 0 = 0 := by
    dsimp only [f]
    rw [sub_zero, mul_zero, zero_mul, sub_zero, hv]
    exact normalizedMidpointFunctional_all_half (n + 1) 1
  have hmin : ∀ᶠ t : ℝ in 𝓝[>] 0, f 0 ≤ f t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds] with t ht hth
    have ht0 : 0 < t := ht
    have hh := shannon_cons_fair_lower n (1 / 2 - t) (by linarith) (by linarith)
    rw [hf0]
    dsimp [f, b]
    have heq : (1 : ℝ) - 2 * (1 / 2 - t) = 2 * t := by ring
    rw [heq] at hh
    linarith
  have hh := hasDerivAt_nonneg_of_right_min hf hmin
  have hw := shannonFairWeight_pos n
  dsimp [D, v] at hh
  linarith

end RenyiMonotonicity
