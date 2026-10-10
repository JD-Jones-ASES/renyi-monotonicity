module

public import RenyiMonotonicity.Gegenbauer
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

open Polynomial

namespace RenyiMonotonicity

/-- Increasing root angles, reversing the increasing real-root list. -/
noncomputable def RealRootList.angle {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (i : Fin n) : ℝ := Real.arccos (r.root i.rev)

theorem RealRootList.angle_mem {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (hr : ∀ j, -1 < r.root j ∧ r.root j < 1) (i : Fin n) :
    0 < r.angle i ∧ r.angle i < Real.pi :=
  ⟨Real.arccos_pos.mpr (hr _).2, Real.arccos_lt_pi.mpr (hr _).1⟩

theorem RealRootList.angle_strictMono {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (hr : ∀ j, -1 < r.root j ∧ r.root j < 1) : StrictMono r.angle := by
  intro i j hij
  exact Real.arccos_lt_arccos (hr _).1.le (r.increasing (Fin.rev_lt_rev.mpr hij)) (hr _).2.le

/-- Reversal under arccos preserves strict consecutive-family interlacing. -/
theorem RealRootList.angle_interlacing {P Q : ℝ[X]} {n : ℕ}
    (r : RealRootList P n) (s : RealRootList Q (n + 1))
    (hr : ∀ j, -1 < r.root j ∧ r.root j < 1)
    (hs : ∀ j, -1 < s.root j ∧ s.root j < 1)
    (hi : ∀ j : Fin n, s.root j.castSucc < r.root j ∧ r.root j < s.root j.succ)
    (j : Fin n) : s.angle j.castSucc < r.angle j ∧ r.angle j < s.angle j.succ := by
  simp only [RealRootList.angle, Fin.rev_castSucc, Fin.rev_succ]
  constructor
  · exact Real.arccos_lt_arccos (hr _).1.le (hi j.rev).2 (hs _).2.le
  · exact Real.arccos_lt_arccos (hs _).1.le (hi j.rev).1 (hr _).2.le

/-- Repeat a strictly interior angle list in consecutive half-periods. -/
noncomputable def periodicRootAngle {m : ℕ} (hm : 0 < m) (θ : Fin m → ℝ) (j : ℕ) : ℝ :=
  (j / m : ℕ) * Real.pi + θ ⟨j % m, Nat.mod_lt _ hm⟩

theorem periodicRootAngle_pos {m : ℕ} (hm : 0 < m) (θ : Fin m → ℝ)
    (hθ : ∀ i, 0 < θ i) (j : ℕ) : 0 < periodicRootAngle hm θ j := by
  unfold periodicRootAngle
  exact add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le) (hθ _)

theorem periodicRootAngle_strictMono {m : ℕ} (hm : 0 < m) (θ : Fin m → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ Real.pi) (hθm : StrictMono θ) :
    StrictMono (periodicRootAngle hm θ) := by
  intro i j hij
  have hd : i / m ≤ j / m := Nat.div_le_div_right hij.le
  by_cases he : i / m = j / m
  · have hr : i % m < j % m := by
      have hi := Nat.mod_add_div i m
      have hj := Nat.mod_add_div j m
      rw [he] at hi
      omega
    dsimp [periodicRootAngle]
    rw [he]
    linarith [hθm (show (⟨i % m, Nat.mod_lt _ hm⟩ : Fin m) < ⟨j % m, Nat.mod_lt _ hm⟩ from hr)]
  · have hlt : i / m + 1 ≤ j / m := by omega
    have hc : ((i / m : ℕ) : ℝ) + 1 ≤ (j / m : ℕ) := by exact_mod_cast hlt
    have hp := mul_le_mul_of_nonneg_right hc Real.pi_pos.le
    dsimp [periodicRootAngle]
    nlinarith [(hθ ⟨i % m, Nat.mod_lt _ hm⟩).2, (hθ ⟨j % m, Nat.mod_lt _ hm⟩).1]

/-- A list with two additional angles per half-period dominates the shorter
list from below once its first angles interlace. This is a literal counting
argument, valid for every zero index. -/
theorem periodicRootAngle_domination {m : ℕ} (hm : 0 < m)
    (θ : Fin m → ℝ) (φ : Fin (m + 2) → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i < Real.pi)
    (hφ : ∀ i, 0 < φ i ∧ φ i ≤ Real.pi) (hφm : Monotone φ)
    (hinter : ∀ i : Fin m, φ ⟨i.val, by omega⟩ ≤ θ i) (j : ℕ) :
    periodicRootAngle (by omega : 0 < m + 2) φ j ≤ periodicRootAngle hm θ j := by
  have hdiv : j / (m + 2) ≤ j / m := Nat.div_le_div_left (by omega : m ≤ m + 2) hm
  by_cases he : j / (m + 2) = j / m
  · have hi := Nat.mod_add_div j m
    have hj := Nat.mod_add_div j (m + 2)
    rw [he] at hj
    have hr : j % (m + 2) ≤ j % m := by
      rw [Nat.add_mul] at hj
      omega
    have hφr := hφm (show (⟨j % (m + 2), Nat.mod_lt _ (by omega)⟩ : Fin (m + 2)) ≤
        ⟨j % m, by have := Nat.mod_lt j hm; omega⟩ from hr)
    have hi' := hinter ⟨j % m, Nat.mod_lt _ hm⟩
    dsimp [periodicRootAngle]
    rw [he]
    linarith [hφr.trans hi']
  · have hd : j / (m + 2) + 1 ≤ j / m := by omega
    have hc : ((j / (m + 2) : ℕ) : ℝ) + 1 ≤ (j / m : ℕ) := by exact_mod_cast hd
    have hp := mul_le_mul_of_nonneg_right hc Real.pi_pos.le
    dsimp [periodicRootAngle]
    nlinarith [(hφ ⟨j % (m + 2), Nat.mod_lt _ (by omega)⟩).2,
      (hθ ⟨j % m, Nat.mod_lt _ hm⟩).1]

/-- Append the sine zero at the right endpoint of a half-period. -/
noncomputable def RealRootList.sineAngle {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (i : Fin (n + 1)) : ℝ := if h : i.val < n then r.angle ⟨i.val, h⟩ else Real.pi

theorem RealRootList.sineAngle_mem {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (hr : ∀ j, -1 < r.root j ∧ r.root j < 1) (i : Fin (n + 1)) :
    0 < r.sineAngle i ∧ r.sineAngle i ≤ Real.pi := by
  dsimp [sineAngle]
  split_ifs
  · exact ⟨(r.angle_mem hr _).1, (r.angle_mem hr _).2.le⟩
  · exact ⟨Real.pi_pos, le_rfl⟩

theorem RealRootList.sineAngle_strictMono {P : ℝ[X]} {n : ℕ} (r : RealRootList P n)
    (hr : ∀ j, -1 < r.root j ∧ r.root j < 1) : StrictMono r.sineAngle := by
  intro i j hij
  have hi : i.val < n := by omega
  simp only [sineAngle, hi, ↓reduceDIte]
  split_ifs with hj
  · exact r.angle_strictMono hr (show (⟨i.val, hi⟩ : Fin n) < ⟨j.val, hj⟩ from hij)
  · exact (r.angle_mem hr _).2

/-- Actual Gegenbauer interlacing orders every repeated positive zero angle
of the `F` and `G` factors, without any finite census. -/
theorem gegenbauer_periodic_angle_domination (a : ℝ) (ha : 0 < a)
    (m : ℕ) (hm : 0 < m) :
    ∃ r : RealRootList (monicGegenbauer a m) m,
    ∃ s : RealRootList (monicGegenbauer a (m + 1)) (m + 1),
      (∀ i, -1 < r.root i ∧ r.root i < 1) ∧
      (∀ i, -1 < s.root i ∧ s.root i < 1) ∧
      StrictMono (periodicRootAngle hm r.angle) ∧
      StrictMono (periodicRootAngle (by omega : 0 < m + 2) s.sineAngle) ∧
      (∀ j, 0 < periodicRootAngle (by omega : 0 < m + 2) s.sineAngle j ∧
        periodicRootAngle (by omega : 0 < m + 2) s.sineAngle j ≤ periodicRootAngle hm r.angle j) := by
  obtain ⟨r, s, hr, hs, hi⟩ := monicGegenbauer_interlacing a ha m
  refine ⟨r, s, hr, hs,
    periodicRootAngle_strictMono hm r.angle (fun i => ⟨(r.angle_mem hr i).1, (r.angle_mem hr i).2.le⟩)
      (r.angle_strictMono hr),
    periodicRootAngle_strictMono (by omega) s.sineAngle (s.sineAngle_mem hs)
      (s.sineAngle_strictMono hs), ?_⟩
  intro j
  refine ⟨periodicRootAngle_pos _ s.sineAngle (fun i => (s.sineAngle_mem hs i).1) j,
    periodicRootAngle_domination hm r.angle s.sineAngle (r.angle_mem hr) (s.sineAngle_mem hs)
      (s.sineAngle_strictMono hs).monotone ?_ j⟩
  intro i
  have H := r.angle_interlacing s hr hs hi i
  change s.sineAngle ⟨i.val, _⟩ ≤ r.angle i
  simp only [RealRootList.sineAngle, show i.val < m + 1 by omega, dite_eq_left]
  have hi : (⟨i.val, by omega⟩ : Fin (m + 1)) = i.castSucc := by ext; rfl
  rw [hi]
  exact H.1.le

/-- Every angle in the smaller repeated list is a zero of the actual
Gegenbauer cosine composition. -/
theorem monicGegenbauer_periodic_angle_zero (a : ℝ) (m : ℕ) (hm : 0 < m)
    (r : RealRootList (monicGegenbauer a m) m)
    (hr : ∀ i, -1 < r.root i ∧ r.root i < 1) (j : ℕ) :
    (monicGegenbauer a m).eval (Real.cos (periodicRootAngle hm r.angle j)) = 0 := by
  rw [periodicRootAngle, add_comm, Real.cos_add_nat_mul_pi]
  simp only [RealRootList.angle, Real.cos_arccos (hr _).1.le (hr _).2.le]
  rcases neg_one_pow_eq_or ℝ (j / m) with h | h
  · rw [h, one_mul]
    exact r.isRoot _
  · rw [h, neg_one_mul, monicGegenbauer_eval_neg, r.isRoot, mul_zero]

end RenyiMonotonicity
