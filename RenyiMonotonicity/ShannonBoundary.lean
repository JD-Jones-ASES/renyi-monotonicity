module
public import RenyiMonotonicity.ShannonStrict
public import RenyiMonotonicity.SupportDecomposition
public import RenyiMonotonicity.MidpointSymmetry

@[expose] public section
noncomputable section
open Set
namespace RenyiMonotonicity

/-- The normalized Shannon midpoint is nonnegative on every closed half cube,
including all zero-coordinate faces. -/
theorem normalizedMidpointFunctional_one_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Icc (0:ℝ) (1/2)) :
    0 ≤ normalizedMidpointFunctional 1 p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : ∃ i, p i = 0
    · obtain ⟨m,k,hdim,hmn,hk,e,hpos,hzero⟩ :=
        exists_positive_core_zero_tail p (fun i => (hp i).1) hz
      rw [normalizedMidpointFunctional_eq_active_core 1 p e hzero]
      exact ih m hmn _ (fun i => hp _)
    · have hpos : ∀ i, 0 < p i := fun i =>
        lt_of_le_of_ne (hp i).1 (Ne.symm (fun he => hz ⟨i,he⟩))
      by_cases hbiased : ∃ i, p i < 1/2
      · exact (normalizedMidpointFunctional_one_pos p hpos (fun i => (hp i).2) hbiased).le
      · have hall : p = fun _ => (1/2:ℝ) := by
          funext i
          exact le_antisymm (hp i).2 (le_of_not_gt (fun hi => hbiased ⟨i,hi⟩))
        rw [hall,normalizedMidpointFunctional_all_half]

end RenyiMonotonicity
