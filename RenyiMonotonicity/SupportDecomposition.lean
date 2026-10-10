module

public import RenyiMonotonicity.ContactSelection
public import RenyiMonotonicity.BoundaryEstimate

/-! Fixed coordinate decompositions into a positive active core and a zero block. -/

@[expose] public section
noncomputable section
open Filter Topology

namespace RenyiMonotonicity

/-- Normalized midpoint values are invariant under coordinate permutations at every order, including one. -/
theorem normalizedMidpointFunctional_comp_equiv {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) :
    normalizedMidpointFunctional q (p ∘ e)=normalizedMidpointFunctional q p := by
  simp only [normalizedMidpointFunctional,edgeDifference,edgeSum,bernoulliMass_comp_equiv]

/-- The same invariance is available when the two finite dimensions are propositionally equal. -/
theorem normalizedMidpointFunctional_comp_finiteEquiv {m n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (e : Fin m ≃ Fin n) :
    normalizedMidpointFunctional q (p ∘ e)=normalizedMidpointFunctional q p := by
  have hmn : m=n := by simpa using Fintype.card_congr e
  subst n
  exact normalizedMidpointFunctional_comp_equiv q p e

/-- Fixed reindexing followed by selection of the first block is continuous. -/
theorem continuous_reindexed_core {m k n : ℕ} (e : Fin (m+k) ≃ Fin n) :
    Continuous (fun r : Fin n → ℝ => fun i : Fin m => r (e (Fin.castAdd k i))) := by
  exact continuous_pi (fun i => continuous_apply _)

/-- Fixed reindexing followed by selection of the second block is continuous. -/
theorem continuous_reindexed_tail {m k n : ℕ} (e : Fin (m+k) ≃ Fin n) :
    Continuous (fun r : Fin n → ℝ => fun i : Fin k => r (e (Fin.natAdd m i))) := by
  exact continuous_pi (fun i => continuous_apply _)

/-- Every vector has its exact append decomposition along any fixed reindexing. -/
theorem reindexed_append {m k n : ℕ} (e : Fin (m+k) ≃ Fin n) (r : Fin n → ℝ) :
    r ∘ e = Fin.append (fun i : Fin m => r (e (Fin.castAdd k i)))
      (fun i : Fin k => r (e (Fin.natAdd m i))) := Fin.append_castAdd_natAdd.symm

/-- A nonnegative vector with a zero coordinate has a strictly smaller positive core
and a nonempty zero block, selected by one fixed finite equivalence. -/
theorem exists_positive_core_zero_tail {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0≤p i) (hzero : ∃ i, p i=0) :
    ∃ m k : ℕ, m+k=n ∧ m<n ∧ 0<k ∧ ∃ e : Fin (m+k) ≃ Fin n,
      (∀ i : Fin m, 0<p (e (Fin.castAdd k i))) ∧
      (∀ i : Fin k, p (e (Fin.natAdd m i))=0) := by
  classical
  let A := {i : Fin n // 0<p i}
  let Z := {i : Fin n // ¬0<p i}
  let m := Fintype.card A
  let k := Fintype.card Z
  let ea : Fin m ≃ A := (Fintype.equivFin A).symm
  let ez : Fin k ≃ Z := (Fintype.equivFin Z).symm
  let e : Fin (m+k) ≃ Fin n := finSumFinEquiv.symm.trans ((Equiv.sumCongr ea ez).trans (Equiv.sumCompl (fun i => 0<p i)))
  have hdim : m+k=n := by simpa using Fintype.card_congr e
  have hk : 0<k := by
    obtain ⟨i,hi⟩ := hzero
    have : Nonempty Z := ⟨⟨i,by rw [hi]; exact lt_irrefl _⟩⟩
    exact Fintype.card_pos
  refine ⟨m,k,hdim,by omega,hk,e,?_,?_⟩
  · intro i
    simp only [e,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.sumCongr_apply,Sum.map_inl]
    rw [Equiv.sumCompl_apply_inl]
    exact (ea i).property
  · intro i
    simp only [e,Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Sum.map_inr]
    rw [Equiv.sumCompl_apply_inr]
    exact le_antisymm (le_of_not_gt (ez i).property) (hp _)

/-- Every order at a zero-face point equals the value on its strictly smaller active core. -/
theorem normalizedMidpointFunctional_eq_active_core {m k n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (e : Fin (m+k) ≃ Fin n) (hzero : ∀ i : Fin k, p (e (Fin.natAdd m i))=0) :
    normalizedMidpointFunctional q p =
      normalizedMidpointFunctional q (fun i : Fin m => p (e (Fin.castAdd k i))) := by
  rw [← normalizedMidpointFunctional_comp_finiteEquiv q p e,reindexed_append]
  exact normalizedMidpointFunctional_append_zero q _ _ hzero

/-- A fixed active core remains uniformly positive in a neighborhood of its base vector. -/
theorem eventually_reindexed_core_pos {m k n : ℕ} (p : Fin n → ℝ) (e : Fin (m+k) ≃ Fin n)
    (hpos : ∀ i : Fin m, 0<p (e (Fin.castAdd k i))) :
    ∀ᶠ r in 𝓝 p, ∀ i : Fin m, p (e (Fin.castAdd k i))/2 < r (e (Fin.castAdd k i)) := by
  rw [Filter.eventually_all]
  intro i
  exact (continuous_apply (e (Fin.castAdd k i))).continuousAt.eventually (eventually_gt_nhds (by linarith [hpos i]))

end RenyiMonotonicity
