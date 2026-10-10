module

public import RenyiMonotonicity.ContactFair
public import RenyiMonotonicity.ContactSingleton

/-! Exact coordinate selection and permutation transport for contact classification. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

lemma bernoulliMass_comp_equiv {n : ℕ} (p : Fin n → ℝ) (e : Equiv.Perm (Fin n)) (k : ℤ) :
    bernoulliMass (p ∘ e) k=bernoulliMass p k := by
  simp only [bernoulliMass,bernoulliPolynomial_comp_equiv]

lemma midpointFunctional_comp_equiv {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    midpointFunctional q (p ∘ e)=midpointFunctional q p := by
  simp only [midpointFunctional,edgeDifference,edgeSum,bernoulliMass_comp_equiv]

/-- An actual global half-cube minimum transports under any coordinate permutation. -/
lemma midpoint_min_comp_equiv {n : ℕ} (q : ℝ) (p : Fin n → ℝ) (e : Equiv.Perm (Fin n))
    (hmin : ∀ r : Fin n → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p≤ midpointFunctional q r) :
    ∀ r : Fin n → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (p ∘ e)≤ midpointFunctional q r := by
  intro r hr
  rw [midpointFunctional_comp_equiv]
  exact hmin r hr

/-- Any three distinct coordinate positions can be moved to the first three slots. -/
theorem exists_triple_reindex {m : ℕ} (p : Fin (m+3) → ℝ) (i j k : Fin (m+3))
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ∃ e : Equiv.Perm (Fin (m+3)), ∃ h : Fin m → ℝ,
      p ∘ e=tripleCoins (p i) (p j) (p k) h := by
  let f : Fin 3 → Fin (m+3) := fun s => ⟨s.val,by omega⟩
  let g : Fin 3 → Fin (m+3) := ![i,j,k]
  have hf : Function.Injective f := by intro a b he; apply Fin.ext; simpa only [f] using congrArg (fun s : Fin (m+3) => s.val) he
  have hg : Function.Injective g := by
    intro a b he
    fin_cases a <;> fin_cases b <;> simp_all [g,Ne.symm hij,Ne.symm hik,Ne.symm hjk]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let h := Fin.tail (Fin.tail (Fin.tail (p ∘ e)))
  refine ⟨e,h,?_⟩
  funext s
  refine Fin.cases ?_ (fun s => Fin.cases ?_ (fun s => Fin.cases ?_ (fun _ => rfl) s) s) s
  · change p (e (f 0))=p (g 0)
    rw [he 0]
  · change p (e (f 1))=p (g 1)
    rw [he 1]
  · change p (e (f 2))=p (g 2)
    rw [he 2]

/-- At an actual zero minimum, three interior coordinate values cannot be pairwise distinct. -/
theorem contact_three_interior_values {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hp : ∀ i, 0<p i) (hpHalf : ∀ i, p i≤1/2)
    (hzero : midpointFunctional q p=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p≤ midpointFunctional q r)
    (i j k : Fin (m+3)) (hi : p i<1/2) (hj : p j<1/2) (hk : p k<1/2) :
    p i=p j ∨ p i=p k ∨ p j=p k := by
  by_contra hn
  push Not at hn
  have hij : i≠j := fun h => hn.1 (congrArg p h)
  have hik : i≠k := fun h => hn.2.1 (congrArg p h)
  have hjk : j≠k := fun h => hn.2.2 (congrArg p h)
  obtain ⟨e,h,he⟩ := exists_triple_reindex p i j k hij hik hjk
  have hpos : ∀ t, 0<tripleCoins (p i) (p j) (p k) h t := by rw [← he]; exact fun t => hp (e t)
  have hhalf : ∀ t, tripleCoins (p i) (p j) (p k) h t≤1/2 := by rw [← he]; exact fun t => hpHalf (e t)
  have hmin' := midpoint_min_comp_equiv q p e hmin
  rw [he] at hmin'
  have hzero' : midpointFunctional q (tripleCoins (p i) (p j) (p k) h)=0 := by
    rw [← he,midpointFunctional_comp_equiv,hzero]
  have hs : ∀ s : Fin 3, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins (p i) (p j) (p k) h) (⟨s.val,by omega⟩ : Fin (m+3)) t))
      ((tripleCoins (p i) (p j) (p k) h) ⟨s.val,by omega⟩)=0 := by
    intro s
    apply midpoint_deriv_zero_of_min q _ (fun t => ⟨(hpos t).le,hhalf t⟩) _ (hpos _) _ hmin'
    fin_cases s
    · exact hi
    · exact hj
    · exact hk
  rcases no_three_distinct_stationary_cons q (p i) (p j) (p k) h hq0 hq1 hpos hhalf hzero' hs with H|H|H
  · exact hn.1 H
  · exact hn.2.1 H
  · exact hn.2.2 H

/-- Any other interior value lies below an actual repeated interior value. -/
theorem contact_repeated_value_dominates {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hp : ∀ i, 0<p i) (hpHalf : ∀ i, p i≤1/2)
    (hzero : midpointFunctional q p=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r)
    (i j k : Fin (m+3)) (hij : i≠j) (hval : p i=p j) (hne : p k≠p i)
    (hi : p i<1/2) (hk : p k<1/2) : p k<p i := by
  have hik : i≠k := fun H => hne (congrArg p H).symm
  have hjk : j≠k := fun H => hne ((congrArg p H).symm.trans hval.symm)
  obtain ⟨e,h,he⟩ := exists_triple_reindex p i j k hij hik hjk
  have hshape : p ∘ e=tripleCoins (p i) (p i) (p k) h := by simpa only [← hval] using he
  have hpos : ∀ t, 0<tripleCoins (p i) (p i) (p k) h t := by rw [← hshape]; exact fun t => hp (e t)
  have hhalf : ∀ t, tripleCoins (p i) (p i) (p k) h t≤1/2 := by rw [← hshape]; exact fun t => hpHalf (e t)
  have hmin' := midpoint_min_comp_equiv q p e hmin
  rw [hshape] at hmin'
  have hzero' : midpointFunctional q (tripleCoins (p i) (p i) (p k) h)=0 := by
    rw [← hshape,midpointFunctional_comp_equiv,hzero]
  have hs : ∀ s : Fin 3, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins (p i) (p i) (p k) h) (⟨s.val,by omega⟩ : Fin (m+3)) t))
      ((tripleCoins (p i) (p i) (p k) h) ⟨s.val,by omega⟩)=0 := by
    intro s
    apply midpoint_deriv_zero_of_min q _ (fun t => ⟨(hpos t).le,hhalf t⟩) _ (hpos _) _ hmin'
    fin_cases s
    · exact hi
    · exact hi
    · exact hk
  exact (stationary_singleton_lt_repeated q (p i) (p k) h hq0 hq1 (hp i) hi (hp k) (hpHalf k)
    (fun t => hpos t.succ.succ.succ) (fun t => hhalf t.succ.succ.succ) hne.symm hzero' hs hmin').1

/-- A fair coordinate leaves at most one interior coordinate at an actual zero minimum. -/
theorem contact_no_fair_two_interior {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hp : ∀ i, 0<p i) (hpHalf : ∀ i, p i≤1/2)
    (hzero : midpointFunctional q p=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r)
    (i j k : Fin (m+3)) (hij : i≠j) (hi : p i<1/2) (hj : p j<1/2) (hk : p k=1/2) : False := by
  have hik : i≠k := by intro H; rw [H,hk] at hi; exact (lt_irrefl _) hi
  have hjk : j≠k := by intro H; rw [H,hk] at hj; exact (lt_irrefl _) hj
  obtain ⟨e,h,he⟩ := exists_triple_reindex p i j k hij hik hjk
  rw [hk] at he
  have hpos : ∀ t, 0<tripleCoins (p i) (p j) (1/2) h t := by rw [← he]; exact fun t => hp (e t)
  have hhalf : ∀ t, tripleCoins (p i) (p j) (1/2) h t≤1/2 := by rw [← he]; exact fun t => hpHalf (e t)
  have hmin' := midpoint_min_comp_equiv q p e hmin
  rw [he] at hmin'
  have hzero' : midpointFunctional q (tripleCoins (p i) (p j) (1/2) h)=0 := by
    rw [← he,midpointFunctional_comp_equiv,hzero]
  by_cases hv : p i=p j
  · rw [← hv] at hmin' hzero'
    exact no_fair_repeated_contact q (p i) h hq0 hq1 (hp i) hi
      (fun t => hpos t.succ.succ.succ) (fun t => hhalf t.succ.succ.succ) hzero' hmin'
  · exact no_fair_distinct_contact q (p i) (p j) h hq0 hq1 (hp i) hi (hp j) hj hv
      (fun t => hpos t.succ.succ.succ) (fun t => hhalf t.succ.succ.succ) hzero' hmin'

end RenyiMonotonicity
