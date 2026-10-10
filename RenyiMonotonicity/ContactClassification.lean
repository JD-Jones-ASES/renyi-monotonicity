module

public import RenyiMonotonicity.ContactSelection

/-! Finite parameter classification at an actual zero minimum. -/

@[expose] public section
noncomputable section

namespace RenyiMonotonicity

/-- On the open half cube, an actual zero minimum is constant or has one lower exceptional parameter. -/
theorem contact_interior_parameter_pattern {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hp : ∀ i, 0<p i) (hpHalf : ∀ i, p i<1/2)
    (hzero : midpointFunctional q p=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    (∃ b : ℝ, 0<b ∧ b<1/2 ∧ ∀ i, p i=b) ∨
    (∃ i : Fin (m+3), ∃ a b : ℝ, 0<a ∧ a<b ∧ b<1/2 ∧ p i=a ∧ ∀ j, j≠i → p j=b) := by
  have hhalf : ∀ i, p i≤1/2 := fun i => (hpHalf i).le
  have hd := contact_three_interior_values q p hq0 hq1 hp hhalf hzero hmin 0 1 2
    (hpHalf 0) (hpHalf 1) (hpHalf 2)
  obtain ⟨i,j,hij,hval⟩ : ∃ i j : Fin (m+3), i≠j ∧ p i=p j := by
    rcases hd with H|H|H
    · exact ⟨0,1,by norm_num [Fin.ext_iff, Nat.mod_eq_of_lt (show 1 < m+3 by omega)],H⟩
    · exact ⟨0,2,by norm_num [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m+3 by omega)],H⟩
    · exact ⟨1,2,by norm_num [Fin.ext_iff, Nat.mod_eq_of_lt (show 1 < m+3 by omega), Nat.mod_eq_of_lt (show 2 < m+3 by omega)],H⟩
  by_cases hall : ∀ k, p k=p i
  · exact Or.inl ⟨p i,hp i,hpHalf i,hall⟩
  · push Not at hall
    obtain ⟨k,hk⟩ := hall
    have hki := contact_repeated_value_dominates q p hq0 hq1 hp hhalf hzero hmin i j k hij hval hk
      (hpHalf i) (hpHalf k)
    refine Or.inr ⟨k,p k,p i,hp k,hki,hpHalf i,rfl,?_⟩
    intro l hlk
    by_contra hli
    have hkl := contact_three_interior_values q p hq0 hq1 hp hhalf hzero hmin i k l
      (hpHalf i) (hpHalf k) (hpHalf l)
    have hsame : p k=p l := by
      rcases hkl with H|H|H
      · exact False.elim (hk H.symm)
      · exact False.elim (hli H.symm)
      · exact H
    have hik := contact_repeated_value_dominates q p hq0 hq1 hp hhalf hzero hmin k l i hlk.symm hsame hk.symm
      (hpHalf k) (hpHalf i)
    exact (lt_asymm hki hik)

/-- On the closed positive half cube, only a constant law or a single lower exception can occur.
The possible fair repeated level is the exact one-biased-plus-fair case. -/
theorem contact_parameter_pattern {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hp : ∀ i, 0<p i) (hpHalf : ∀ i, p i≤1/2)
    (hzero : midpointFunctional q p=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    (∃ b : ℝ, 0<b ∧ b≤1/2 ∧ ∀ i, p i=b) ∨
    (∃ i : Fin (m+3), ∃ a b : ℝ, 0<a ∧ a<b ∧ b≤1/2 ∧ p i=a ∧ ∀ j, j≠i → p j=b) := by
  by_cases hfair : ∃ k, p k=1/2
  · obtain ⟨k,hk⟩ := hfair
    by_cases hall : ∀ i, p i=1/2
    · exact Or.inl ⟨1/2,by norm_num,le_rfl,hall⟩
    · push Not at hall
      obtain ⟨i,hi⟩ := hall
      have hiHalf : p i<1/2 := lt_of_le_of_ne (hpHalf i) hi
      refine Or.inr ⟨i,p i,1/2,hp i,hiHalf,le_rfl,rfl,?_⟩
      intro j hji
      by_contra hj
      exact contact_no_fair_two_interior q p hq0 hq1 hp hpHalf hzero hmin i j k hji.symm hiHalf
        (lt_of_le_of_ne (hpHalf j) hj) hk
  · have hstrict : ∀ i, p i<1/2 := by
      intro i
      exact lt_of_le_of_ne (hpHalf i) (fun H => hfair ⟨i,H⟩)
    rcases contact_interior_parameter_pattern q p hq0 hq1 hp hstrict hzero hmin with H|H
    · obtain ⟨b,hb,hbH,hall⟩ := H
      exact Or.inl ⟨b,hb,hbH.le,hall⟩
    · obtain ⟨i,a,b,ha,hab,hbH,hi,hall⟩ := H
      exact Or.inr ⟨i,a,b,ha,hab,hbH.le,hi,hall⟩

/-- A single exceptional coordinate has an exact Bernoulli-plus-binomial presentation after permutation. -/
theorem single_exception_reindex {n : ℕ} (p : Fin (n+1) → ℝ) (i : Fin (n+1)) (a b : ℝ)
    (hi : p i=a) (hrest : ∀ j, j≠i → p j=b) :
    ∃ e : Equiv.Perm (Fin (n+1)), p ∘ e=Fin.cons a (fun _ : Fin n => b) := by
  let e := Equiv.swap (0:Fin (n+1)) i
  refine ⟨e,?_⟩
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [Function.comp_apply,e,Equiv.swap_apply_left,Fin.cons_zero] using hi
  · change p (e j.succ)=b
    apply hrest
    intro he
    have H : e j.succ=e 0 := by simpa only [e,Equiv.swap_apply_left] using he
    have := e.injective H
    exact Fin.succ_ne_zero j this

/-- Every actual positive half-cube zero minimum has an explicit constant or singleton-binomial factorization. -/
theorem contact_parameter_factorization {m : ℕ} (q : ℝ) (p : Fin (m+3) → ℝ)
    (hq0 : 0<q) (hq1 : q<1) (hp : ∀ i, 0<p i) (hpHalf : ∀ i, p i≤1/2)
    (hzero : midpointFunctional q p=0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i∈Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    (∃ b : ℝ, 0<b ∧ b≤1/2 ∧ p=fun _ => b) ∨
    (∃ e : Equiv.Perm (Fin (m+3)), ∃ a b : ℝ, 0<a ∧ a<b ∧ b≤1/2 ∧
      p ∘ e=Fin.cons a (fun _ : Fin (m+2) => b)) := by
  rcases contact_parameter_pattern q p hq0 hq1 hp hpHalf hzero hmin with H|H
  · obtain ⟨b,hb,hbH,hall⟩ := H
    exact Or.inl ⟨b,hb,hbH,funext hall⟩
  · obtain ⟨i,a,b,ha,hab,hbH,hi,hall⟩ := H
    obtain ⟨e,he⟩ := single_exception_reindex p i a b hi hall
    exact Or.inr ⟨e,a,b,ha,hab,hbH,he⟩

end RenyiMonotonicity
