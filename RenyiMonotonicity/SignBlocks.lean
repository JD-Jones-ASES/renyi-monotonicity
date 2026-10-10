module

public import Mathlib

/-! Finite sign-block bookkeeping, with zeros allowed in either neighbouring block. -/

@[expose] public section
noncomputable section

namespace RenyiMonotonicity

/-- Four successive weak sign blocks: negative, positive, negative, positive.
Any block may be empty, and zero values may be placed on either side of a cut. -/
def FourSignBlocks {n : ℕ} (f : Fin n → ℝ) : Prop :=
  ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧ c ≤ n ∧ ∀ i,
    (i.val < a → f i ≤ 0) ∧
    (a ≤ i.val → i.val < b → 0 ≤ f i) ∧
    (b ≤ i.val → i.val < c → f i ≤ 0) ∧
    (c ≤ i.val → 0 ≤ f i)

/-- A finite interval in which positive values cannot be followed by negative ones
has a single weak negative-to-positive cut. -/
theorem exists_signCut {n : ℕ} (f : Fin n → ℝ) (l r : ℕ) (hlr : l ≤ r)
    (horder : ∀ i j, l ≤ i.val → i.val < j.val → j.val < r → 0 < f i → 0 ≤ f j) :
    ∃ a : ℕ, l ≤ a ∧ a ≤ r ∧ ∀ i,
      (l ≤ i.val → i.val < a → f i ≤ 0) ∧
      (a ≤ i.val → i.val < r → 0 ≤ f i) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => l ≤ i.val ∧ i.val < r ∧ 0 < f i)
  by_cases hs : s.Nonempty
  · let j := s.min' hs
    have hj : l ≤ j.val ∧ j.val < r ∧ 0 < f j := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
    refine ⟨j.val, hj.1, hj.2.1.le, ?_⟩
    intro i
    constructor
    · intro hli hij
      by_contra hi
      have hi' : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli, hij.trans hj.2.1, lt_of_not_ge hi⟩
      have hji := Finset.min'_le s i hi'
      exact (not_le_of_gt hij) hji
    · intro hji hir
      rcases lt_or_eq_of_le hji with hji | hji
      · exact horder j i hj.1 hji hir hj.2.2
      · have he : j = i := Fin.ext hji
        simpa only [← he] using hj.2.2.le
  · refine ⟨r, hlr, le_rfl, ?_⟩
    intro i
    constructor
    · intro hli hir
      by_contra hi
      exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hli, hir, lt_of_not_ge hi⟩⟩
    · intro hri hir
      omega

/-- Two consecutive intervals, each ordered negative-to-positive, form four sign blocks. -/
theorem fourSignBlocks_of_split {n : ℕ} (f : Fin n → ℝ) (b : ℕ) (hb : b ≤ n)
    (hleft : ∀ i j, i.val < j.val → j.val < b → 0 < f i → 0 ≤ f j)
    (hright : ∀ i j, b ≤ i.val → i.val < j.val → 0 < f i → 0 ≤ f j) :
    FourSignBlocks f := by
  obtain ⟨a, _, hab, ha⟩ := exists_signCut f 0 b (Nat.zero_le _) (fun i j _ hij hj => hleft i j hij hj)
  obtain ⟨c, hbc, hcn, hc⟩ := exists_signCut f b n hb (fun i j hi hij _ => hright i j hi hij)
  refine ⟨a,b,c,hab,hbc,hcn,?_⟩
  intro i
  exact ⟨fun hi => (ha i).1 (Nat.zero_le _) hi, (ha i).2,
    (hc i).1, fun hi => (hc i).2 hi i.isLt⟩

/-- The number of nonzero constant-sign runs in a real list. -/
def signRuns (l : List ℝ) : ℕ :=
  (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length

lemma length_destutter_append_le {α : Type*} [DecidableEq α] (l r : List α) :
    ((l++r).destutter (· ≠ ·)).length ≤
      (l.destutter (· ≠ ·)).length + (r.destutter (· ≠ ·)).length := by
  obtain ⟨a,b,he,ha,hb⟩ := List.sublist_append_iff.mp ((l++r).destutter_sublist (· ≠ ·))
  have H := List.isChain_destutter (· ≠ ·) (l++r)
  rw [he] at H ⊢
  have h₁ := H.left_of_append.length_le_length_destutter_ne ha
  have h₂ := H.right_of_append.length_le_length_destutter_ne hb
  simpa only [List.length_append] using Nat.add_le_add h₁ h₂

lemma signRuns_append_le (l r : List ℝ) : signRuns (l++r) ≤ signRuns l + signRuns r := by
  unfold signRuns
  rw [List.map_append, List.filter_append]
  exact length_destutter_append_le _ _

lemma length_le_one_of_constant_chain {α : Type*} (l : List α) (a : α)
    (h : ∀ b ∈ l, b = a) (hc : l.IsChain (· ≠ ·)) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons b l =>
    cases l with
    | nil => simp
    | cons c l =>
      have hbc := (List.isChain_cons_cons.mp hc).1
      exact False.elim (hbc ((h b (by simp)).trans (h c (by simp)).symm))

lemma signRuns_le_one_of_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) : signRuns l ≤ 1 := by
  apply length_le_one_of_constant_chain _ (1 : SignType)
  · intro s hs
    have hs' := (List.destutter_sublist (· ≠ ·) _).subset hs
    obtain ⟨hs', hs0⟩ := List.mem_filter.mp hs'
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs'
    have hx0 : x ≠ 0 := by simpa using hs0
    exact sign_eq_one_iff.mpr (lt_of_le_of_ne (h x hx) hx0.symm)
  · exact List.isChain_destutter _ _

lemma signRuns_le_one_of_nonpos (l : List ℝ) (h : ∀ x ∈ l, x ≤ 0) : signRuns l ≤ 1 := by
  apply length_le_one_of_constant_chain _ (-1 : SignType)
  · intro s hs
    have hs' := (List.destutter_sublist (· ≠ ·) _).subset hs
    obtain ⟨hs', hs0⟩ := List.mem_filter.mp hs'
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs'
    have hx0 : x ≠ 0 := by simpa using hs0
    exact sign_eq_neg_one_iff.mpr (lt_of_le_of_ne (h x hx) hx0)
  · exact List.isChain_destutter _ _

/-- Split a tuple-list at an arbitrary natural cut. -/
lemma ofFn_split_at {n : ℕ} (f : Fin n → ℝ) (a : ℕ) (ha : a ≤ n) :
    List.ofFn f =
      List.ofFn (fun i : Fin a => f ⟨i.val, by omega⟩) ++
      List.ofFn (fun i : Fin (n-a) => f ⟨a+i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    by_cases hia : i < a
    · simp [hia]
    · simp [List.getElem_append, hia]
      congr 1
      apply Fin.ext
      simp
      omega

lemma signRuns_ofFn_split_le {n : ℕ} (f : Fin n → ℝ) (a : ℕ) (ha : a ≤ n) :
    signRuns (List.ofFn f) ≤
      signRuns (List.ofFn (fun i : Fin a => f ⟨i.val, by omega⟩)) +
      signRuns (List.ofFn (fun i : Fin (n-a) => f ⟨a+i.val, by omega⟩)) := by
  conv_lhs => rw [ofFn_split_at f a ha]
  exact signRuns_append_le _ _

lemma signRuns_ofFn_nonneg {n : ℕ} (f : Fin n → ℝ) (h : ∀ i, 0 ≤ f i) :
    signRuns (List.ofFn f) ≤ 1 := by
  apply signRuns_le_one_of_nonneg
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact h i

lemma signRuns_ofFn_nonpos {n : ℕ} (f : Fin n → ℝ) (h : ∀ i, f i ≤ 0) :
    signRuns (List.ofFn f) ≤ 1 := by
  apply signRuns_le_one_of_nonpos
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact h i

/-- Four weak sign blocks bound the number of nonzero sign runs by four. -/
theorem FourSignBlocks.signRuns_le_four {n : ℕ} {f : Fin n → ℝ} (h : FourSignBlocks f) :
    signRuns (List.ofFn f) ≤ 4 := by
  obtain ⟨a,b,c,hab,hbc,hcn,h⟩ := h
  let fc : Fin c → ℝ := fun i => f ⟨i.val, by omega⟩
  let fb : Fin b → ℝ := fun i => f ⟨i.val, by omega⟩
  have Hc := signRuns_ofFn_split_le f c hcn
  have Hb := signRuns_ofFn_split_le fc b hbc
  have Ha := signRuns_ofFn_split_le fb a hab
  have H₁ : signRuns (List.ofFn (fun i : Fin a => fb ⟨i.val, by omega⟩)) ≤ 1 := by
    apply signRuns_ofFn_nonpos
    intro i
    exact (h ⟨i.val, by omega⟩).1 i.isLt
  have H₂ : signRuns (List.ofFn (fun i : Fin (b-a) => fb ⟨a+i.val, by omega⟩)) ≤ 1 := by
    apply signRuns_ofFn_nonneg
    intro i
    exact (h ⟨a+i.val, by omega⟩).2.1 (by dsimp only; omega) (by dsimp only; omega)
  have H₃ : signRuns (List.ofFn (fun i : Fin (c-b) => fc ⟨b+i.val, by omega⟩)) ≤ 1 := by
    apply signRuns_ofFn_nonpos
    intro i
    exact (h ⟨b+i.val, by omega⟩).2.2.1 (by dsimp only; omega) (by dsimp only; omega)
  have H₄ : signRuns (List.ofFn (fun i : Fin (n-c) => f ⟨c+i.val, by omega⟩)) ≤ 1 := by
    apply signRuns_ofFn_nonneg
    intro i
    exact (h ⟨c+i.val, by omega⟩).2.2.2 (by dsimp only; omega)
  have Hb' : signRuns (List.ofFn fc) ≤ signRuns (List.ofFn fb) +
      signRuns (List.ofFn (fun i : Fin (c-b) => fc ⟨b+i.val, by omega⟩)) := Hb
  have Hc' : signRuns (List.ofFn f) ≤ signRuns (List.ofFn fc) +
      signRuns (List.ofFn (fun i : Fin (n-c) => f ⟨c+i.val, by omega⟩)) := Hc
  omega

/-- Four weak sign blocks give at most three sign changes after every zero is removed. -/
theorem FourSignBlocks.signVariations_le_three {n : ℕ} {f : Fin n → ℝ} (h : FourSignBlocks f) :
    (List.ofFn f).signVariations ≤ 3 := by
  have H := h.signRuns_le_four
  change signRuns (List.ofFn f)-1 ≤ 3
  omega

end RenyiMonotonicity
