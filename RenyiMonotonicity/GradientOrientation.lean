module

public import RenyiMonotonicity.GradientSigns
public import RenyiMonotonicity.VariationDiminishing

/-! Endpoint orientation when the actual mass gradient attains its three-variation bound. -/

@[expose] public section
noncomputable section

namespace RenyiMonotonicity

/-- Four numerical cuts give an exact list decomposition into the four weak sign blocks. -/
theorem FourSignBlocks.exists_list_decomposition {n : ℕ} {f : Fin n → ℝ} (h : FourSignBlocks f) :
    ∃ a b c d : List ℝ, List.ofFn f = a++b++c++d ∧
      (∀ x ∈ a, x ≤ 0) ∧ (∀ x ∈ b, 0 ≤ x) ∧ (∀ x ∈ c, x ≤ 0) ∧ (∀ x ∈ d, 0 ≤ x) := by
  obtain ⟨a,b,c,hab,hbc,hcn,h⟩ := h
  let fc : Fin c → ℝ := fun i => f ⟨i.val, by omega⟩
  let fb : Fin b → ℝ := fun i => f ⟨i.val, by omega⟩
  let l₁ := List.ofFn (fun i : Fin a => f ⟨i.val, by omega⟩)
  let l₂ := List.ofFn (fun i : Fin (b-a) => f ⟨a+i.val, by omega⟩)
  let l₃ := List.ofFn (fun i : Fin (c-b) => f ⟨b+i.val, by omega⟩)
  let l₄ := List.ofFn (fun i : Fin (n-c) => f ⟨c+i.val, by omega⟩)
  have Hc : List.ofFn f = List.ofFn fc ++ l₄ := ofFn_split_at f c hcn
  have Hb : List.ofFn fc = List.ofFn fb ++ l₃ := ofFn_split_at fc b hbc
  have Ha : List.ofFn fb = l₁ ++ l₂ := ofFn_split_at fb a hab
  refine ⟨l₁,l₂,l₃,l₄,by rw [Hc,Hb,Ha],?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (h ⟨i.val, by omega⟩).1 i.isLt
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (h ⟨a+i.val, by omega⟩).2.1 (by dsimp only; omega) (by dsimp only; omega)
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (h ⟨b+i.val, by omega⟩).2.2.1 (by dsimp only; omega) (by dsimp only; omega)
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (h ⟨c+i.val, by omega⟩).2.2.2 (by dsimp only; omega)

lemma nonzeroSigns_constant_of_nonpos (l : List ℝ) (h : ∀ x ∈ l, x ≤ 0) :
    ∀ s ∈ nonzeroSigns l, s = -1 := by
  intro s hs
  obtain ⟨hs,hne⟩ := List.mem_filter.mp hs
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs
  have hx0 : x ≠ 0 := by simpa using hne
  exact sign_neg (lt_of_le_of_ne (h x hx) hx0)

lemma nonzeroSigns_constant_of_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) :
    ∀ s ∈ nonzeroSigns l, s = 1 := by
  intro s hs
  obtain ⟨hs,hne⟩ := List.mem_filter.mp hs
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs
  have hx0 : x ≠ 0 := by simpa using hne
  exact sign_pos (lt_of_le_of_ne (h x hx) hx0.symm)

lemma head_eq_of_nonempty_constant {α : Type*} (l : List α) (a : α)
    (hne : l ≠ []) (h : ∀ x ∈ l, x = a) : l.head? = some a := by
  cases l with
  | nil => contradiction
  | cons b l => simpa only [List.head?_cons, Option.some.injEq] using h b (by simp)

lemma last_eq_of_nonempty_constant {α : Type*} (l : List α) (a : α)
    (hne : l ≠ []) (h : ∀ x ∈ l, x = a) : l.getLast? = some a := by
  have H := head_eq_of_nonempty_constant l.reverse a (by simpa using hne)
    (fun x hx => h x (List.mem_reverse.mp hx))
  simpa using H

/-- Attaining three variations forces the prescribed initial negative and terminal positive signs. -/
theorem FourSignBlocks.endpoints_of_three {n : ℕ} {f : Fin n → ℝ} (h : FourSignBlocks f)
    (hvar : (List.ofFn f).signVariations = 3) :
    (nonzeroSigns (List.ofFn f)).head? = some (-1) ∧
    (nonzeroSigns (List.ofFn f)).getLast? = some 1 := by
  obtain ⟨a,b,c,d,he,ha,hb,hc,hd⟩ := h.exists_list_decomposition
  have Hr : signRuns (List.ofFn f) = 4 := by
    change signRuns (List.ofFn f)-1=3 at hvar
    omega
  have H₁ := signRuns_le_one_of_nonpos a ha
  have H₂ := signRuns_le_one_of_nonneg b hb
  have H₃ := signRuns_le_one_of_nonpos c hc
  have H₄ := signRuns_le_one_of_nonneg d hd
  have Hab := signRuns_append_le a b
  have Habc := signRuns_append_le (a++b) c
  have Habcd := signRuns_append_le (a++b++c) d
  rw [← he, Hr] at Habcd
  have hap : 0 < signRuns a := by omega
  have hdp : 0 < signRuns d := by omega
  have han : nonzeroSigns a ≠ [] := by
    intro hz
    change 0 < (compressedSigns a).length at hap
    simp [compressedSigns,hz] at hap
  have hdn : nonzeroSigns d ≠ [] := by
    intro hz
    change 0 < (compressedSigns d).length at hdp
    simp [compressedSigns,hz] at hdp
  have hhead := head_eq_of_nonempty_constant (nonzeroSigns a) (-1) han (nonzeroSigns_constant_of_nonpos a ha)
  have hlast := last_eq_of_nonempty_constant (nonzeroSigns d) 1 hdn (nonzeroSigns_constant_of_nonneg d hd)
  rw [he]
  simp only [nonzeroSigns, List.map_append, List.filter_append] at hhead hlast han hdn ⊢
  constructor
  · rw [List.append_assoc, List.append_assoc, List.head?_append_of_ne_nil _ han]
    exact hhead
  · rw [List.getLast?_append_of_ne_nil _ hdn]
    exact hlast

/-- The only possible three-change orientation of the actual mass gradient starts negative
and ends positive, including all zero entries in the proved convention. -/
theorem bernoulliMassGradient_endpoints_of_three {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hvar : (List.ofFn (fun i : Fin (n+1) => bernoulliMassGradient q p i.val)).signVariations = 3) :
    (nonzeroSigns (List.ofFn (fun i : Fin (n+1) => bernoulliMassGradient q p i.val))).head? = some (-1) ∧
    (nonzeroSigns (List.ofFn (fun i : Fin (n+1) => bernoulliMassGradient q p i.val))).getLast? = some 1 :=
  (bernoulliMassGradient_fourSignBlocks q p hq0 hq1 hp hp1).endpoints_of_three hvar

end RenyiMonotonicity
