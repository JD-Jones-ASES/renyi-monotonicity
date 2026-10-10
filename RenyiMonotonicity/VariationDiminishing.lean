module

public import RenyiMonotonicity.SignBlocks

/-! Positive adjacent averaging and zero-deleting sign variation. -/

@[expose] public section
noncomputable section
open scoped List

namespace RenyiMonotonicity

/-- Delete zero signs before compressing equal consecutive signs. -/
def nonzeroSigns (l : List ℝ) : List SignType := (l.map SignType.sign).filter (· ≠ 0)

def compressedSigns (l : List ℝ) : List SignType := (nonzeroSigns l).destutter (· ≠ ·)

lemma compressedSigns_length (l : List ℝ) : (compressedSigns l).length = signRuns l := rfl

lemma destutter'_destutter {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    (l.destutter (· ≠ ·)).destutter' (· ≠ ·) a = l.destutter' (· ≠ ·) a := by
  induction l using List.twoStepInduction generalizing a with
  | nil => simp
  | singleton b => simp
  | cons_cons b c l ih ih' =>
    by_cases hab : a = b <;> by_cases hbc : b = c
    all_goals
      simp only [List.destutter_cons_cons, List.destutter'_cons, ne_eq, hab, hbc,
        not_true_eq_false, not_false_eq_true, ite_true, ite_false]
    · subst b; subst c
      simpa only [List.destutter_cons', List.destutter'_cons, ne_eq, not_true_eq_false, ite_false] using ih' a a
    · subst b
      simpa only [List.destutter_cons', List.destutter'_cons, ne_eq, hbc, not_false_eq_true, ite_true] using ih' c a
    · subst c
      simpa only [List.destutter_cons', List.destutter'_cons, ne_eq, hab, not_false_eq_true, ite_true] using ih' b a
    · simpa only [List.destutter_cons', List.destutter'_cons, ne_eq, hbc, not_false_eq_true, ite_true] using congrArg (List.cons a) (ih' c b)

lemma destutter_prefix {α : Type*} [DecidableEq α] (l r : List α) :
    (l ++ r.destutter (· ≠ ·)).destutter (· ≠ ·) = (l++r).destutter (· ≠ ·) := by
  have aux (l : List α) (a : α) :
      (l ++ r.destutter (· ≠ ·)).destutter' (· ≠ ·) a = (l++r).destutter' (· ≠ ·) a := by
    induction l generalizing a with
    | nil => exact destutter'_destutter r a
    | cons b l ih =>
      simp only [List.cons_append, List.destutter'_cons]
      split_ifs <;> rw [ih]
  cases l with
  | nil => exact List.destutter_idem _ _
  | cons a l => exact aux l a

lemma compressedSigns_prefix_congr (l r t : List ℝ) (h : compressedSigns r = compressedSigns t) :
    compressedSigns (l++r) = compressedSigns (l++t) := by
  unfold compressedSigns nonzeroSigns at *
  simp only [List.map_append, List.filter_append]
  rw [← destutter_prefix, h, destutter_prefix]

lemma compressedSigns_insert (a b c : ℝ) (l : List ℝ)
    (h : SignType.sign c = 0 ∨ SignType.sign c = SignType.sign a ∨ SignType.sign c = SignType.sign b) :
    compressedSigns (a::c::b::l) = compressedSigns (a::b::l) := by
  rcases h with h | h | h
  all_goals
    cases ha : SignType.sign a <;> cases hb : SignType.sign b <;>
      simp [compressedSigns, nonzeroSigns, h, ha, hb, List.destutter_cons']

/-- A positive weighted average has one of its endpoint signs, or is zero. -/
lemma sign_weighted_average (p a b : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    SignType.sign ((1-p)*a+p*b) = 0 ∨
    SignType.sign ((1-p)*a+p*b) = SignType.sign a ∨
    SignType.sign ((1-p)*a+p*b) = SignType.sign b := by
  rcases lt_trichotomy ((1-p)*a+p*b) 0 with h | h | h
  · have he : a < 0 ∨ b < 0 := by
      by_contra hn
      push Not at hn
      have H := add_nonneg (mul_nonneg (by linarith : 0 ≤ 1-p) hn.1) (mul_nonneg hp.le hn.2)
      linarith
    rcases he with ha | hb
    · exact Or.inr (Or.inl (by rw [sign_neg h, sign_neg ha]))
    · exact Or.inr (Or.inr (by rw [sign_neg h, sign_neg hb]))
  · exact Or.inl (by simp [h])
  · have he : 0 < a ∨ 0 < b := by
      by_contra hn
      push Not at hn
      have H := add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1-p) hn.1)
        (mul_nonpos_of_nonneg_of_nonpos hp.le hn.2)
      linarith
    rcases he with ha | hb
    · exact Or.inr (Or.inl (by rw [sign_pos h, sign_pos ha]))
    · exact Or.inr (Or.inr (by rw [sign_pos h, sign_pos hb]))

/-- Adjacent Bernoulli averages, shortened by one entry. -/
def averageList (p : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | a::b::l => ((1-p)*a+p*b)::averageList p (b::l)

/-- Insert each Bernoulli average between its two original entries. -/
def interleaveList (p : ℝ) : List ℝ → List ℝ
  | [] => []
  | [a] => [a]
  | a::b::l => a::((1-p)*a+p*b)::interleaveList p (b::l)

lemma interleaveList_compressedSigns (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (l : List ℝ) :
    compressedSigns (interleaveList p l) = compressedSigns l := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b l ih ih' =>
    change compressedSigns ([a,(1-p)*a+p*b]++interleaveList p (b::l)) = compressedSigns (a::b::l)
    rw [compressedSigns_prefix_congr _ _ _ (ih' b)]
    exact compressedSigns_insert a b _ l (sign_weighted_average p a b hp hp1)

lemma averageList_sublist_interleaveList (p : ℝ) (l : List ℝ) :
    averageList p l <+ interleaveList p l := by
  induction l using List.twoStepInduction with
  | nil => exact .refl _
  | singleton a => exact List.nil_sublist _
  | cons_cons a b l ih ih' => exact (List.Sublist.cons_cons _ (ih' b)).cons a

lemma signRuns_le_of_sublist {l r : List ℝ} (h : l <+ r) : signRuns l ≤ signRuns r := by
  have H := (h.map SignType.sign).filter (· ≠ 0)
  exact List.IsChain.length_le_length_destutter_ne
    ((List.destutter_sublist (· ≠ ·) _).trans H) (List.isChain_destutter _ _)

/-- Positive adjacent averaging cannot increase zero-deleting sign variation. -/
theorem averageList_signVariations_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (l : List ℝ) :
    (averageList p l).signVariations ≤ l.signVariations := by
  have H := signRuns_le_of_sublist (averageList_sublist_interleaveList p l)
  have he := congrArg List.length (interleaveList_compressedSigns p hp hp1 l)
  change signRuns (interleaveList p l) = signRuns l at he
  rw [he] at H
  exact Nat.sub_le_sub_right H 1

lemma averageList_length (p : ℝ) (l : List ℝ) : (averageList p l).length = l.length-1 := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b l ih ih' => simpa [averageList] using congrArg Nat.succ (ih' b)

lemma all_zero_of_averageList_zero_head (p : ℝ) (hp : 0 < p) (l : List ℝ) (a : ℝ)
    (hzero : ∀ x ∈ averageList p (a::l), x = 0) (ha : a = 0) : ∀ x ∈ a::l, x = 0 := by
  induction l generalizing a with
  | nil => simpa only [List.mem_singleton, forall_eq] using ha
  | cons b l ih =>
    have he : (1-p)*a+p*b = 0 := hzero _ (by simp [averageList])
    have hb : b = 0 := by simpa only [ha, mul_zero, zero_add, hp.ne', false_or, mul_eq_zero] using he
    have ht : ∀ x ∈ averageList p (b::l), x = 0 := fun x hx => hzero x (by simp [averageList, hx])
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih b ht hb x hx

lemma opposite_signs_of_zero_average (p a b : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ha : a ≠ 0) (he : (1-p)*a+p*b = 0) :
    b ≠ 0 ∧ SignType.sign a ≠ SignType.sign b := by
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, mul_zero, add_zero] at he
    exact ha ((mul_eq_zero.mp he).resolve_left (by linarith))
  refine ⟨hb, ?_⟩
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hbpos : 0 < b := by
      by_contra h
      have H := mul_neg_of_pos_of_neg (by linarith : 0 < 1-p) ha
      have H' := mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt h)
      linarith
    rw [sign_neg ha, sign_pos hbpos]
    decide
  · have hbneg : b < 0 := by
      by_contra h
      have H := mul_pos (by linarith : 0 < 1-p) ha
      have H' := mul_nonneg hp.le (le_of_not_gt h)
      linarith
    rw [sign_pos ha, sign_neg hbneg]
    decide

/-- If one positive averaging step vanishes, every nonzero input entry alternates in sign. -/
theorem averageList_zero_signVariations (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (l : List ℝ) (hzero : ∀ x ∈ averageList p l, x = 0) (hne : ¬∀ x ∈ l, x = 0) :
    l.signVariations = l.length-1 := by
  induction l using List.twoStepInduction with
  | nil => simp at hne
  | singleton a => simp
  | cons_cons a b l ih ih' =>
    have he : (1-p)*a+p*b=0 := hzero _ (by simp [averageList])
    have ha : a ≠ 0 := fun ha => hne (all_zero_of_averageList_zero_head p hp (b::l) a hzero ha)
    obtain ⟨hb,hs⟩ := opposite_signs_of_zero_average p a b hp hp1 ha he
    have ht : ∀ x ∈ averageList p (b::l), x = 0 := fun x hx => hzero x (by simp [averageList,hx])
    have hn : ¬∀ x ∈ b::l, x = 0 := fun h => hb (h b (by simp))
    rw [List.signVariations_cons_cons_of_ne_zero l ha hb, ite_eq_right hs, ih' b ht hn]
    simp

/-- Apply each positive adjacent averaging factor, in the listed order. -/
def convolveList : List ℝ → List ℝ → List ℝ
  | [], v => v
  | p::ps, v => convolveList ps (averageList p v)

/-- A product of positive Bernoulli averaging factors diminishes sign variation. -/
theorem convolveList_signVariations_le (ps v : List ℝ)
    (hp : ∀ p ∈ ps, 0 < p ∧ p < 1) : (convolveList ps v).signVariations ≤ v.signVariations := by
  induction ps generalizing v with
  | nil => exact le_rfl
  | cons p ps ih =>
    exact (ih (averageList p v) (fun a ha => hp a (by simp [ha]))).trans
      (averageList_signVariations_le p (hp p (by simp)).1 (hp p (by simp)).2 v)

/-- Shift annihilation for a product of positive Bernoulli averages. A nonzero vector
with `r+1` consecutive zero outputs must have at least `r+1` sign changes. -/
theorem convolveList_kernel_signVariations (ps v : List ℝ) (r : ℕ)
    (hp : ∀ p ∈ ps, 0 < p ∧ p < 1) (hlen : v.length = ps.length+r+1)
    (hne : ¬∀ x ∈ v, x = 0) (hzero : ∀ x ∈ convolveList ps v, x = 0) :
    r+1 ≤ v.signVariations := by
  induction ps generalizing v with
  | nil => exact False.elim (hne hzero)
  | cons p ps ih =>
    have hp' := hp p (by simp)
    by_cases hw : ∀ x ∈ averageList p v, x = 0
    · rw [averageList_zero_signVariations p hp'.1 hp'.2 v hw hne, hlen]
      simp
    · have H := ih (averageList p v) (fun a ha => hp a (by simp [ha]))
        (by rw [averageList_length, hlen]; simp; omega) hw hzero
      exact H.trans (averageList_signVariations_le p hp'.1 hp'.2 v)

lemma destutter_head {α : Type*} [DecidableEq α] (l : List α) :
    (l.destutter (· ≠ ·)).head? = l.head? := by
  have aux (l : List α) (a : α) : (l.destutter' (· ≠ ·) a).head? = some a := by
    induction l generalizing a with
    | nil => rfl
    | cons b l ih =>
      rw [List.destutter'_cons]
      split_ifs <;> simp_all
  cases l with
  | nil => rfl
  | cons a l => exact aux l a

lemma destutter_getLast {α : Type*} [DecidableEq α] (l : List α) :
    (l.destutter (· ≠ ·)).getLast? = l.getLast? := by
  have aux (l : List α) (a : α) : (l.destutter' (· ≠ ·) a).getLast? = (a::l).getLast? := by
    induction l generalizing a with
    | nil => rfl
    | cons b l ih =>
      rw [List.destutter'_cons]
      by_cases hab : a = b
      · subst b
        simp only [ne_eq, not_true_eq_false, ite_false, List.getLast?_cons_cons]
        exact ih a
      · rw [ite_eq_left hab, List.getLast?_cons_of_ne_nil (List.destutter'_ne_nil _ _), ih]
        exact List.getLast?_cons_cons.symm
  cases l with
  | nil => rfl
  | cons a l => exact aux l a

/-- A longest alternating sublist must retain the first sign of its source. -/
lemma head_eq_of_maximal_ne_chain {α : Type*} [DecidableEq α] {l r : List α} (h : l <+ r)
    (hc : l.IsChain (· ≠ ·)) (hlen : l.length = (r.destutter (· ≠ ·)).length) (hne : l ≠ []) :
    l.head? = r.head? := by
  induction h with
  | slnil => exact False.elim (hne rfl)
  | @cons l r a h ih =>
    have hle := hc.length_le_length_destutter_ne h
    have hle' := List.length_destutter_ne_le_length_destutter_cons (l := r) (a := a)
    have he : l.length = (r.destutter (· ≠ ·)).length := by omega
    have hi := ih hc he hne
    cases r with
    | nil => have := List.sublist_nil.mp h; contradiction
    | cons b r =>
      by_cases hab : a = b
      · subst a
        exact hi
      · have hh : ((a::b::r).destutter (· ≠ ·)).length = (1+( (b::r).destutter (· ≠ ·)).length) := by
          simp only [List.destutter_cons', List.destutter'_cons, ite_eq_left hab, List.length_cons]
          omega
        omega
  | cons_cons a h ih => rfl

lemma length_destutter_reverse {α : Type*} [DecidableEq α] (l : List α) :
    (l.reverse.destutter (· ≠ ·)).length = (l.destutter (· ≠ ·)).length := by
  have aux (l : List α) : (l.destutter (· ≠ ·)).length ≤ (l.reverse.destutter (· ≠ ·)).length := by
    have hc : (l.destutter (· ≠ ·)).reverse.IsChain (· ≠ ·) :=
      List.isChain_reverse.mpr (by simpa only [ne_comm] using List.isChain_destutter (· ≠ ·) l)
    simpa only [List.length_reverse] using
      hc.length_le_length_destutter_ne (List.destutter_sublist (· ≠ ·) l).reverse
  apply le_antisymm
  · simpa only [List.reverse_reverse] using aux l.reverse
  · exact aux l

lemma nonzeroSigns_eq_nil (l : List ℝ) : nonzeroSigns l = [] ↔ ∀ x ∈ l, x = 0 := by
  simp [nonzeroSigns, List.filter_eq_nil_iff, List.mem_map]

lemma signRuns_reverse (l : List ℝ) : signRuns l.reverse = signRuns l := by
  unfold signRuns
  rw [List.map_reverse, List.filter_reverse]
  exact length_destutter_reverse _

/-- Deleting entries without lowering the variation count preserves both nonzero endpoint signs. -/
theorem sublist_sign_endpoints_of_variations_eq {l r : List ℝ} (h : l <+ r)
    (hne : ¬∀ x ∈ l, x = 0) (hvar : l.signVariations = r.signVariations) :
    (nonzeroSigns l).head? = (nonzeroSigns r).head? ∧
    (nonzeroSigns l).getLast? = (nonzeroSigns r).getLast? := by
  have hlne : nonzeroSigns l ≠ [] := (nonzeroSigns_eq_nil l).not.mpr hne
  have hcne : compressedSigns l ≠ [] := (List.destutter_eq_nil (· ≠ ·)).not.mpr hlne
  have hpos : 0 < signRuns l := List.length_pos_iff.mpr hcne
  have hle := signRuns_le_of_sublist h
  have he : signRuns l = signRuns r := by
    change signRuns l-1=signRuns r-1 at hvar
    omega
  have aux {l r : List ℝ} (h : l <+ r) (hne : nonzeroSigns l ≠ []) (he : signRuns l=signRuns r) :
      (nonzeroSigns l).head? = (nonzeroSigns r).head? := by
    have hs := ((List.destutter_sublist (· ≠ ·) _).trans ((h.map SignType.sign).filter (· ≠ 0)))
    have H := head_eq_of_maximal_ne_chain hs (List.isChain_destutter (· ≠ ·) _) he
      ((List.destutter_eq_nil (· ≠ ·)).not.mpr hne)
    exact (destutter_head (nonzeroSigns l)).symm.trans H
  refine ⟨aux h hlne he, ?_⟩
  have hne' : nonzeroSigns l.reverse ≠ [] := by simpa [nonzeroSigns] using hlne
  have H := aux h.reverse hne' (by simpa only [signRuns_reverse] using he)
  simpa [nonzeroSigns] using H

/-- Equality in variation diminution preserves the input's first and last nonzero signs. -/
theorem averageList_sign_endpoints_of_variations_eq (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (v : List ℝ) (hne : ¬∀ x ∈ averageList p v, x = 0)
    (hvar : (averageList p v).signVariations = v.signVariations) :
    (nonzeroSigns (averageList p v)).head? = (nonzeroSigns v).head? ∧
    (nonzeroSigns (averageList p v)).getLast? = (nonzeroSigns v).getLast? := by
  have he := interleaveList_compressedSigns p hp hp1 v
  have hlen := congrArg List.length he
  change signRuns (interleaveList p v) = signRuns v at hlen
  have H := sublist_sign_endpoints_of_variations_eq (averageList_sublist_interleaveList p v) hne
    (by change signRuns (averageList p v)-1 = signRuns (interleaveList p v)-1; rw [hlen]; exact hvar)
  have hhead := congrArg List.head? he
  have hlast := congrArg List.getLast? he
  simp only [compressedSigns, destutter_head] at hhead
  simp only [compressedSigns, destutter_getLast] at hlast
  exact ⟨H.1.trans hhead, H.2.trans hlast⟩

lemma averageList_all_zero (p : ℝ) (v : List ℝ) (hz : ∀ x ∈ v, x = 0) :
    ∀ x ∈ averageList p v, x = 0 := by
  induction v using List.twoStepInduction with
  | nil => simp [averageList]
  | singleton a => simp [averageList]
  | cons_cons a b l ih ih' =>
    have ha := hz a (by simp)
    have hb := hz b (by simp)
    have ht := ih' b (fun x hx => hz x (by simp [hx]))
    simpa [averageList, ha, hb] using ht

lemma convolveList_all_zero (ps v : List ℝ) (hz : ∀ x ∈ v, x = 0) :
    ∀ x ∈ convolveList ps v, x = 0 := by
  induction ps generalizing v with
  | nil => exact hz
  | cons p ps ih => exact ih (averageList p v) (averageList_all_zero p v hz)

/-- A nonzero output with the full input variation count has exactly the same
first and last nonzero signs, through any finite positive Bernoulli convolution. -/
theorem convolveList_sign_endpoints_of_variations_eq (ps v : List ℝ)
    (hp : ∀ p ∈ ps, 0 < p ∧ p < 1)
    (hne : ¬∀ x ∈ convolveList ps v, x = 0)
    (hvar : (convolveList ps v).signVariations = v.signVariations) :
    (nonzeroSigns (convolveList ps v)).head? = (nonzeroSigns v).head? ∧
    (nonzeroSigns (convolveList ps v)).getLast? = (nonzeroSigns v).getLast? := by
  induction ps generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons p ps ih =>
    have hp' := hp p (by simp)
    have htail : ∀ a ∈ ps, 0 < a ∧ a < 1 := fun a ha => hp a (by simp [ha])
    have hne' : ¬∀ x ∈ averageList p v, x = 0 := fun hz => hne (convolveList_all_zero ps _ hz)
    have h₁ := convolveList_signVariations_le ps (averageList p v) htail
    have h₂ := averageList_signVariations_le p hp'.1 hp'.2 v
    have he₁ : (convolveList ps (averageList p v)).signVariations = (averageList p v).signVariations := by
      change (convolveList ps (averageList p v)).signVariations = v.signVariations at hvar
      omega
    have he₂ : (averageList p v).signVariations = v.signVariations := by
      change (convolveList ps (averageList p v)).signVariations = v.signVariations at hvar
      omega
    have H₁ := ih (averageList p v) htail hne he₁
    have H₂ := averageList_sign_endpoints_of_variations_eq p hp'.1 hp'.2 v hne' he₂
    exact ⟨H₁.1.trans H₂.1,H₁.2.trans H₂.2⟩

end RenyiMonotonicity
