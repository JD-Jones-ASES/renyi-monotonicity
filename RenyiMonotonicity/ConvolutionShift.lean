module

public import RenyiMonotonicity.VariationDiminishing
public import RenyiMonotonicity.BernoulliPolynomial

/-! Identification of positive adjacent averaging with the actual Bernoulli shift kernel. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

def sampleList (n : ℕ) (f : ℕ → ℝ) : List ℝ := List.ofFn (fun i : Fin n => f i.val)

def averageFunction (p : ℝ) (f : ℕ → ℝ) (j : ℕ) : ℝ := (1-p)*f j+p*f (j+1)

lemma sampleList_succ (n : ℕ) (f : ℕ → ℝ) :
    sampleList (n+1) f = f 0 :: sampleList n (fun j => f (j+1)) := by
  simp only [sampleList, List.ofFn_succ, Fin.val_zero, Fin.val_succ]

lemma averageList_sampleList (p : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    averageList p (sampleList (n+1) f) = sampleList n (averageFunction p f) := by
  induction n generalizing f with
  | zero => simp [sampleList, List.ofFn_succ, averageList]
  | succ n ih =>
    rw [sampleList_succ, sampleList_succ]
    rw [averageList, ← sampleList_succ n (fun j => f (j+1))]
    rw [ih, sampleList_succ]
    rfl

/-- One actual coefficient convolution is exactly one adjacent averaging factor. -/
theorem bernoulliShift_cons {n : ℕ} (a : ℝ) (p : Fin n → ℝ) (f : ℕ → ℝ) (j : ℕ) :
    (∑ k : Fin (n+2), bernoulliMass (Fin.cons a p) k.val * f (j+k.val)) =
      ∑ k : Fin (n+1), bernoulliMass p k.val * averageFunction a f (j+k.val) := by
  simp_rw [bernoulliMass_cons, add_mul]
  rw [Finset.sum_add_distrib]
  have hleft : (∑ k : Fin (n+2), (1-a)*bernoulliMass p k.val*f (j+k.val)) =
      ∑ k : Fin (n+1), (1-a)*bernoulliMass p k.val*f (j+k.val) := by
    rw [Fin.sum_univ_castSucc]
    simp [bernoulliMass_outer_right]
  have hright : (∑ k : Fin (n+2), a*bernoulliMass p ((k.val:ℤ)-1)*f (j+k.val)) =
      ∑ k : Fin (n+1), a*bernoulliMass p k.val*f (j+k.val+1) := by
    rw [Fin.sum_univ_succ]
    simp [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
  rw [hleft, hright, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold averageFunction
  ring

/-- The iterated list average is the concrete Bernoulli coefficient kernel on every shift. -/
theorem convolveList_bernoulliShift {m : ℕ} (p : Fin m → ℝ) (f : ℕ → ℝ) (r : ℕ) :
    convolveList (List.ofFn p) (sampleList (m+r+1) f) =
      List.ofFn (fun j : Fin (r+1) => ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val)) := by
  induction m generalizing f with
  | zero =>
    simp [sampleList, convolveList, bernoulliMass, bernoulliPolynomial]
  | succ m ih =>
    have hp : p = Fin.cons (p 0) (Fin.tail p) := (Fin.cons_self_tail p).symm
    rw [hp, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, convolveList]
    rw [show m+1+r+1=(m+r+1)+1 by omega, averageList_sampleList, ih]
    apply congrArg List.ofFn
    funext j
    exact (bernoulliShift_cons (p 0) (Fin.tail p) f j.val).symm

/-- The actual Bernoulli shift kernel has the strict kernel variation bound for every number of shifts. -/
theorem bernoulliShift_kernel_signVariations {m : ℕ} (p : Fin m → ℝ) (f : ℕ → ℝ) (r : ℕ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hne : ¬∀ j < m+r+1, f j = 0)
    (hzero : ∀ j : Fin (r+1), ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val) = 0) :
    r+1 ≤ (sampleList (m+r+1) f).signVariations := by
  apply convolveList_kernel_signVariations (List.ofFn p) _ r
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨hp i,hp1 i⟩
  · simp [sampleList]
  · intro hz
    apply hne
    intro j hj
    exact hz (f j) (List.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩)
  · rw [convolveList_bernoulliShift]
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact hzero j

/-- Variation diminution for the actual Bernoulli coefficient kernel. -/
theorem bernoulliShift_signVariations_le {m : ℕ} (p : Fin m → ℝ) (f : ℕ → ℝ) (r : ℕ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    (List.ofFn (fun j : Fin (r+1) => ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val))).signVariations ≤
      (sampleList (m+r+1) f).signVariations := by
  rw [← convolveList_bernoulliShift]
  apply convolveList_signVariations_le
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact ⟨hp i,hp1 i⟩

/-- At equal variation count, a nonzero actual Bernoulli convolution retains both
nonzero endpoint signs of the original finite vector. -/
theorem bernoulliShift_sign_endpoints_of_variations_eq {m : ℕ} (p : Fin m → ℝ)
    (f : ℕ → ℝ) (r : ℕ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (hne : ¬∀ j : Fin (r+1), ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val) = 0)
    (hvar : (List.ofFn (fun j : Fin (r+1) => ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val))).signVariations =
      (sampleList (m+r+1) f).signVariations) :
    (nonzeroSigns (List.ofFn (fun j : Fin (r+1) => ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val)))).head? =
      (nonzeroSigns (sampleList (m+r+1) f)).head? ∧
    (nonzeroSigns (List.ofFn (fun j : Fin (r+1) => ∑ k : Fin (m+1), bernoulliMass p k.val*f (j.val+k.val)))).getLast? =
      (nonzeroSigns (sampleList (m+r+1) f)).getLast? := by
  rw [← convolveList_bernoulliShift] at hvar ⊢
  apply convolveList_sign_endpoints_of_variations_eq _ _ _ _ hvar
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨hp i,hp1 i⟩
  · intro hz
    rw [convolveList_bernoulliShift] at hz
    apply hne
    intro j
    exact hz _ (List.mem_ofFn.mpr ⟨j,rfl⟩)

end RenyiMonotonicity
