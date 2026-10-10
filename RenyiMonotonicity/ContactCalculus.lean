module

public import RenyiMonotonicity.GradientNonzero
public import RenyiMonotonicity.ConvolutionShift

/-! Actual first-contact derivatives and homogeneous mass-gradient identities. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

/-- Pair a mass perturbation with the actual finite mass gradient. -/
def massGradientPairing (q : ℝ) (n : ℕ) (g h : ℤ → ℝ) : ℝ :=
  ∑ k : Fin (n+1), h k.val * massGradientEntry q (g ((k.val:ℤ)-1)) (g k.val) (g ((k.val:ℤ)+1))

lemma massGradientPairing_edges (q : ℝ) (n : ℕ) (g h : ℤ → ℝ)
    (hleft : h (-1)=0) (hright : h ((n:ℤ)+1)=0) :
    massGradientPairing q n g h =
      ∑ k : Fin (n+2), (h ((k.val:ℤ)-1)*massGradientScalar q (g ((k.val:ℤ)-1)) (g k.val) -
        h k.val*massGradientScalar q (g k.val) (g ((k.val:ℤ)-1))) := by
  rw [Finset.sum_sub_distrib]
  have h₁ : (∑ k : Fin (n+2), h ((k.val:ℤ)-1)*massGradientScalar q (g ((k.val:ℤ)-1)) (g k.val)) =
      ∑ k : Fin (n+1), h k.val*massGradientScalar q (g k.val) (g ((k.val:ℤ)+1)) := by
    rw [Fin.sum_univ_succ]
    simp [hleft, Nat.cast_add, Nat.cast_one]
  have h₂ : (∑ k : Fin (n+2), h k.val*massGradientScalar q (g k.val) (g ((k.val:ℤ)-1))) =
      ∑ k : Fin (n+1), h k.val*massGradientScalar q (g k.val) (g ((k.val:ℤ)-1)) := by
    rw [Fin.sum_univ_castSucc]
    simp [hright]
  rw [h₁,h₂,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold massGradientEntry
  ring

lemma hasDerivAt_mass_edge (q : ℝ) (a b : ℝ → ℝ) (da db t : ℝ)
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hs : 0 < a t+b t) :
    HasDerivAt (fun s => (a s-b s)*(a s+b s)^(q-1))
      (da*massGradientScalar q (a t) (b t) - db*massGradientScalar q (b t) (a t)) t := by
  have H := (ha.sub hb).mul ((ha.add hb).rpow_const (p := q-1) (Or.inl hs.ne'))
  have he : (a t+b t)^(q-1) = (a t+b t)^(q-2)*(a t+b t) := by
    rw [show q-1=(q-2)+1 by ring, Real.rpow_add hs, Real.rpow_one]
  convert H using 1
  simp only [Pi.sub_apply, Pi.add_apply]
  unfold massGradientScalar
  rw [show q-1-1=q-2 by ring, he, add_comm (b t) (a t)]
  ring

/-- Every differentiable mass path has the actual mass-gradient pairing as derivative. -/
theorem hasDerivAt_finiteMassFunctional_path (q : ℝ) (n : ℕ) (g : ℝ → ℤ → ℝ) (h : ℤ → ℝ)
    (t : ℝ) (hg : ∀ k, HasDerivAt (fun s => g s k) (h k) t)
    (hs : ∀ k : Fin (n+2), 0 < g t ((k.val:ℤ)-1)+g t k.val)
    (hleft : h (-1)=0) (hright : h ((n:ℤ)+1)=0) :
    HasDerivAt (fun s => finiteMassFunctional q n (g s)) (massGradientPairing q n (g t) h) t := by
  rw [massGradientPairing_edges q n (g t) h hleft hright]
  apply HasDerivAt.fun_sum
  intro k _
  exact hasDerivAt_mass_edge q (fun s => g s ((k.val:ℤ)-1)) (fun s => g s k.val)
    _ _ t (hg _) (hg _) (hs k)

lemma massGradientScalar_euler (q a b : ℝ) (hs : 0 < a+b) :
    a*massGradientScalar q a b-b*massGradientScalar q b a = q*(a-b)*(a+b)^(q-1) := by
  have he : (a+b)^(q-1) = (a+b)^(q-2)*(a+b) := by
    rw [show q-1=(q-2)+1 by ring, Real.rpow_add hs, Real.rpow_one]
  unfold massGradientScalar
  rw [add_comm b a, he]
  ring

/-- Euler's homogeneous identity for the actual finite mass functional. -/
theorem massGradientPairing_euler (q : ℝ) (n : ℕ) (g : ℤ → ℝ)
    (hleft : g (-1)=0) (hright : g ((n:ℤ)+1)=0)
    (hs : ∀ k : Fin (n+2), 0 < g ((k.val:ℤ)-1)+g k.val) :
    massGradientPairing q n g g = q*finiteMassFunctional q n g := by
  rw [massGradientPairing_edges q n g g hleft hright]
  unfold finiteMassFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [mul_assoc] using massGradientScalar_euler q _ _ (hs k)

/-- Euler's identity on the actual positive Bernoulli count law. -/
theorem bernoulliMassGradient_euler {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) :
    (∑ k : Fin (n+1), bernoulliMass p k.val*bernoulliMassGradient q p k.val) = q*midpointFunctional q p :=
  massGradientPairing_euler q n (bernoulliMass p) (bernoulliMass_outer_left p)
    (bernoulliMass_outer_right p) (edgeSum_pos p hp hp1)

/-- The exact coordinate derivative of the actual midpoint functional. -/
theorem hasDerivAt_midpointFunctional_update_gradient {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i : Fin (n+1)) :
    HasDerivAt (fun t => midpointFunctional q (Function.update p i t))
      (massGradientPairing q (n+1) (bernoulliMass p)
        (fun k => bernoulliMass (omitCoin p i) (k-1)-bernoulliMass (omitCoin p i) k)) (p i) := by
  have H := hasDerivAt_finiteMassFunctional_path q (n+1)
    (fun t => bernoulliMass (Function.update p i t))
    (fun k => bernoulliMass (omitCoin p i) (k-1)-bernoulliMass (omitCoin p i) k) (p i)
    (fun k => hasDerivAt_bernoulliMass_update p i (p i) k)
    (by intro k; simpa only [Function.update_eq_self, edgeSum] using edgeSum_pos p hp hp1 k)
    (by simp)
    (by simp only [show (((n+1:ℕ):ℤ)+1)-1=(n:ℤ)+1 by omega,
        bernoulliMass_outer_right]; rw [show ((n+1:ℕ):ℤ)+1=((n+2:ℕ):ℤ) by omega,
        bernoulliMass_natCast, coeff_bernoulliPolynomial_eq_zero _ _ (by omega)]; simp)
  simpa only [Function.update_eq_self, finiteMassFunctional_bernoulliMass] using H

lemma massGradientPairing_linear (q : ℝ) (n : ℕ) (g h l : ℤ → ℝ) (a b : ℝ) :
    massGradientPairing q n g (fun k => a*h k+b*l k) =
      a*massGradientPairing q n g h+b*massGradientPairing q n g l := by
  simp only [massGradientPairing, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

lemma massGradientPairing_sub (q : ℝ) (n : ℕ) (g h l : ℤ → ℝ) :
    massGradientPairing q n g (fun k => h k-l k) =
      massGradientPairing q n g h-massGradientPairing q n g l := by
  simp only [massGradientPairing, sub_mul, Finset.sum_sub_distrib]

/-- Pair the actual gradient with an integer shift of an actual Bernoulli background law. -/
def bernoulliGradientPairing {n m : ℕ} (q : ℝ) (p : Fin n → ℝ) (h : Fin m → ℝ) (j : ℤ) : ℝ :=
  massGradientPairing q n (bernoulliMass p) (fun k => bernoulliMass h (k-j))

/-- Euler and the actual coordinate derivative identify the omitted unshifted pairing. -/
theorem bernoulliGradientPairing_omit_zero {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i : Fin (n+1)) :
    bernoulliGradientPairing q p (omitCoin p i) 0 = q*midpointFunctional q p -
      p i * deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) := by
  have hd := (hasDerivAt_midpointFunctional_update_gradient q p hp hp1 i).deriv
  rw [massGradientPairing_sub] at hd
  have he : bernoulliMass p = (fun k => (1-p i)*bernoulliMass (omitCoin p i) k+
      p i*bernoulliMass (omitCoin p i) (k-1)) := by
    funext k
    simpa only [Function.update_eq_self] using bernoulliMass_update p i (p i) k
  have H : q*midpointFunctional q p =
      (1-p i)*bernoulliGradientPairing q p (omitCoin p i) 0+
        p i*bernoulliGradientPairing q p (omitCoin p i) 1 := by
    calc
      q*midpointFunctional q p = massGradientPairing q (n+1) (bernoulliMass p) (bernoulliMass p) :=
        (bernoulliMassGradient_euler q p hp hp1).symm
      _ = massGradientPairing q (n+1) (bernoulliMass p)
          (fun k => (1-p i)*bernoulliMass (omitCoin p i) k+p i*bernoulliMass (omitCoin p i) (k-1)) :=
        congrArg (massGradientPairing q (n+1) (bernoulliMass p)) he
      _ = _ := by
        simpa [bernoulliGradientPairing] using
          (massGradientPairing_linear q (n+1) (bernoulliMass p) (bernoulliMass (omitCoin p i))
            (fun k => bernoulliMass (omitCoin p i) (k-1)) (1-p i) (p i))
  change deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) =
    bernoulliGradientPairing q p (omitCoin p i) 1-bernoulliGradientPairing q p (omitCoin p i) 0 at hd
  rw [H, hd]
  ring

/-- Value zero and coordinate stationarity annihilate both shifts of the actual omitted law. -/
theorem bernoulliGradientPairing_omit_of_stationary {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i : Fin (n+1))
    (hzero : midpointFunctional q p = 0)
    (hstationary : deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) = 0) :
    bernoulliGradientPairing q p (omitCoin p i) 0 = 0 ∧
      bernoulliGradientPairing q p (omitCoin p i) 1 = 0 := by
  have h₀ := bernoulliGradientPairing_omit_zero q p hp hp1 i
  rw [hzero,hstationary] at h₀
  have h₀' : bernoulliGradientPairing q p (omitCoin p i) 0 = 0 := by simpa using h₀
  refine ⟨h₀',?_⟩
  have hd := (hasDerivAt_midpointFunctional_update_gradient q p hp hp1 i).deriv
  rw [massGradientPairing_sub, hstationary] at hd
  change 0=bernoulliGradientPairing q p (omitCoin p i) 1-bernoulliGradientPairing q p (omitCoin p i) 0 at hd
  linarith

/-- At value zero, a nonpositive coordinate derivative gives a nonnegative omitted pairing. -/
theorem bernoulliGradientPairing_omit_nonneg {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (i : Fin (n+1))
    (hzero : midpointFunctional q p = 0)
    (hstationary : deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) ≤ 0) :
    0 ≤ bernoulliGradientPairing q p (omitCoin p i) 0 := by
  rw [bernoulliGradientPairing_omit_zero q p hp hp1 i, hzero, mul_zero, zero_sub]
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hp i).le hstationary)

end RenyiMonotonicity
