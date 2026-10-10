module

public import RenyiMonotonicity.GradientCubic
public import RenyiMonotonicity.MidpointFunctional

/-! Differentiating the actual finite edge functional with respect to its mass coordinates. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

/-- The finite midpoint functional on an integer-extended mass array, retaining both outer edges. -/
def finiteMassFunctional (q : ℝ) (n : ℕ) (g : ℤ → ℝ) : ℝ :=
  ∑ j : Fin (n+2), (g ((j.val : ℤ)-1) - g (j.val : ℤ)) *
    (g ((j.val : ℤ)-1) + g (j.val : ℤ))^(q-1)

/-- The mass-array functional agrees literally with the actual Bernoulli midpoint functional. -/
theorem finiteMassFunctional_bernoulliMass {n : ℕ} (q : ℝ) (p : Fin n → ℝ) :
    finiteMassFunctional q n (bernoulliMass p) = midpointFunctional q p := rfl

lemma hasDerivAt_left_mass_edge (q a b : ℝ) (hs : 0 < a+b) :
    HasDerivAt (fun t => (a-t)*(a+t)^(q-1)) (-massGradientScalar q b a) b := by
  have h₁ := (hasDerivAt_const b a).sub (hasDerivAt_id b)
  have h₂ := ((hasDerivAt_id b).const_add a).rpow_const (p := q-1) (Or.inl hs.ne')
  have he : (a+b)^(q-1) = (a+b)^(q-2)*(a+b) := by
    rw [show q-1 = (q-2)+1 by ring, Real.rpow_add hs, Real.rpow_one]
  convert h₁.mul h₂ using 1
  · rfl
  · simp only [id_eq, zero_sub, one_mul, Pi.sub_apply]
    unfold massGradientScalar
    rw [show q-1-1=q-2 by ring, he, add_comm b a]
    ring

lemma hasDerivAt_right_mass_edge (q b c : ℝ) (hs : 0 < b+c) :
    HasDerivAt (fun t => (t-c)*(t+c)^(q-1)) (massGradientScalar q b c) b := by
  have h₁ := (hasDerivAt_id b).sub_const c
  have h₂ := ((hasDerivAt_id b).add_const c).rpow_const (p := q-1) (Or.inl hs.ne')
  have he : (b+c)^(q-1) = (b+c)^(q-2)*(b+c) := by
    rw [show q-1 = (q-2)+1 by ring, Real.rpow_add hs, Real.rpow_one]
  convert h₁.mul h₂ using 1
  · rfl
  · simp only [id_eq, one_mul]
    unfold massGradientScalar
    rw [show q-1-1=q-2 by ring, he]
    ring

/-- The derivative with respect to one mass is exactly the difference of its two neighbour kernels.
Only the two adjacent edge sums need to be positive. -/
theorem hasDerivAt_finiteMassFunctional_update {n : ℕ} (q : ℝ) (g : ℤ → ℝ) (k : Fin (n+1))
    (hleft : 0 < g ((k.val : ℤ)-1) + g (k.val : ℤ))
    (hright : 0 < g (k.val : ℤ) + g ((k.val : ℤ)+1)) :
    HasDerivAt (fun t => finiteMassFunctional q n (Function.update g (k.val : ℤ) t))
      (massGradientEntry q (g ((k.val : ℤ)-1)) (g (k.val : ℤ)) (g ((k.val : ℤ)+1))) (g (k.val : ℤ)) := by
  classical
  have hne : k.castSucc ≠ k.succ := by intro h; have := congrArg Fin.val h; simp at this
  have heach (j : Fin (n+2)) : HasDerivAt
      (fun t => (Function.update g (k.val : ℤ) t ((j.val : ℤ)-1) - Function.update g (k.val : ℤ) t (j.val : ℤ)) *
        (Function.update g (k.val : ℤ) t ((j.val : ℤ)-1) + Function.update g (k.val : ℤ) t (j.val : ℤ))^(q-1))
      ((if j = k.castSucc then -massGradientScalar q (g (k.val : ℤ)) (g ((k.val : ℤ)-1)) else 0) +
        (if j = k.succ then massGradientScalar q (g (k.val : ℤ)) (g ((k.val : ℤ)+1)) else 0)) (g (k.val : ℤ)) := by
    by_cases hj : j = k.castSucc
    · subst j
      simpa [Function.update, show (k.val : ℤ)-1 ≠ k.val by omega, hne] using
        hasDerivAt_left_mass_edge q (g ((k.val : ℤ)-1)) (g (k.val : ℤ)) hleft
    · by_cases hj' : j = k.succ
      · subst j
        simpa [Function.update, show (k.val : ℤ)+1 ≠ k.val by omega, Nat.cast_add, Nat.cast_one, hne, Ne.symm hne] using
          hasDerivAt_right_mass_edge q (g (k.val : ℤ)) (g ((k.val : ℤ)+1)) hright
      · have h₁ : (j.val : ℤ) ≠ k.val := by
          intro h
          apply hj
          apply Fin.ext
          simpa using h
        have h₂ : (j.val : ℤ)-1 ≠ k.val := by
          intro h
          apply hj'
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        simpa [Function.update, h₁, h₂, hj, hj'] using
          hasDerivAt_const (g (k.val : ℤ)) ((g ((j.val : ℤ)-1) - g (j.val : ℤ)) *
            (g ((j.val : ℤ)-1) + g (j.val : ℤ))^(q-1))
  have H := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => heach j)
  convert H using 1
  · rfl
  · simp [massGradientEntry, Finset.sum_add_distrib]
    ring

/-- The actual Bernoulli mass gradient is the proved coordinate derivative of its full edge functional. -/
theorem hasDerivAt_bernoulliMassGradient {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : Fin (n+1)) :
    HasDerivAt (fun t => finiteMassFunctional q n (Function.update (bernoulliMass p) (k.val : ℤ) t))
      (bernoulliMassGradient q p (k.val : ℤ)) (bernoulliMass p (k.val : ℤ)) := by
  apply hasDerivAt_finiteMassFunctional_update
  · exact edgeSum_pos p hp hp1 k.castSucc
  · have H := edgeSum_pos p hp hp1 k.succ
    simpa [edgeSum, Nat.cast_add, Nat.cast_one] using H

end RenyiMonotonicity
