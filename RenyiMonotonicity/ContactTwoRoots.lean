module

public import RenyiMonotonicity.ContactEvaluation

/-! Two-root evaluation of low-degree polynomial contact functionals. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

lemma coinFactor_eval (a x : ℝ) : (coinFactor a).eval x = 1-a+a*x := by
  simp [coinFactor]

lemma coinFactor_eval_root (a : ℝ) (ha : a ≠ 0) : (coinFactor a).eval (coinRoot a)=0 := by
  rw [coinFactor_eval]
  unfold coinRoot
  field_simp
  ring

lemma coinRoot_ne {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) : coinRoot a ≠ coinRoot b := by
  intro h
  unfold coinRoot at h
  have H := (div_eq_div_iff ha hb).mp h
  apply hab
  nlinarith

lemma linearMap_eq_two_eval (L : ℝ[X] →ₗ[ℝ] ℝ) (x y w v : ℝ) (N : ℕ)
    (hm : ∀ j ≤ N, L (X^j)=w*x^j+v*y^j) (Q : ℝ[X]) (hQ : Q.natDegree ≤ N) :
    L Q = w*Q.eval x+v*Q.eval y := by
  have he := Q.as_sum_range_C_mul_X_pow' (n := N+1) (by omega)
  rw [he]
  simp only [map_sum, eval_finsetSum, eval_smul,eval_pow,eval_X,Finset.mul_sum,
    ← smul_eq_C_mul, map_smul, smul_eq_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hm j (by have := Finset.mem_range.mp hj; omega)]
  ring

/-- Annihilation by a product of two distinct factors gives a sum of evaluations at its two roots. -/
theorem linearMap_two_factor_moments (L : ℝ[X] →ₗ[ℝ] ℝ) (p a : ℝ) (hp : p ≠ 0) (ha : a ≠ 0)
    (hpa : p ≠ a) (N : ℕ)
    (hz : ∀ j, j+2 ≤ N → L (coinFactor p*coinFactor a*X^j)=0) :
    ∃ w v : ℝ, ∀ j ≤ N, L (X^j)=w*coinRoot p^j+v*coinRoot a^j := by
  let x := coinRoot p
  let y := coinRoot a
  have hxy : x-y ≠ 0 := sub_ne_zero.mpr (coinRoot_ne hp ha hpa)
  let w := (L X-y*L 1)/(x-y)
  let v := (x*L 1-L X)/(x-y)
  refine ⟨w,v,?_⟩
  have hbase0 : L 1=w+v := by dsimp [w,v]; field_simp; ring
  have hbase1 : L X=w*x+v*y := by dsimp [w,v]; field_simp; ring
  have hrec (j : ℕ) (hj : j+2 ≤ N) :
      (1-p)*(1-a)*L (X^j)+(p+a-2*p*a)*L (X^(j+1))+p*a*L (X^(j+2))=0 := by
    have H := hz j hj
    rw [show coinFactor p*coinFactor a*X^j =
        ((1-p)*(1-a)) • X^j+(p+a-2*p*a) • X^(j+1)+(p*a) • X^(j+2) by
      simp only [coinFactor,smul_eq_C_mul,map_mul,map_sub,map_add,map_one,map_ofNat,pow_succ]; ring] at H
    simpa only [map_add,map_smul,smul_eq_mul] using H
  have hx : (1-p)*(1-a)+(p+a-2*p*a)*x+p*a*x^2=0 := by
    dsimp [x,coinRoot]
    field_simp
    ring
  have hy : (1-p)*(1-a)+(p+a-2*p*a)*y+p*a*y^2=0 := by
    dsimp [y,coinRoot]
    field_simp
    ring
  intro j
  induction j using Nat.twoStepInduction with
  | zero => intro _; simpa using hbase0
  | one => intro _; simpa using hbase1
  | more j ih ih' =>
    intro hj
    have H := hrec j hj
    rw [ih (by omega),ih' (by omega)] at H
    apply mul_left_cancel₀ (mul_ne_zero hp ha)
    change p*a*L (X^(j+2))=(p*a)*(w*x^(j+2)+v*y^(j+2))
    linear_combination H - (w*x^j)*hx - (v*y^j)*hy

end RenyiMonotonicity
