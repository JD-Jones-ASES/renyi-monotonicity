module
public import Mathlib

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RenyiMonotonicity

lemma power_cross_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    {k L : ℕ} (hk : k ≤ L) : 0 ≤ x^k*y^L-y^k*x^L := by
  have hy : 0 ≤ y := hx.trans hxy
  have hyL : y^L = y^k*y^(L-k) := by rw [←pow_add,Nat.add_sub_of_le hk]
  have hxL : x^L = x^k*x^(L-k) := by rw [←pow_add,Nat.add_sub_of_le hk]
  have he : x^k*y^L-y^k*x^L = x^k*y^k*(y^(L-k)-x^(L-k)) := by rw [hyL,hxL]; ring
  rw [he]
  exact mul_nonneg (mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _))
    (sub_nonneg.mpr (pow_le_pow_left₀ hx hxy _))

lemma power_cross_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    {k L : ℕ} (hk : k < L) : 0 < x^k*y^L-y^k*x^L := by
  have hy : 0 < y := hx.trans hxy
  have hyL : y^L = y^k*y^(L-k) := by rw [←pow_add,Nat.add_sub_of_le hk.le]
  have hxL : x^L = x^k*x^(L-k) := by rw [←pow_add,Nat.add_sub_of_le hk.le]
  have he : x^k*y^L-y^k*x^L = x^k*y^k*(y^(L-k)-x^(L-k)) := by rw [hyL,hxL]; ring
  rw [he]
  exact mul_pos (mul_pos (pow_pos hx _) (pow_pos hy _))
    (sub_pos.mpr (pow_lt_pow_left₀ hxy hx.le (by omega)))

/-- A single change from nonnegative to nonpositive coefficients makes the
weighted sum strictly decrease between any two points of the unit interval.
Only convergence at those two interior points is needed. -/
theorem signed_series_cross_pos (a : ℕ → ℝ) (L : ℕ)
    (hleft : ∀ k < L, 0 ≤ a k) (hright : ∀ k, L ≤ k → a k ≤ 0)
    (hstrict : a (L+1) < 0) {x y A B : ℝ} (hx : 0 < x) (hxy : x < y)
    (hA : HasSum (fun k => a k*x^(2*k)) A)
    (hB : HasSum (fun k => a k*y^(2*k)) B) :
    0 < A*y^(2*L)-B*x^(2*L) := by
  let f : ℕ → ℝ := fun k => a k*x^(2*k)*y^(2*L)-a k*y^(2*k)*x^(2*L)
  have hs : HasSum f (A*y^(2*L)-B*x^(2*L)) :=
    (hA.mul_right (y^(2*L))).sub (hB.mul_right (x^(2*L)))
  have hf (k : ℕ) : 0 ≤ f k := by
    have he : f k = a k*(x^(2*k)*y^(2*L)-y^(2*k)*x^(2*L)) := by dsimp [f]; ring
    rw [he]
    rcases lt_or_ge k L with hk | hk
    · exact mul_nonneg (hleft k hk) (power_cross_nonneg hx.le hxy.le (by omega))
    · have hh := power_cross_nonneg hx.le hxy.le (k := 2*L) (L := 2*k) (by omega)
      exact mul_nonneg_of_nonpos_of_nonpos (hright k hk) (by nlinarith)
  have hstrict' : 0 < f (L+1) := by
    have hh := power_cross_pos hx hxy (k := 2*L) (L := 2*(L+1)) (by omega)
    have he : f (L+1) = (-a (L+1))*(x^(2*L)*y^(2*(L+1))-y^(2*L)*x^(2*(L+1))) := by dsimp [f]; ring
    rw [he]
    exact mul_pos (neg_pos.mpr hstrict) hh
  rw [←hs.tsum_eq]
  exact hs.summable.tsum_pos hf (L+1) hstrict'

/-- An interior power series with one coefficient sign change and a zero
boundary limit is strictly positive. Endpoint absolute convergence is not
required: the boundary limit is supplied by the actual finite-law functional. -/
theorem signed_series_pos_of_boundary_zero (a : ℕ → ℝ) (F : ℝ → ℝ) (L : ℕ)
    (hleft : ∀ k < L, 0 ≤ a k) (hright : ∀ k, L ≤ k → a k ≤ 0)
    (hstrict : a (L+1) < 0)
    (hsum : ∀ x ∈ Ioo (0:ℝ) 1, HasSum (fun k => a k*x^(2*k)) (F x))
    (hlim : Tendsto F (𝓝[<] (1:ℝ)) (𝓝 0)) :
    ∀ x ∈ Ioo (0:ℝ) 1, 0 < F x := by
  have hnonneg (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0 ≤ F x := by
    have ht : Tendsto (fun y : ℝ => F x*y^(2*L)-F y*x^(2*L)) (𝓝[<] (1:ℝ)) (𝓝 (F x)) := by
      have h := ((((tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 (1:ℝ)) (𝓝 1)).mono_left nhdsWithin_le_nhds).pow (2*L)).const_mul (F x)).sub
        (hlim.mul_const (x^(2*L)))
      simpa using h
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hx.2).filter_mono nhdsWithin_le_nhds] with y hy hxy
    exact (signed_series_cross_pos a L hleft hright hstrict hx.1 hxy
      (hsum x hx) (hsum y ⟨hx.1.trans hxy,hy⟩)).le
  intro x hx
  let y := (x+1)/2
  have hxy : x < y := by dsimp [y]; linarith [hx.2]
  have hy : y ∈ Ioo (0:ℝ) 1 := ⟨hx.1.trans hxy,by dsimp [y]; linarith [hx.2]⟩
  have hc := signed_series_cross_pos a L hleft hright hstrict hx.1 hxy (hsum x hx) (hsum y hy)
  have hprod : 0 < F x*y^(2*L) := by
    have := mul_nonneg (hnonneg y hy) (pow_nonneg hx.1.le (2*L))
    linarith
  exact (mul_pos_iff.mp hprod).resolve_right (by intro h; exact (not_lt_of_ge (pow_nonneg hy.1.le _)) h.2) |>.1

end RenyiMonotonicity
