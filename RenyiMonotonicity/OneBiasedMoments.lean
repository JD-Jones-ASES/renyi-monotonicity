module
public import RenyiMonotonicity.CMBTail
public import RenyiMonotonicity.OneBiasedLaw

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace RenyiMonotonicity
set_option maxHeartbeats 1200000

def escortGrid (N : ℕ) (k : Fin (N+1)) : ℝ := ((N:ℝ)-2*k.val)/N

theorem escortGrid_sq (N : ℕ) (k : Fin (N+1)) : (escortGrid N k)^2=cmbGrid N k := rfl

theorem escortGrid_abs_le (N : ℕ) (hN : 0 < N) (k : Fin (N+1)) : |escortGrid N k| ≤ 1 := by
  have hh := cmbGrid_le_one N hN k
  rw [←escortGrid_sq] at hh
  exact abs_le_of_sq_le_sq (by simpa using hh) (by norm_num)

theorem escortGrid_rev (N : ℕ) (k : Fin (N+1)) : escortGrid N k.rev = -escortGrid N k := by
  have hk : k.val ≤ N := by omega
  simp only [escortGrid,Fin.val_rev,show N+1-(k.val+1)=N-k.val by omega,Nat.cast_sub hk]
  ring

def escortPowerMoment (N : ℕ) (q : ℝ) (d : ℕ) : ℝ :=
  ∑ k : Fin (N+1), (N.choose k.val:ℝ)^q*(escortGrid N k)^d

theorem escortPowerMoment_even (N : ℕ) (q : ℝ) (ell : ℕ) :
    escortPowerMoment N q (2*ell)=cmbMoment N q ell := by
  simp only [escortPowerMoment,cmbMoment,pow_mul,escortGrid_sq]

theorem escortPowerMoment_odd (N : ℕ) (q : ℝ) (ell : ℕ) :
    escortPowerMoment N q (2*ell+1)=0 := by
  have he (k : Fin (N+1)) : (N.choose k.rev.val:ℝ)^q*(escortGrid N k.rev)^(2*ell+1) =
      -((N.choose k.val:ℝ)^q*(escortGrid N k)^(2*ell+1)) := by
    rw [escortGrid_rev]
    have hk : N.choose k.rev.val = N.choose k.val := by
      rw [Fin.val_rev,show N+1-(k.val+1)=N-k.val by omega]
      exact Nat.choose_symm (by omega)
    rw [hk,Odd.neg_pow (show Odd (2*ell+1) from ⟨ell,by omega⟩)]
    ring
  have hh := Equiv.sum_comp Fin.revPerm
    (fun k : Fin (N+1) => (N.choose k.val:ℝ)^q*(escortGrid N k)^(2*ell+1))
  change (∑ k : Fin (N+1), (N.choose k.rev.val:ℝ)^q*(escortGrid N k.rev)^(2*ell+1)) = _ at hh
  simp_rw [he,Finset.sum_neg_distrib] at hh
  unfold escortPowerMoment
  linarith

def escortBinomialTransform (N : ℕ) (q δ : ℝ) (d : ℕ) : ℝ :=
  ∑ k : Fin (N+1), (N.choose k.val:ℝ)^q*(escortGrid N k)^d*(1+δ*escortGrid N k)^(q-1)

/-- Finite summation and the ordinary real binomial series give the exact
power expansion before parity selection. -/
theorem hasSum_escortBinomialTransform (N : ℕ) (hN : 0 < N) (q δ : ℝ)
    (hδ : |δ| < 1) (d : ℕ) :
    HasSum (fun j => Ring.choose (q-1) j*escortPowerMoment N q (j+d)*δ^j)
      (escortBinomialTransform N q δ d) := by
  have hs (k : Fin (N+1)) : |δ*escortGrid N k| < 1 := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg δ) (escortGrid_abs_le N hN k)).trans_lt hδ
  have hh := hasSum_sum (s := (Finset.univ : Finset (Fin (N+1))))
    (fun k _ => (hasSum_real_binomial (q-1) (δ*escortGrid N k) (hs k)).mul_left
      ((N.choose k.val:ℝ)^q*(escortGrid N k)^d))
  convert hh using 1
  · funext j
    simp only [escortPowerMoment,Finset.mul_sum,Finset.sum_mul,mul_pow,pow_add]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · rfl

/-- The even transforms use the actual even moments of the finite CMB law. -/
theorem hasSum_escortBinomial_even (N : ℕ) (hN : 0 < N) (q δ : ℝ)
    (hδ : |δ| < 1) (d : ℕ) :
    HasSum (fun ell => Ring.choose (q-1) (2*ell)*cmbMoment N q (ell+d)*δ^(2*ell))
      (escortBinomialTransform N q δ (2*d)) := by
  let f := fun j => Ring.choose (q-1) j*escortPowerMoment N q (j+2*d)*δ^j
  have hs : HasSum f (escortBinomialTransform N q δ (2*d)) := hasSum_escortBinomialTransform N hN q δ hδ (2*d)
  have he := hs.summable.comp_injective (show Function.Injective (fun j : ℕ => 2*j) by intro i j hij; dsimp at hij; omega)
  have ho : HasSum (fun j => f (2*j+1)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0) using 1
    funext j
    simp only [f,show 2*j+1+2*d=2*(j+d)+1 by omega,escortPowerMoment_odd,mul_zero,zero_mul]
  have heq := (he.hasSum.even_add_odd ho).unique hs
  simp only [add_zero] at heq
  rw [←heq]
  convert he.hasSum using 1
  funext j
  simp only [Function.comp_apply,f,show 2*j+2*d=2*(j+d) by omega,escortPowerMoment_even]

/-- The odd first transform contains exactly the next even moment. -/
theorem hasSum_escortBinomial_odd (N : ℕ) (hN : 0 < N) (q δ : ℝ)
    (hδ : |δ| < 1) :
    HasSum (fun ell => Ring.choose (q-1) (2*ell+1)*cmbMoment N q (ell+1)*δ^(2*ell+1))
      (escortBinomialTransform N q δ 1) := by
  let f := fun j => Ring.choose (q-1) j*escortPowerMoment N q (j+1)*δ^j
  have hs : HasSum f (escortBinomialTransform N q δ 1) := hasSum_escortBinomialTransform N hN q δ hδ 1
  have ho := hs.summable.comp_injective (show Function.Injective (fun j : ℕ => 2*j+1) by intro i j hij; dsimp at hij; omega)
  have he : HasSum (fun j => f (2*j)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0) using 1
    funext j
    simp only [f,escortPowerMoment_odd,mul_zero,zero_mul]
  have heq := (he.even_add_odd ho.hasSum).unique hs
  simp only [zero_add] at heq
  rw [←heq]
  convert ho.hasSum using 1
  funext j
  simp only [Function.comp_apply,f,show 2*j+1+1=2*(j+1) by omega,escortPowerMoment_even]

end RenyiMonotonicity
