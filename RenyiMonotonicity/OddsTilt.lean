module

public import RenyiMonotonicity.ContactMoments

/-! Exact common odds tilt and positive homogeneity of the mass functional. -/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Polynomial Filter

namespace RenyiMonotonicity

def oddsTilt {n : ℕ} (p : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  p i * (1+t) / (1+p i*t)

def oddsNormalizer {n : ℕ} (p : Fin n → ℝ) (t : ℝ) : ℝ := ∏ i, (1+p i*t)

@[simp] theorem oddsTilt_zero {n : ℕ} (p : Fin n → ℝ) : oddsTilt p 0 = p := by
  funext i
  simp [oddsTilt]

@[simp] theorem oddsNormalizer_zero {n : ℕ} (p : Fin n → ℝ) : oddsNormalizer p 0 = 1 := by
  simp [oddsNormalizer]

theorem coinFactor_oddsTilt (p t : ℝ) (h : 1+p*t ≠ 0) :
    C (1+p*t) * coinFactor (p*(1+t)/(1+p*t)) = (coinFactor p).comp (C (1+t)*X) := by
  simp only [coinFactor, add_comp, C_comp, mul_comp, X_comp]
  have h1 : (1+p*t)*(1-p*(1+t)/(1+p*t)) = 1-p := by field_simp; ring
  have h2 : (1+p*t)*(p*(1+t)/(1+p*t)) = p*(1+t) := mul_div_cancel₀ _ h
  rw [mul_add, ← mul_assoc, ← C_mul, h1, ← C_mul, h2, map_mul]
  ring

theorem bernoulliPolynomial_oddsTilt {n : ℕ} (p : Fin n → ℝ) (t : ℝ)
    (hd : ∀ i, 1+p i*t ≠ 0) :
    C (oddsNormalizer p t) * bernoulliPolynomial (oddsTilt p t) =
      (bernoulliPolynomial p).comp (C (1+t)*X) := by
  change C (∏ i, (1+p i*t)) * ∏ i, coinFactor (oddsTilt p t i) = _
  rw [map_prod, ← Finset.prod_mul_distrib]
  simp_rw [oddsTilt, coinFactor_oddsTilt _ _ (hd _)]
  change _ = (∏ i, coinFactor (p i)).comp (C (1+t)*X)
  exact (prod_comp Finset.univ (fun i => coinFactor (p i)) (C (1+t)*X)).symm

/-- The unnormalized tilted law has exact geometric count weights. -/
theorem bernoulliMass_oddsTilt {n : ℕ} (p : Fin n → ℝ) (t : ℝ)
    (hd : ∀ i, 1+p i*t ≠ 0) (k : ℤ) :
    oddsNormalizer p t * bernoulliMass (oddsTilt p t) k =
      (1+t)^k.toNat * bernoulliMass p k := by
  by_cases hk : 0 ≤ k
  · obtain ⟨k,rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have H := congrArg (fun P : ℝ[X] => P.coeff k) (bernoulliPolynomial_oddsTilt p t hd)
    simp only [coeff_C_mul, comp_C_mul_X_coeff] at H
    simpa only [bernoulliMass_natCast, Int.toNat_natCast, mul_comm] using H
  · simp [bernoulliMass_neg _ _ (lt_of_not_ge hk)]

/-- Homogeneity is valid for the exact finite mass functional at any positive scale. -/
theorem finiteMassFunctional_scale (q : ℝ) (n : ℕ) (g : ℤ → ℝ) (c : ℝ)
    (hc : 0 < c) (hs : ∀ k : Fin (n+2), 0 ≤ g ((k.val:ℤ)-1)+g k.val) :
    finiteMassFunctional q n (fun k => c*g k) = c^q*finiteMassFunctional q n g := by
  unfold finiteMassFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_sub, ← mul_add, Real.mul_rpow hc.le (hs k)]
  have he : c * c^(q-1) = c^q := by
    calc
      c*c^(q-1) = c^(1:ℝ)*c^(q-1) := by rw [Real.rpow_one]
      _ = c^q := by rw [← Real.rpow_add hc]; congr 1; ring
  calc
    (c*(g ((k.val:ℤ)-1)-g k.val))*(c^(q-1)*(g ((k.val:ℤ)-1)+g k.val)^(q-1)) =
      (c*c^(q-1))*((g ((k.val:ℤ)-1)-g k.val)*(g ((k.val:ℤ)-1)+g k.val)^(q-1)) := by ring
    _ = _ := by rw [he]

/-- Every interior half-cube point has a two-sided admissible common odds tilt. -/
theorem oddsTilt_eventually_interior {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i < 1/2) :
    ∀ᶠ t in 𝓝 (0:ℝ), (∀ i, oddsTilt p t i ∈ Set.Ioo (0:ℝ) (1/2)) ∧
      (∀ i, 0 < 1+p i*t) ∧ 0 < 1+t := by
  have hcoin (i : Fin n) : ContinuousAt (fun t => oddsTilt p t i) 0 := by
    unfold oddsTilt
    fun_prop (disch := norm_num)
  have hden (i : Fin n) : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+p i*t :=
    (show ContinuousAt (fun t : ℝ => 1+p i*t) 0 by fun_prop).eventually (isOpen_Ioi.mem_nhds (by norm_num))
  have hinside (i : Fin n) : ∀ᶠ t in 𝓝 (0:ℝ), oddsTilt p t i ∈ Set.Ioo (0:ℝ) (1/2) :=
    (hcoin i).eventually (isOpen_Ioo.mem_nhds (by simpa using And.intro (hp i) (hpHalf i)))
  have hbase : ∀ᶠ t in 𝓝 (0:ℝ), 0 < 1+t :=
    (show ContinuousAt (fun t : ℝ => 1+t) 0 by fun_prop).eventually (isOpen_Ioi.mem_nhds (by norm_num))
  filter_upwards [Filter.eventually_all.mpr hinside, Filter.eventually_all.mpr hden, hbase] with t ht hd ht1
  exact ⟨ht, hd, ht1⟩

/-- At a zero coin minimum, positive homogeneity removes the tilt normalizer. -/
theorem oddsTilt_mass_localMin {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i < 1/2)
    (hD : midpointFunctional q p = 0)
    (hmin : ∀ r : Fin n → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q p ≤ midpointFunctional q r) :
    IsLocalMin (fun t => finiteMassFunctional q n (fun k => (1+t)^k.toNat*bernoulliMass p k)) 0 := by
  filter_upwards [oddsTilt_eventually_interior p hp hpHalf] with t ht
  have hn : 0 < oddsNormalizer p t := Finset.prod_pos (fun i _ => ht.2.1 i)
  have hmass : (fun k => (1+t)^k.toNat*bernoulliMass p k) =
      fun k => oddsNormalizer p t * bernoulliMass (oddsTilt p t) k := by
    funext k
    exact (bernoulliMass_oddsTilt p t (fun i => (ht.2.1 i).ne') k).symm
  simp only [add_zero, one_pow, one_mul, finiteMassFunctional_bernoulliMass, hD]
  rw [hmass, finiteMassFunctional_scale q n _ _ hn,
    finiteMassFunctional_bernoulliMass]
  · exact mul_nonneg (Real.rpow_nonneg hn.le q) (by simpa [hD] using hmin _ (fun i => ⟨(ht.1 i).1.le, (ht.1 i).2.le⟩))
  · intro k
    exact add_nonneg (bernoulliMass_nonneg _ (fun i => (ht.1 i).1.le) (fun i => by linarith [(ht.1 i).2]) _) (bernoulliMass_nonneg _ (fun i => (ht.1 i).1.le) (fun i => by linarith [(ht.1 i).2]) _)

end RenyiMonotonicity
