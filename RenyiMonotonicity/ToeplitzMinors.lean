module

public import RenyiMonotonicity.CubicIdentities

@[expose] public section

namespace RenyiMonotonicity

/-- Three-by-three determinant as a division-free scalar expression. -/
def detThree (a b c d e f g h i : ℝ) : ℝ :=
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g

/-- A three-row Toeplitz minor of an integer-indexed coefficient sequence. -/
noncomputable def toeplitzThree (g : ℤ → ℝ) (r₀ r₁ r₂ c₀ c₁ c₂ : ℤ) : ℝ :=
  detThree (g (c₀ - r₀)) (g (c₁ - r₀)) (g (c₂ - r₀))
    (g (c₀ - r₁)) (g (c₁ - r₁)) (g (c₂ - r₁))
    (g (c₀ - r₂)) (g (c₁ - r₂)) (g (c₂ - r₂))

theorem toeplitzThree_rows_eq_left (g : ℤ → ℝ) (r r₂ c₀ c₁ c₂ : ℤ) :
    toeplitzThree g r r r₂ c₀ c₁ c₂ = 0 := by
  unfold toeplitzThree detThree
  ring

theorem toeplitzThree_rows_eq_right (g : ℤ → ℝ) (r₀ r c₀ c₁ c₂ : ℤ) :
    toeplitzThree g r₀ r r c₀ c₁ c₂ = 0 := by
  unfold toeplitzThree detThree
  ring

/-- Expanding the convolution in the three rows gives exactly eight ordered minors. -/
theorem toeplitzThree_convolution (g : ℤ → ℝ) (u v : ℝ)
    (r₀ r₁ r₂ c₀ c₁ c₂ : ℤ) :
    toeplitzThree (fun k => u * g k + v * g (k - 1)) r₀ r₁ r₂ c₀ c₁ c₂ =
      u ^ 3 * toeplitzThree g r₀ r₁ r₂ c₀ c₁ c₂ +
      u ^ 2 * v * (toeplitzThree g (r₀ + 1) r₁ r₂ c₀ c₁ c₂ +
        toeplitzThree g r₀ (r₁ + 1) r₂ c₀ c₁ c₂ +
        toeplitzThree g r₀ r₁ (r₂ + 1) c₀ c₁ c₂) +
      u * v ^ 2 * (toeplitzThree g (r₀ + 1) (r₁ + 1) r₂ c₀ c₁ c₂ +
        toeplitzThree g (r₀ + 1) r₁ (r₂ + 1) c₀ c₁ c₂ +
        toeplitzThree g r₀ (r₁ + 1) (r₂ + 1) c₀ c₁ c₂) +
      v ^ 3 * toeplitzThree g (r₀ + 1) (r₁ + 1) (r₂ + 1) c₀ c₁ c₂ := by
  unfold toeplitzThree detThree
  simp only [sub_add_eq_sub_sub]
  ring

private theorem reversed_delta_product {r s c d : ℤ} (hrs : r ≤ s) (hcd : c < d) :
    (if d = r then (1 : ℝ) else 0) * (if c = s then 1 else 0) = 0 := by
  split_ifs <;> simp_all
  omega

/-- Ordered minors of the identity Toeplitz matrix are nonnegative. -/
theorem toeplitzThree_pointMass_nonneg (r₀ r₁ r₂ c₀ c₁ c₂ : ℤ)
    (hr₀ : r₀ ≤ r₁) (hr₁ : r₁ ≤ r₂) (hc₀ : c₀ < c₁) (hc₁ : c₁ < c₂) :
    0 ≤ toeplitzThree (fun k => if k = 0 then 1 else 0) r₀ r₁ r₂ c₀ c₁ c₂ := by
  have hr₂ := le_trans hr₀ hr₁
  have hc₂ := lt_trans hc₀ hc₁
  have h₁ := congrArg (fun x : ℝ => (if c₀ = r₀ then 1 else 0) * x)
    (reversed_delta_product hr₁ hc₁)
  have h₂ := congrArg (fun x : ℝ => (if c₂ = r₂ then 1 else 0) * x)
    (reversed_delta_product hr₀ hc₀)
  have h₃ := congrArg (fun x : ℝ => (if c₁ = r₁ then 1 else 0) * x)
    (reversed_delta_product hr₂ hc₂)
  have h₄ := congrArg (fun x : ℝ => (if c₂ = r₁ then 1 else 0) * x)
    (reversed_delta_product hr₂ hc₀)
  have h₅ := congrArg (fun x : ℝ => (if c₁ = r₂ then 1 else 0) * x)
    (reversed_delta_product hr₀ hc₂)
  have hd : 0 ≤ (if c₀ = r₀ then (1 : ℝ) else 0) *
      (if c₁ = r₁ then 1 else 0) * (if c₂ = r₂ then 1 else 0) := by positivity
  simp only [toeplitzThree, detThree, sub_eq_zero]
  nlinarith [h₁, h₂, h₃, h₄, h₅]

@[simp] theorem bernoulliMass_empty (p : Fin 0 → ℝ) (k : ℤ) :
    bernoulliMass p k = if k = 0 then 1 else 0 := by
  by_cases hk : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp [bernoulliMass, Polynomial.coeff_one]
  · have hn : k < 0 := lt_of_not_ge hk
    have hne : k ≠ 0 := by omega
    simp [bernoulliMass, hk, hne]

/-- Three-row total positivity of every actual Bernoulli convolution. The induction
uses only ordered rows; a shifted row can collide with the next row but cannot
cross it, and coincident-row determinants vanish. -/
theorem bernoulli_toeplitzThree_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    (r₀ r₁ r₂ c₀ c₁ c₂ : ℤ)
    (hr₀ : r₀ ≤ r₁) (hr₁ : r₁ ≤ r₂) (hc₀ : c₀ < c₁) (hc₁ : c₁ < c₂) :
    0 ≤ toeplitzThree (bernoulliMass p) r₀ r₁ r₂ c₀ c₁ c₂ := by
  induction n generalizing r₀ r₁ r₂ with
  | zero =>
      have heq : bernoulliMass p = fun k => if k = 0 then 1 else 0 := by
        funext k
        exact bernoulliMass_empty p k
      rw [heq]
      exact toeplitzThree_pointMass_nonneg r₀ r₁ r₂ c₀ c₁ c₂ hr₀ hr₁ hc₀ hc₁
  | succ n ih =>
      by_cases h₀ : r₀ = r₁
      · subst r₁
        simp only [toeplitzThree_rows_eq_left, le_refl]
      by_cases h₁ : r₁ = r₂
      · subst r₂
        simp only [toeplitzThree_rows_eq_right, le_refl]
      have heq : bernoulliMass p = fun k =>
          (1 - p 0) * bernoulliMass (Fin.tail p) k +
            p 0 * bernoulliMass (Fin.tail p) (k - 1) := by
        funext k
        simpa only [Fin.cons_self_tail] using bernoulliMass_cons (p 0) (Fin.tail p) k
      have ht : ∀ i, 0 ≤ Fin.tail p i := fun i => hp i.succ
      have ht₁ : ∀ i, Fin.tail p i ≤ 1 := fun i => hp₁ i.succ
      have h000 := ih (Fin.tail p) ht ht₁ r₀ r₁ r₂ hr₀ hr₁
      have h100 := ih (Fin.tail p) ht ht₁ (r₀ + 1) r₁ r₂ (by omega) hr₁
      have h010 := ih (Fin.tail p) ht ht₁ r₀ (r₁ + 1) r₂ (by omega) (by omega)
      have h001 := ih (Fin.tail p) ht ht₁ r₀ r₁ (r₂ + 1) hr₀ (by omega)
      have h110 := ih (Fin.tail p) ht ht₁ (r₀ + 1) (r₁ + 1) r₂ (by omega) (by omega)
      have h101 := ih (Fin.tail p) ht ht₁ (r₀ + 1) r₁ (r₂ + 1) (by omega) (by omega)
      have h011 := ih (Fin.tail p) ht ht₁ r₀ (r₁ + 1) (r₂ + 1) (by omega) (by omega)
      have h111 := ih (Fin.tail p) ht ht₁ (r₀ + 1) (r₁ + 1) (r₂ + 1) (by omega) (by omega)
      have hu : 0 ≤ 1 - p 0 := sub_nonneg.mpr (hp₁ 0)
      have hv : 0 ≤ p 0 := hp 0
      rw [heq, toeplitzThree_convolution]
      positivity

/-- Shifting every selected row is the same as shifting every selected column
in the opposite direction. -/
theorem toeplitzThree_shift_rows (g : ℤ → ℝ) (r₀ r₁ r₂ c₀ c₁ c₂ : ℤ) :
    toeplitzThree g (r₀ + 1) (r₁ + 1) (r₂ + 1) c₀ c₁ c₂ =
      toeplitzThree g r₀ r₁ r₂ (c₀ - 1) (c₁ - 1) (c₂ - 1) := by
  have h (c r : ℤ) : c - (r + 1) = c - 1 - r := by omega
  simp only [toeplitzThree, h]

/-- Every contiguous three-row minor on the coefficient support is strictly
positive when every coin parameter is strictly between zero and one. -/
theorem bernoulli_toeplitzThree_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    0 < toeplitzThree (bernoulliMass p) 0 1 2 k (k + 1) (k + 2) := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      norm_num [toeplitzThree, detThree, bernoulliMass_empty]
  | succ n ih =>
      have heq : bernoulliMass p = fun k =>
          (1 - p 0) * bernoulliMass (Fin.tail p) k +
            p 0 * bernoulliMass (Fin.tail p) (k - 1) := by
        funext k
        simpa only [Fin.cons_self_tail] using bernoulliMass_cons (p 0) (Fin.tail p) k
      have ht : ∀ i, 0 < Fin.tail p i := fun i => hp i.succ
      have ht₁ : ∀ i, Fin.tail p i < 1 := fun i => hp₁ i.succ
      have hn (r₀ r₁ r₂ : ℤ) (h₀ : r₀ ≤ r₁) (h₁ : r₁ ≤ r₂) :
          0 ≤ toeplitzThree (bernoulliMass (Fin.tail p)) r₀ r₁ r₂ k (k + 1) (k + 2) :=
        bernoulli_toeplitzThree_nonneg (Fin.tail p) (fun i => le_of_lt (ht i))
          (fun i => le_of_lt (ht₁ i)) r₀ r₁ r₂ k (k + 1) (k + 2) h₀ h₁
          (by omega) (by omega)
      have h000 := hn 0 1 2 (by omega) (by omega)
      have h100 := hn 1 1 2 (by omega) (by omega)
      have h010 := hn 0 2 2 (by omega) (by omega)
      have h001 := hn 0 1 3 (by omega) (by omega)
      have h110 := hn 1 2 2 (by omega) (by omega)
      have h101 := hn 1 1 3 (by omega) (by omega)
      have h011 := hn 0 2 3 (by omega) (by omega)
      have h111 := hn 1 2 3 (by omega) (by omega)
      have hu : 0 < 1 - p 0 := sub_pos.mpr (hp₁ 0)
      have hv : 0 < p 0 := hp 0
      rw [heq, toeplitzThree_convolution]
      norm_num only at ⊢
      by_cases hk : k ≤ n
      · have h000pos := ih (Fin.tail p) ht ht₁ k hk₀ hk
        positivity
      · have h111pos : 0 < toeplitzThree (bernoulliMass (Fin.tail p))
            1 2 3 k (k + 1) (k + 2) := by
          have hs := toeplitzThree_shift_rows (bernoulliMass (Fin.tail p)) 0 1 2
            k (k + 1) (k + 2)
          norm_num only at hs
          rw [hs]
          convert ih (Fin.tail p) ht ht₁ (k - 1) (by omega) (by omega) using 1
          congr 1 <;> omega
        positivity

/-- The contiguous Toeplitz determinant is the expanded cubic used in the HJ
identities, with all boundary entries supplied by the actual zero extension. -/
theorem toeplitzThree_eq_toeplitzCubic (g : ℤ → ℝ) (k : ℤ) :
    toeplitzThree g 0 1 2 k (k + 1) (k + 2) =
      toeplitzCubic (g (k - 2)) (g (k - 1)) (g k) (g (k + 1)) (g (k + 2)) := by
  unfold toeplitzThree detThree toeplitzCubic
  have h₁ : k + 1 - 2 = k - 1 := by omega
  have h₂ : k + 2 - 1 = k + 1 := by omega
  simp only [sub_zero, add_sub_cancel_right, h₁, h₂]
  ring

/-- Nonnegativity of every omitted-law HJ cubic, including outer indices. -/
theorem omittedToeplitzCubic_nonneg {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1) (i : Fin (n + 1)) (k : ℤ) :
    0 ≤ omittedToeplitzCubic p i k := by
  unfold omittedToeplitzCubic
  rw [← toeplitzThree_eq_toeplitzCubic]
  exact bernoulli_toeplitzThree_nonneg (omitCoin p i)
    (fun j => hp (i.succAbove j)) (fun j => hp₁ (i.succAbove j))
    0 1 2 k (k + 1) (k + 2) (by omega) (by omega) (by omega) (by omega)

/-- Strict positivity of every omitted-law HJ cubic on its full closed support. -/
theorem omittedToeplitzCubic_pos {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (i : Fin (n + 1)) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) : 0 < omittedToeplitzCubic p i k := by
  unfold omittedToeplitzCubic
  rw [← toeplitzThree_eq_toeplitzCubic]
  exact bernoulli_toeplitzThree_pos (omitCoin p i)
    (fun j => hp (i.succAbove j)) (fun j => hp₁ (i.succAbove j)) k hk₀ hkn

/-- A two-row Toeplitz minor. -/
noncomputable def toeplitzTwo (g : ℤ → ℝ) (r₀ r₁ c₀ c₁ : ℤ) : ℝ :=
  g (c₀ - r₀) * g (c₁ - r₁) - g (c₁ - r₀) * g (c₀ - r₁)

@[simp] theorem toeplitzTwo_rows_eq (g : ℤ → ℝ) (r c₀ c₁ : ℤ) :
    toeplitzTwo g r r c₀ c₁ = 0 := by simp [toeplitzTwo, mul_comm]

/-- The corresponding four-term row expansion for two-row minors. -/
theorem toeplitzTwo_convolution (g : ℤ → ℝ) (u v : ℝ) (r₀ r₁ c₀ c₁ : ℤ) :
    toeplitzTwo (fun k => u * g k + v * g (k - 1)) r₀ r₁ c₀ c₁ =
      u ^ 2 * toeplitzTwo g r₀ r₁ c₀ c₁ +
      u * v * (toeplitzTwo g (r₀ + 1) r₁ c₀ c₁ +
        toeplitzTwo g r₀ (r₁ + 1) c₀ c₁) +
      v ^ 2 * toeplitzTwo g (r₀ + 1) (r₁ + 1) c₀ c₁ := by
  unfold toeplitzTwo
  simp only [sub_add_eq_sub_sub]
  ring

/-- All ordered two-row minors of every actual Bernoulli law are nonnegative. -/
theorem bernoulli_toeplitzTwo_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    (r₀ r₁ c₀ c₁ : ℤ) (hr : r₀ ≤ r₁) (hc : c₀ < c₁) :
    0 ≤ toeplitzTwo (bernoulliMass p) r₀ r₁ c₀ c₁ := by
  induction n generalizing r₀ r₁ with
  | zero =>
      simp only [toeplitzTwo, bernoulliMass_empty, sub_eq_zero]
      rw [reversed_delta_product hr hc, sub_zero]
      positivity
  | succ n ih =>
      by_cases he : r₀ = r₁
      · subst r₁
        simp
      have heq : bernoulliMass p = fun k =>
          (1 - p 0) * bernoulliMass (Fin.tail p) k +
            p 0 * bernoulliMass (Fin.tail p) (k - 1) := by
        funext k
        simpa only [Fin.cons_self_tail] using bernoulliMass_cons (p 0) (Fin.tail p) k
      have ht : ∀ i, 0 ≤ Fin.tail p i := fun i => hp i.succ
      have ht₁ : ∀ i, Fin.tail p i ≤ 1 := fun i => hp₁ i.succ
      have h00 := ih (Fin.tail p) ht ht₁ r₀ r₁ hr
      have h10 := ih (Fin.tail p) ht ht₁ (r₀ + 1) r₁ (by omega)
      have h01 := ih (Fin.tail p) ht ht₁ r₀ (r₁ + 1) (by omega)
      have h11 := ih (Fin.tail p) ht ht₁ (r₀ + 1) (r₁ + 1) (by omega)
      have hu : 0 ≤ 1 - p 0 := sub_nonneg.mpr (hp₁ 0)
      have hv : 0 ≤ p 0 := hp 0
      rw [heq, toeplitzTwo_convolution]
      positivity

/-- Strict contiguous two-row minors, including the support endpoints. -/
theorem bernoulli_toeplitzTwo_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    0 < toeplitzTwo (bernoulliMass p) 0 1 k (k + 1) := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      norm_num [toeplitzTwo, bernoulliMass_empty]
  | succ n ih =>
      have heq : bernoulliMass p = fun k =>
          (1 - p 0) * bernoulliMass (Fin.tail p) k +
            p 0 * bernoulliMass (Fin.tail p) (k - 1) := by
        funext k
        simpa only [Fin.cons_self_tail] using bernoulliMass_cons (p 0) (Fin.tail p) k
      have ht : ∀ i, 0 < Fin.tail p i := fun i => hp i.succ
      have ht₁ : ∀ i, Fin.tail p i < 1 := fun i => hp₁ i.succ
      have hn (r₀ r₁ : ℤ) (hr : r₀ ≤ r₁) :
          0 ≤ toeplitzTwo (bernoulliMass (Fin.tail p)) r₀ r₁ k (k + 1) :=
        bernoulli_toeplitzTwo_nonneg (Fin.tail p) (fun i => le_of_lt (ht i))
          (fun i => le_of_lt (ht₁ i)) r₀ r₁ k (k + 1) hr (by omega)
      have h00 := hn 0 1 (by omega)
      have h10 := hn 1 1 (by omega)
      have h01 := hn 0 2 (by omega)
      have h11 := hn 1 2 (by omega)
      have hu : 0 < 1 - p 0 := sub_pos.mpr (hp₁ 0)
      have hv : 0 < p 0 := hp 0
      rw [heq, toeplitzTwo_convolution]
      norm_num only at ⊢
      by_cases hk : k ≤ n
      · have h00pos := ih (Fin.tail p) ht ht₁ k hk₀ hk
        positivity
      · have h11pos : 0 < toeplitzTwo (bernoulliMass (Fin.tail p)) 1 2 k (k + 1) := by
          have hi := ih (Fin.tail p) ht ht₁ (k - 1) (by omega) (by omega)
          have h₁ : k - 1 + 1 = k := by omega
          have h₂ : k + 1 - 2 = k - 1 := by omega
          simpa only [toeplitzTwo, sub_zero, h₁, h₂, add_sub_cancel_right,
            sub_sub, show (1 : ℤ) + 1 = 2 by omega] using hi
        positivity

/-- Strict log-concavity of the actual mass on the full count support. -/
theorem bernoulliMass_strict_logconcave {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (k : ℤ)
    (hk₀ : 0 ≤ k) (hkn : k ≤ n) :
    bernoulliMass p (k - 1) * bernoulliMass p (k + 1) < bernoulliMass p k ^ 2 := by
  have h := bernoulli_toeplitzTwo_pos p hp hp₁ k hk₀ hkn
  simp only [toeplitzTwo, sub_zero, add_sub_cancel_right] at h
  nlinarith

end RenyiMonotonicity
