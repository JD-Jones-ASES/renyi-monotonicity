module
public import Mathlib

/-! A finite-domain density ratio for the scalar-threshold comparison. -/

@[expose] public section
noncomputable section
namespace RenyiMonotonicity

def scalarRatio (q c x : ℝ) : ℝ :=
  (1+x)^q * (1+c*x)^(q-3) * (1+(c-1)*x)^(-q)

def scalarRatioNumerator (q c x : ℝ) : ℝ :=
  (2*q-3*c)*(1+c*x) + (3-q)*c*(1-c)*x^2

theorem scalarRatio_pos (q c x : ℝ)
    (h1 : 0 < 1+x) (h2 : 0 < 1+c*x) (h3 : 0 < 1+(c-1)*x) :
    0 < scalarRatio q c x := by
  unfold scalarRatio
  positivity

@[simp] theorem scalarRatio_zero (q c : ℝ) : scalarRatio q c 0 = 1 := by
  simp [scalarRatio]

theorem hasDerivAt_scalarRatio (q c x : ℝ)
    (h1 : 0 < 1+x) (h2 : 0 < 1+c*x) (h3 : 0 < 1+(c-1)*x) :
    HasDerivAt (scalarRatio q c)
      (scalarRatio q c x * scalarRatioNumerator q c x /
        ((1+x)*(1+c*x)*(1+(c-1)*x))) x := by
  have d1 := ((hasDerivAt_id x).const_add 1).rpow_const (p := q) (Or.inl h1.ne')
  have d2 := (((hasDerivAt_id x).const_mul c).const_add 1).rpow_const
    (p := q-3) (Or.inl h2.ne')
  have d3 := (((hasDerivAt_id x).const_mul (c-1)).const_add 1).rpow_const
    (p := -q) (Or.inl h3.ne')
  convert (d1.mul d2).mul d3 using 1
  · rfl
  · simp only [id_eq, mul_one, one_mul, Pi.mul_apply]
    rw [Real.rpow_sub_one h1.ne', Real.rpow_sub_one h2.ne', Real.rpow_sub_one h3.ne']
    unfold scalarRatio scalarRatioNumerator
    generalize (1+x)^q = A, (1+c*x)^(q-3) = B, (1+(c-1)*x)^(-q) = C
    have h3n : 1+c*x-x ≠ 0 := by nlinarith
    field_simp [h1.ne', h2.ne', h3.ne', h3n]
    ring_nf
    field_simp [h3n]
    ring

end RenyiMonotonicity
