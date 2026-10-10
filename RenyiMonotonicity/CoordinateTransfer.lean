module
public import RenyiMonotonicity.MidpointFunctional

@[expose] public section

noncomputable section
open Set
open Filter
open scoped BigOperators Topology

namespace RenyiMonotonicity

/-- The Tsallis slope decreases along any positive affine mixture. -/
theorem tsallisSlope_antitoneOn {m : ℕ} (q : ℝ) (a b : Fin m → ℝ)
    (hq : 0 < q) (hq1 : q ≠ 1)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ k, 0 < affineMass a b t k) :
    AntitoneOn (tsallisSlope q a b) (Ioo (0 : ℝ) 1) := by
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :=
    hasDerivAt_tsallisSlope q a b t hq1 (hpos t ht)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  exact tsallis_second_derivative_nonpos q a b t hq.le (hpos t (interior_subset ht))

/-- A nonnegative fair-point slope controls the whole lower half of an affine
mixture, including its endpoint at zero. -/
theorem tsallis_affine_monotone_half {m : ℕ} (q : ℝ) (a b : Fin m → ℝ)
    (hq : 0 < q) (hq1 : q ≠ 1)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ k, 0 < affineMass a b t k)
    (hmid : 0 ≤ tsallisSlope q a b (1 / 2)) :
    MonotoneOn (fun t => tsallis q (affineMass a b t)) (Icc (0 : ℝ) (1 / 2)) := by
  have ha := tsallisSlope_antitoneOn q a b hq hq1 hpos
  have hs (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) (1 / 2))) :
      t ∈ Ioo (0 : ℝ) 1 := by
    rw [interior_Icc] at ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1 / 2))
    (fun t _ => (continuousAt_tsallis_affine q a b t hq).continuousWithinAt)
    (fun t ht => (hasDerivAt_tsallis_affine q a b t hq.ne' hq1
      (hpos t (hs t ht))).hasDerivWithinAt)
  intro t ht
  have hh : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have ht' := interior_subset ht
  exact hmid.trans (ha (hs t ht) hh ht'.2)

theorem affineMass_pos_of_edge {m : ℕ} (a b : Fin m → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (hs : ∀ k, 0 < a k + b k)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (k : Fin m) :
    0 < affineMass a b t k := by
  have hc : 0 < 1 - t := sub_pos.mpr ht.2
  dsimp [affineMass]
  rcases eq_or_lt_of_le (ha k) with hk | hk
  · have hb' : 0 < b k := by linarith [hs k]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hc.le (ha k)) (mul_pos ht.1 hb')
  · exact add_pos_of_pos_of_nonneg (mul_pos hc hk) (mul_nonneg ht.1.le (hb k))

/-- Transfer from the actual midpoint functional to one actual Bernoulli coin.
The sign of the midpoint functional is the remaining analytic input. -/
theorem tsallis_cons_monotone_of_midpoint {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) (hq1 : q ≠ 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1 / 2)
    (hmid : 0 ≤ midpointFunctional q p / (1 - q)) :
    MonotoneOn (fun t => tsallis q (bernoulliSum (Fin.cons t p)))
      (Icc (0 : ℝ) (1 / 2)) := by
  let a : Fin (n + 2) → ℝ := fun k => bernoulliMass p (k.val : ℤ)
  let b : Fin (n + 2) → ℝ := fun k => bernoulliMass p ((k.val : ℤ) - 1)
  have ha : ∀ k, 0 ≤ a k := fun k => bernoulliMass_nonneg p (fun i => (hp i).le)
    (fun i => by linarith [hp1 i]) _
  have hb : ∀ k, 0 ≤ b k := fun k => bernoulliMass_nonneg p (fun i => (hp i).le)
    (fun i => by linarith [hp1 i]) _
  have hs : ∀ k, 0 < a k + b k := by
    intro k
    simpa only [a, b, edgeSum, add_comm] using edgeSum_pos p hp (fun i => by linarith [hp1 i]) k
  have hpos := affineMass_pos_of_edge a b ha hb hs
  have hh : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hder : HasDerivAt (fun t => tsallis q (affineMass a b t))
      (q * (2 : ℝ) ^ (1 - q) * midpointFunctional q p / (1 - q)) (1 / 2) := by
    simpa only [bernoulliSum_cons_eq_affineMass] using
      hasDerivAt_tsallis_cons_half q p hq hq1 hp hp1
  have he := (hasDerivAt_tsallis_affine q a b (1 / 2) hq.ne' hq1 (hpos _ hh)).unique hder
  have hnonneg : 0 ≤ tsallisSlope q a b (1 / 2) := by
    rw [he, mul_div_assoc]
    exact mul_nonneg (mul_nonneg hq.le (Real.rpow_pos_of_pos (by norm_num) _).le) hmid
  simpa only [bernoulliSum_cons_eq_affineMass] using
    tsallis_affine_monotone_half q a b hq hq1 hpos hnonneg

/-- The same midpoint transfer for any named coordinate. -/
theorem tsallis_update_monotone_of_midpoint {n : ℕ} (q : ℝ)
    (p : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hq : 0 < q) (hq1 : q ≠ 1) (hp : ∀ j, 0 < p j) (hp1 : ∀ j, p j ≤ 1 / 2)
    (hmid : 0 ≤ midpointFunctional q (omitCoin p i) / (1 - q)) :
    MonotoneOn (fun t => tsallis q (bernoulliSum (Function.update p i t)))
      (Icc (0 : ℝ) (1 / 2)) := by
  have h := tsallis_cons_monotone_of_midpoint q (omitCoin p i) hq hq1
    (fun j => hp _) (fun j => hp1 _) hmid
  have he (t : ℝ) : bernoulliSum (Function.update p i t) =
      bernoulliSum (Fin.cons t (omitCoin p i)) := by
    funext k
    simp only [bernoulliSum, bernoulliPolynomial_update_eq_cons]
  simp_rw [he]
  exact h

/-- Finite coordinate replacement on the positive half cube, once the actual
midpoint sign has been established in every background dimension. -/
theorem tsallis_monotone_positive_of_midpoint (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1)
    (hmid : ∀ (n : ℕ) (p : Fin n → ℝ), (∀ i, 0 < p i) → (∀ i, p i ≤ 1 / 2) →
      0 ≤ midpointFunctional q p / (1 - q))
    {n : ℕ} (p r : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum r) := by
  classical
  cases n with
  | zero =>
      have he : p = r := Subsingleton.elim _ _
      rw [he]
  | succ n =>
      have haux (s : Finset (Fin (n + 1))) :
          tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum (s.piecewise r p)) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.piecewise_insert]
            have hwpos (j) : 0 < s.piecewise r p j := by
              by_cases hj : j ∈ s
              · simpa [Finset.piecewise, hj] using (hp j).trans_le (hpr j)
              · simpa [Finset.piecewise, hj] using hp j
            have hwle (j) : s.piecewise r p j ≤ 1 / 2 := by
              by_cases hj : j ∈ s
              · simpa [Finset.piecewise, hj] using hr j
              · simpa [Finset.piecewise, hj] using (hpr j).trans (hr j)
            have hm := tsallis_update_monotone_of_midpoint q (s.piecewise r p) i hq hq1
              hwpos hwle (hmid n (omitCoin (s.piecewise r p) i)
                (fun j => hwpos _) (fun j => hwle _))
            have hc := hm (show p i ∈ Icc (0 : ℝ) (1 / 2) from
                ⟨(hp i).le, (hpr i).trans (hr i)⟩)
              (show r i ∈ Icc (0 : ℝ) (1 / 2) from ⟨(hp i).le.trans (hpr i), hr i⟩) (hpr i)
            have hv : s.piecewise r p i = p i := Finset.piecewise_eq_of_notMem _ _ _ hi
            have hu : Function.update (s.piecewise r p) i (p i) = s.piecewise r p := by
              rw [← hv]
              exact Function.update_eq_self _ _
            dsimp only at hc
            rw [hu] at hc
            exact ih.trans hc
      simpa only [Finset.piecewise_univ] using haux Finset.univ

/-- Continuity extends a monotone function from the positive half cube to every
support-changing face. The explicit approximation preserves coordinate order. -/
theorem halfCube_monotone_of_positive {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hc : ∀ p, (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1 / 2) → ContinuousAt F p)
    (hm : ∀ p r, (∀ i, 0 < p i) → (∀ i, p i ≤ r i) → (∀ i, r i ≤ 1 / 2) → F p ≤ F r)
    (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hpr : ∀ i, p i ≤ r i)
    (hr : ∀ i, r i ≤ 1 / 2) : F p ≤ F r := by
  let v (p : Fin n → ℝ) (e : ℝ) : Fin n → ℝ := fun i => (1 - e) * p i + e / 4
  have hv (p : Fin n → ℝ) : ContinuousAt (v p) 0 := by dsimp [v]; fun_prop
  have hvt (p : Fin n → ℝ) : Tendsto (v p) (𝓝 0) (𝓝 p) := by
    simpa [v] using (hv p).tendsto
  have hfp : Tendsto (fun e => F (v p e)) (𝓝[>] (0 : ℝ)) (𝓝 (F p)) := by
    have hh := (hc p hp (fun i => (hpr i).trans (hr i))).tendsto.comp (hvt p)
    simpa only [Function.comp_def] using hh.mono_left nhdsWithin_le_nhds
  have hfr : Tendsto (fun e => F (v r e)) (𝓝[>] (0 : ℝ)) (𝓝 (F r)) := by
    have hh := (hc r (fun i => (hp i).trans (hpr i)) hr).tendsto.comp (hvt r)
    simpa only [Function.comp_def] using hh.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hfp hfr
  have he1 : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he1] with e he0 he1
  have he0' : 0 < e := he0
  apply hm
  · intro i
    dsimp [v]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (hp i)) (by positivity)
  · intro i
    dsimp [v]
    nlinarith [mul_nonneg (show 0 ≤ 1 - e by linarith) (sub_nonneg.mpr (hpr i))]
  · intro i
    dsimp [v]
    nlinarith [mul_nonneg (sub_nonneg.mpr he1.le) (sub_nonneg.mpr (hr i))]

/-- Complete closed-cube transfer for any positive order other than one. Its
sole mathematical input is the actual midpoint sign in all dimensions. -/
theorem tsallis_monotone_of_midpoint (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1)
    (hmid : ∀ (n : ℕ) (p : Fin n → ℝ), (∀ i, 0 < p i) → (∀ i, p i ≤ 1 / 2) →
      0 ≤ midpointFunctional q p / (1 - q))
    {n : ℕ} (p r : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    tsallis q (bernoulliSum p) ≤ tsallis q (bernoulliSum r) := by
  exact halfCube_monotone_of_positive (fun p => tsallis q (bernoulliSum p))
    (fun p _ _ => continuousAt_tsallis_bernoulli q p hq)
    (fun p r hp hpr hr => tsallis_monotone_positive_of_midpoint q hq hq1 hmid p r hp hpr hr)
    p r hp hpr hr

end RenyiMonotonicity
