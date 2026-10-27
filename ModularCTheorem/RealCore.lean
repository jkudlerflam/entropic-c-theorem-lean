import Mathlib

/-!
RealCore.lean. Uncompiled, as requested.

Step 6 uses midpoint concavity and continuity, followed by an elementary
maximum argument. This avoids discretization and floor/ceiling limits.

The one-sided derivative API was checked against
[Mathlib v4.35.0](https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.35.0/Mathlib/Analysis/Convex/Deriv.lean).
-/

open Real Set Filter
open scoped Topology

structure OneSidedData (D : ℝ → ℝ → ℝ → ℝ) (c : ℝ) : Prop where
  nonneg : ∀ a A b, 0 < a → a ≤ A → 0 < b → 0 ≤ D a A b
  add : ∀ a A A' b, 0 < a → a ≤ A → A ≤ A' → 0 < b →
    D a A b + D A A' b = D a A' b
  boost : ∀ μ a A b, 0 < μ → 0 < a → a ≤ A → 0 < b →
    D (μ * a) (μ * A) (b / μ) = D a A b
  anti_b : ∀ a A b B, 0 < a → a ≤ A → 0 < b → b ≤ B →
    D a A B ≤ D a A b
  uv : ∀ a A b, 0 < a → a ≤ A → 0 < b →
    D a A b ≤ c / 6 * Real.log (A / a)

namespace OneSidedData

variable {D : ℝ → ℝ → ℝ → ℝ} {c : ℝ}

theorem boost_one (h : OneSidedData D c) (a A b : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) :
    D a A b = D (a * b) (A * b) 1 := by
  simpa only [div_self hb.ne', mul_comm b a, mul_comm b A] using
    (h.boost b a A b hb ha haA hb).symm

noncomputable def potential (D : ℝ → ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then D 1 (Real.exp x) 1 else -D (Real.exp x) 1 1

/-- Additivity across the three possible positions relative to zero. -/
theorem potential_exp_difference (h : OneSidedData D c)
    {x y : ℝ} (hxy : x ≤ y) :
    D (Real.exp x) (Real.exp y) 1 = potential D y - potential D x := by
  have hexy : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := hx.trans hxy
    have hex : 1 ≤ Real.exp x := by
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hx)
    have hadd :=
      h.add 1 (Real.exp x) (Real.exp y) 1
        zero_lt_one hex hexy zero_lt_one
    simp only [potential, if_pos hx, if_pos hy]
    linarith
  · have hex : Real.exp x ≤ 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (lt_of_not_ge hx).le)
    by_cases hy : 0 ≤ y
    · have hey : 1 ≤ Real.exp y := by
        simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hy)
      have hadd :=
        h.add (Real.exp x) 1 (Real.exp y) 1
          (Real.exp_pos x) hex hey zero_lt_one
      simp only [potential, if_neg hx, if_pos hy]
      linarith
    · have hey : Real.exp y ≤ 1 := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (lt_of_not_ge hy).le)
      have hadd :=
        h.add (Real.exp x) (Real.exp y) 1 1
          (Real.exp_pos x) hexy hey zero_lt_one
      simp only [potential, if_neg hx, if_neg hy]
      linarith

theorem representation (h : OneSidedData D c) (a A b : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) :
    D a A b =
      potential D (Real.log (A * b)) - potential D (Real.log (a * b)) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hAb : 0 < A * b := mul_pos (ha.trans_le haA) hb
  have hlog : Real.log (a * b) ≤ Real.log (A * b) :=
    Real.log_le_log hab (mul_le_mul_of_nonneg_right haA hb.le)
  calc
    D a A b = D (a * b) (A * b) 1 := h.boost_one a A b ha haA hb
    _ = potential D (Real.log (A * b)) -
        potential D (Real.log (a * b)) := by
      simpa only [Real.exp_log hab, Real.exp_log hAb] using
        h.potential_exp_difference hlog

theorem potential_increment_bounds (h : OneSidedData D c)
    (x y : ℝ) (hxy : x ≤ y) :
    0 ≤ potential D y - potential D x ∧
      potential D y - potential D x ≤ c / 6 * (y - x) := by
  have hexy : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  have h0 :=
    h.nonneg (Real.exp x) (Real.exp y) 1
      (Real.exp_pos x) hexy zero_lt_one
  have hu :=
    h.uv (Real.exp x) (Real.exp y) 1
      (Real.exp_pos x) hexy zero_lt_one
  rw [h.potential_exp_difference hxy] at h0 hu
  rw [Real.log_div (Real.exp_ne_zero y) (Real.exp_ne_zero x),
    Real.log_exp, Real.log_exp] at hu
  exact ⟨h0, hu⟩

theorem potential_monotone (h : OneSidedData D c) :
    Monotone (potential D) := by
  intro x y hxy
  exact sub_nonneg.mp (h.potential_increment_bounds x y hxy).1

/-- The UV estimate gives a global Lipschitz estimate, hence continuity. -/
theorem potential_continuous (h : OneSidedData D c) :
    Continuous (potential D) := by
  have hdist : ∀ x y : ℝ,
      dist (potential D x) (potential D y) ≤ c / 6 * dist x y := by
    intro x y
    rcases le_total x y with hxy | hyx
    · rw [Real.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (h.potential_monotone hxy)),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      simpa only [neg_sub] using
        (h.potential_increment_bounds x y hxy).2
    · rw [Real.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (h.potential_monotone hyx)),
        abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact (h.potential_increment_bounds y x hyx).2
  exact (LipschitzWith.of_dist_le' hdist).continuous

theorem potential_increment_eq (h : OneSidedData D c)
    (s t : ℝ) (ht : 0 ≤ t) :
    potential D (s + t) - potential D s =
      D 1 (Real.exp t) (Real.exp s) := by
  have het : 1 ≤ Real.exp t := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr ht)
  have hr :=
    h.representation 1 (Real.exp t) (Real.exp s)
      zero_lt_one het (Real.exp_pos s)
  have hlog : Real.log (Real.exp t * Real.exp s) = t + s := by
    rw [← Real.exp_add, Real.log_exp]
  simpa only [one_mul, hlog, Real.log_exp, add_comm t s] using hr.symm

theorem potential_increment_antitone (h : OneSidedData D c)
    (s s' t : ℝ) (hss : s ≤ s') (ht : 0 ≤ t) :
    potential D (s' + t) - potential D s' ≤
      potential D (s + t) - potential D s := by
  have het : 1 ≤ Real.exp t := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr ht)
  rw [h.potential_increment_eq s' t ht, h.potential_increment_eq s t ht]
  exact h.anti_b 1 (Real.exp t) (Real.exp s) (Real.exp s')
    zero_lt_one het (Real.exp_pos s) (Real.exp_le_exp.mpr hss)

theorem potential_midpoint (h : OneSidedData D c) (x y : ℝ) :
    potential D x + potential D y ≤
      2 * potential D ((x + y) / 2) := by
  have ordered : ∀ u v : ℝ, u ≤ v →
      potential D u + potential D v ≤
        2 * potential D ((u + v) / 2) := by
    intro u v huv
    have hi :=
      h.potential_increment_antitone u ((u + v) / 2) ((v - u) / 2)
        (by linarith) (by linarith)
    have hleft : u + (v - u) / 2 = (u + v) / 2 := by ring
    have hright : (u + v) / 2 + (v - u) / 2 = v := by ring
    rw [hleft, hright] at hi
    linarith
  rcases le_total x y with hxy | hyx
  · exact ordered x y hxy
  · simpa only [add_comm y x, add_comm (potential D y) (potential D x)] using
      ordered y x hyx

/--
A continuous midpoint-concave function is concave.

For each chord, its deficit `g` has zero endpoint values and is midpoint-convex.
At a maximum on `[0,1]`, midpoint convexity gives `2 g(t) ≤ g(t)`, by reflecting
toward one endpoint. Thus the entire deficit is nonpositive.
-/
private theorem concaveOn_univ_of_continuous_midpoint
    {f : ℝ → ℝ} (hf : Continuous f)
    (hmid : ∀ x y : ℝ, f x + f y ≤ 2 * f ((x + y) / 2)) :
    ConcaveOn ℝ univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change a * f x + b * f y ≤ f (a * x + b * y)
  let g : ℝ → ℝ :=
    fun t => (1 - t) * f x + t * f y - f ((1 - t) * x + t * y)
  have hg : Continuous g := by
    dsimp only [g]
    exact
      (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)).sub
        (hf.comp
          (((continuous_const.sub continuous_id).mul continuous_const).add
            (continuous_id.mul continuous_const)))
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = 0 := by simp [g]
  have hgmid : ∀ u v : ℝ, 2 * g ((u + v) / 2) ≤ g u + g v := by
    intro u v
    have hm := hmid ((1 - u) * x + u * y) ((1 - v) * x + v * y)
    have he :
        (((1 - u) * x + u * y) + ((1 - v) * x + v * y)) / 2 =
          (1 - (u + v) / 2) * x + ((u + v) / 2) * y := by
      ring
    rw [he] at hm
    dsimp only [g]
    nlinarith only [hm]
  obtain ⟨t, ht, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn
      (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
      hg.continuousOn
  have hgt : g t ≤ 0 := by
    by_cases ht2 : t ≤ 1 / 2
    · have hm : 2 * t ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ht.1, ht.2]
      have hbound : g (2 * t) ≤ g t := hmax hm
      have hi := hgmid 0 (2 * t)
      rw [show (0 + 2 * t) / 2 = t by ring, hg0] at hi
      linarith
    · have hm : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := by
        constructor <;> linarith [ht.1, ht.2]
      have hbound : g (2 * t - 1) ≤ g t := hmax hm
      have hi := hgmid (2 * t - 1) 1
      rw [show (2 * t - 1 + 1) / 2 = t by ring, hg1] at hi
      linarith
  have hgb : g b ≤ 0 :=
    (hmax (show b ∈ Icc (0 : ℝ) 1 from ⟨hb, by linarith⟩)).trans hgt
  have ha' : a = 1 - b := by linarith
  rw [ha']
  dsimp only [g] at hgb
  linarith

theorem potential_concave (h : OneSidedData D c) :
    ConcaveOn ℝ univ (potential D) :=
  concaveOn_univ_of_continuous_midpoint
    h.potential_continuous h.potential_midpoint

/-- Defined using the convex function `-potential D`. -/
noncomputable def rightSlope (D : ℝ → ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  -derivWithin (fun y => -potential D y) (Ioi x) x

/--
Mathlib obtains this finite one-sided derivative by monotone convergence of
secant slopes. An interior point supplies the opposite-side slope bound.
-/
theorem potential_hasDerivWithinAt_rightSlope (h : OneSidedData D c) (x : ℝ) :
    HasDerivWithinAt (potential D) (rightSlope D x) (Ioi x) x := by
  have hc : ConvexOn ℝ univ (fun y => -potential D y) :=
    h.potential_concave.neg
  have hd :=
    (hc.hasDerivWithinAt_rightDeriv_of_mem_interior
      (x := x) (by simp)).neg
  simpa only [rightSlope, Pi.neg_def, neg_neg] using hd

theorem rightSlope_antitone (h : OneSidedData D c) :
    Antitone (rightSlope D) := by
  intro x y hxy
  have hc : ConvexOn ℝ univ (fun z => -potential D z) :=
    h.potential_concave.neg
  have hm :
      derivWithin (fun z => -potential D z) (Ioi x) x ≤
        derivWithin (fun z => -potential D z) (Ioi y) y :=
    hc.monotoneOn_rightDeriv (by simp) (by simp) hxy
  simpa only [rightSlope] using neg_le_neg hm

theorem potential_slope_bounds (h : OneSidedData D c)
    (x y : ℝ) (hxy : x < y) :
    0 ≤ slope (potential D) x y ∧
      slope (potential D) x y ≤ c / 6 := by
  have hb := h.potential_increment_bounds x y hxy.le
  have hden : 0 < y - x := sub_pos.mpr hxy
  rw [slope_def_field]
  exact ⟨div_nonneg hb.1 hden.le, (div_le_iff₀ hden).mpr hb.2⟩

theorem rightSlope_bounds (h : OneSidedData D c) (x : ℝ) :
    0 ≤ rightSlope D x ∧ rightSlope D x ≤ c / 6 := by
  have hlim :
      Tendsto (slope (potential D) x) (𝓝[>] x) (𝓝 (rightSlope D x)) :=
    (hasDerivWithinAt_iff_tendsto_slope'
      (show x ∉ Ioi x by simp)).mp
      (h.potential_hasDerivWithinAt_rightSlope x)
  have hev : ∀ᶠ y in 𝓝[>] x,
      0 ≤ slope (potential D) x y ∧
        slope (potential D) x y ≤ c / 6 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h.potential_slope_bounds x y hy
  exact ⟨ge_of_tendsto hlim (hev.mono fun _ hy => hy.1),
    le_of_tendsto hlim (hev.mono fun _ hy => hy.2)⟩

/-- The logarithm maps the entire source half-line into the target half-line. -/
theorem hasDerivWithinAt_D (h : OneSidedData D c) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    HasDerivWithinAt (fun A => D a A b)
      (rightSlope D (Real.log (a * b)) / a) (Ici a) a := by
  have hg :
      HasDerivAt (fun A : ℝ => Real.log (A * b))
        ((1 * b) / (a * b)) a :=
    ((hasDerivAt_id a).mul_const b).log (mul_ne_zero ha.ne' hb.ne')
  have hcancel : (1 * b) / (a * b) = 1 / a := by
    field_simp [ha.ne', hb.ne'] <;> ring
  rw [hcancel] at hg
  have hmap :
      MapsTo (fun A : ℝ => Real.log (A * b))
        (Ici a) (Ici (Real.log (a * b))) := by
    intro A hA
    change Real.log (a * b) ≤ Real.log (A * b)
    exact Real.log_le_log (mul_pos ha hb)
      (mul_le_mul_of_nonneg_right hA hb.le)
  have hout :
      HasDerivWithinAt (potential D) (rightSlope D (Real.log (a * b)))
        (Ici (Real.log (a * b))) (Real.log (a * b)) :=
    (h.potential_hasDerivWithinAt_rightSlope (Real.log (a * b))).Ici_of_Ioi
  have hcomp := hout.comp a hg.hasDerivWithinAt hmap
  have hd :
      HasDerivWithinAt (fun A => D a A b)
        (rightSlope D (Real.log (a * b)) * (1 / a)) (Ici a) a :=
    (hcomp.sub_const (potential D (Real.log (a * b)))).congr_of_mem
      (fun A hA => h.representation a A b ha hA hb)
      (show a ∈ Ici a from Set.mem_Ici.mpr le_rfl)
  simpa only [div_eq_mul_inv, one_mul] using hd

theorem cTheorem (h : OneSidedData D c) :
    ∃ C : ℝ → ℝ,
      (∀ r, 0 < r → 0 ≤ C r) ∧
      (∀ r, 0 < r → C r ≤ c) ∧
      AntitoneOn C (Ioi 0) ∧
      ∀ a b, 0 < a → 0 < b →
        HasDerivWithinAt (fun A => D a A b)
          (C (Real.sqrt (a * b)) / (6 * a)) (Ici a) a := by
  let C : ℝ → ℝ := fun r => 6 * rightSlope D (2 * Real.log r)
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact mul_nonneg (by norm_num) (h.rightSlope_bounds (2 * Real.log r)).1
  · intro r hr
    have hu := (h.rightSlope_bounds (2 * Real.log r)).2
    dsimp only [C]
    linarith
  · intro r hr s hs hrs
    have hlog : 2 * Real.log r ≤ 2 * Real.log s :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hr hrs) (by norm_num)
    exact mul_le_mul_of_nonneg_left
      (h.rightSlope_antitone hlog) (by norm_num)
  · intro a b ha hb
    have hlog :
        2 * Real.log (Real.sqrt (a * b)) = Real.log (a * b) := by
      rw [Real.log_sqrt (mul_pos ha hb).le]
      ring
    have hcoeff :
        C (Real.sqrt (a * b)) / (6 * a) =
          rightSlope D (Real.log (a * b)) / a := by
      dsimp only [C]
      rw [hlog]
      field_simp [ha.ne'] <;> ring
    rw [hcoeff]
    exact h.hasDerivWithinAt_D a b ha hb

end OneSidedData

noncomputable def cR (D : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  6 * a * derivWithin (fun A => D a A b) (Ici a) a

/-- The same witness also represents the normalized right derivative `cR`. -/
theorem OneSidedData.cTheorem_with_cR
    {D : ℝ → ℝ → ℝ → ℝ} {c : ℝ} (h : OneSidedData D c) :
    ∃ C : ℝ → ℝ,
      (∀ r, 0 < r → 0 ≤ C r) ∧
      (∀ r, 0 < r → C r ≤ c) ∧
      AntitoneOn C (Ioi 0) ∧
      (∀ a b, 0 < a → 0 < b →
        HasDerivWithinAt (fun A => D a A b)
          (C (Real.sqrt (a * b)) / (6 * a)) (Ici a) a) ∧
      (∀ a b, 0 < a → 0 < b →
        cR D a b = C (Real.sqrt (a * b))) := by
  obtain ⟨C, hC0, hCc, hCanti, hCderiv⟩ := h.cTheorem
  refine ⟨C, hC0, hCc, hCanti, hCderiv, ?_⟩
  intro a b ha hb
  rw [cR, (hCderiv a b ha hb).derivWithin (uniqueDiffWithinAt_Ici a)]
  field_simp [ha.ne'] <;> ring

