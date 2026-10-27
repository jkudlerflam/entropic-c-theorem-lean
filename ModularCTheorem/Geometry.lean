import Mathlib

namespace CTheorem

noncomputable section

/- Compiles cleanly on Lean v4.35.0 / Mathlib v4.35.0. -/

/-- Points of 1+1 Minkowski space in light-cone coordinates `(u, v) = (t - x, t + x)`. -/
abbrev Pt := ℝ × ℝ

/-- Open causal diamond `{u0 < u < u1, v0 < v < v1}`. -/
structure Diamond where
  u0 : ℝ
  u1 : ℝ
  v0 : ℝ
  v1 : ℝ
  hu : u0 < u1
  hv : v0 < v1

def Diamond.toSet (Y : Diamond) : Set Pt :=
  {p | Y.u0 < p.1 ∧ p.1 < Y.u1 ∧ Y.v0 < p.2 ∧ p.2 < Y.v1}

/-- `Y ⋐ Z`: the closure of `Y` lies in `Z` (strict inequalities on all four sides). -/
def Diamond.CompactIn (Y Z : Diamond) : Prop :=
  Z.u0 < Y.u0 ∧ Y.u1 < Z.u1 ∧ Z.v0 < Y.v0 ∧ Y.v1 < Z.v1

/-- Left and right Rindler wedges `L_a = {u > a, v < 0}`, `R_b = {u < 0, v > b}`. -/
def leftWedge (a : ℝ) : Set Pt := {p | a < p.1 ∧ p.2 < 0}

def rightWedge (b : ℝ) : Set Pt := {p | p.1 < 0 ∧ b < p.2}

/-- Spacelike separation of points and of sets. -/
def Spacelike (p q : Pt) : Prop :=
  (p.1 - q.1) * (p.2 - q.2) < 0

def SpacelikeSets (S T : Set Pt) : Prop :=
  ∀ p ∈ S, ∀ q ∈ T, Spacelike p q

/-- Boost about the origin with rapidity `log μ`: `(u, v) ↦ (μ u, v / μ)`, `μ > 0`. -/
def boost (μ : ℝ) (p : Pt) : Pt := (μ * p.1, p.2 / μ)

/-- Boost of a diamond (requires `0 < μ` for the corner order; take it as an argument). -/
def Diamond.boost (μ : ℝ) (hμ : 0 < μ) (Y : Diamond) : Diamond where
  u0 := μ * Y.u0
  u1 := μ * Y.u1
  v0 := Y.v0 / μ
  v1 := Y.v1 / μ
  hu := mul_lt_mul_of_pos_left Y.hu hμ
  hv := by
    simp only [div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right Y.hv (inv_pos.mpr hμ)

@[ext]
theorem Diamond.ext {Y Z : Diamond}
    (hu0 : Y.u0 = Z.u0) (hu1 : Y.u1 = Z.u1)
    (hv0 : Y.v0 = Z.v0) (hv1 : Y.v1 = Z.v1) :
    Y = Z := by
  rcases Y with ⟨yu0, yu1, yv0, yv1, yhu, yhv⟩
  rcases Z with ⟨zu0, zu1, zv0, zv1, zhu, zhv⟩
  change yu0 = zu0 at hu0
  change yu1 = zu1 at hu1
  change yv0 = zv0 at hv0
  change yv1 = zv1 at hv1
  subst zu0
  subst zu1
  subst zv0
  subst zv1
  rfl

/- Elementary endpoint tests for nonempty open intervals. -/

private theorem lower_bound_of_interval
    (l r c : ℝ) (hlr : l < r)
    (h : ∀ x : ℝ, l < x → x < r → c < x) :
    c ≤ l := by
  by_contra hc
  have hlc : l < c := lt_of_not_ge hc
  have hlm : l < min c r := lt_min hlc hlr
  have hmc : min c r ≤ c := min_le_left c r
  have hmr : min c r ≤ r := min_le_right c r
  have hx0 : l < (l + min c r) / 2 := by linarith
  have hx1 : (l + min c r) / 2 < r := by linarith
  have hx := h ((l + min c r) / 2) hx0 hx1
  linarith

private theorem upper_bound_of_interval
    (l r c : ℝ) (hlr : l < r)
    (h : ∀ x : ℝ, l < x → x < r → x < c) :
    r ≤ c := by
  by_contra hc
  have hcr : c < r := lt_of_not_ge hc
  have hmr : max l c < r := max_lt hlr hcr
  have hlm : l ≤ max l c := le_max_left l c
  have hcm : c ≤ max l c := le_max_right l c
  have hx0 : l < (max l c + r) / 2 := by linarith
  have hx1 : (max l c + r) / 2 < r := by linarith
  have hx := h ((max l c + r) / 2) hx0 hx1
  linarith

private theorem mem_with_v_midpoint (Y : Diamond) {u : ℝ}
    (hu0 : Y.u0 < u) (hu1 : u < Y.u1) :
    (u, (Y.v0 + Y.v1) / 2) ∈ Y.toSet := by
  exact ⟨hu0, hu1, by linarith [Y.hv], by linarith [Y.hv]⟩

private theorem mem_with_u_midpoint (Y : Diamond) {v : ℝ}
    (hv0 : Y.v0 < v) (hv1 : v < Y.v1) :
    ((Y.u0 + Y.u1) / 2, v) ∈ Y.toSet := by
  exact ⟨by linarith [Y.hu], by linarith [Y.hu], hv0, hv1⟩

/- 1. Inclusion of diamonds. -/

theorem Diamond.toSet_subset_iff (Y Z : Diamond) :
    Y.toSet ⊆ Z.toSet ↔
      Z.u0 ≤ Y.u0 ∧ Y.u1 ≤ Z.u1 ∧ Z.v0 ≤ Y.v0 ∧ Y.v1 ≤ Z.v1 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply lower_bound_of_interval Y.u0 Y.u1 Z.u0 Y.hu
      intro u hu0 hu1
      exact (h (mem_with_v_midpoint Y hu0 hu1)).1
    · apply upper_bound_of_interval Y.u0 Y.u1 Z.u1 Y.hu
      intro u hu0 hu1
      exact (h (mem_with_v_midpoint Y hu0 hu1)).2.1
    · apply lower_bound_of_interval Y.v0 Y.v1 Z.v0 Y.hv
      intro v hv0 hv1
      exact (h (mem_with_u_midpoint Y hv0 hv1)).2.2.1
    · apply upper_bound_of_interval Y.v0 Y.v1 Z.v1 Y.hv
      intro v hv0 hv1
      exact (h (mem_with_u_midpoint Y hv0 hv1)).2.2.2
  · rintro ⟨hu0, hu1, hv0, hv1⟩ p ⟨hp0, hp1, hp2, hp3⟩
    exact ⟨lt_of_le_of_lt hu0 hp0, lt_of_lt_of_le hp1 hu1,
      lt_of_le_of_lt hv0 hp2, lt_of_lt_of_le hp3 hv1⟩

/- 2. Inclusion in wedges. No sign assumptions on the wedge parameters are needed. -/

theorem Diamond.subset_rightWedge_iff (Y : Diamond) (b : ℝ) :
    Y.toSet ⊆ rightWedge b ↔ Y.u1 ≤ 0 ∧ b ≤ Y.v0 := by
  constructor
  · intro h
    constructor
    · apply upper_bound_of_interval Y.u0 Y.u1 0 Y.hu
      intro u hu0 hu1
      exact (h (mem_with_v_midpoint Y hu0 hu1)).1
    · apply lower_bound_of_interval Y.v0 Y.v1 b Y.hv
      intro v hv0 hv1
      exact (h (mem_with_u_midpoint Y hv0 hv1)).2
  · rintro ⟨hu, hv⟩ p ⟨hp0, hp1, hp2, hp3⟩
    exact ⟨lt_of_lt_of_le hp1 hu, lt_of_le_of_lt hv hp2⟩

theorem Diamond.subset_leftWedge_iff (Y : Diamond) (a : ℝ) :
    Y.toSet ⊆ leftWedge a ↔ a ≤ Y.u0 ∧ Y.v1 ≤ 0 := by
  constructor
  · intro h
    constructor
    · apply lower_bound_of_interval Y.u0 Y.u1 a Y.hu
      intro u hu0 hu1
      exact (h (mem_with_v_midpoint Y hu0 hu1)).1
    · apply upper_bound_of_interval Y.v0 Y.v1 0 Y.hv
      intro v hv0 hv1
      exact (h (mem_with_u_midpoint Y hv0 hv1)).2
  · rintro ⟨hu, hv⟩ p ⟨hp0, hp1, hp2, hp3⟩
    exact ⟨lt_of_le_of_lt hu hp0, lt_of_lt_of_le hp3 hv⟩

/- 3. Monotonicity of wedges. -/

theorem leftWedge_anti {a A : ℝ} :
    a ≤ A → leftWedge A ⊆ leftWedge a := by
  intro ha p hp
  exact ⟨lt_of_le_of_lt ha hp.1, hp.2⟩

theorem rightWedge_anti {b B : ℝ} :
    b ≤ B → rightWedge B ⊆ rightWedge b := by
  intro hb p hp
  exact ⟨hp.1, lt_of_le_of_lt hb hp.2⟩

/- 4. Spacelike separation of opposite wedges. -/

theorem spacelike_leftWedge_rightWedge {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    SpacelikeSets (leftWedge a) (rightWedge b) := by
  intro p hp q hq
  rcases hp with ⟨hpu, hpv⟩
  rcases hq with ⟨hqu, hqv⟩
  change (p.1 - q.1) * (p.2 - q.2) < 0
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/- 5. Boost identities and covariance. -/

private theorem div_lt_div_pos {x y μ : ℝ} (hμ : 0 < μ) :
    x / μ < y / μ ↔ x < y := by
  simp only [div_eq_mul_inv]
  exact mul_lt_mul_iff_of_pos_right (inv_pos.mpr hμ)

theorem boost_apply_inv {μ : ℝ} (hμ : 0 < μ) (p : Pt) :
    boost μ (boost μ⁻¹ p) = p := by
  apply Prod.ext <;>
    dsimp [boost] <;>
    field_simp [ne_of_gt hμ]

theorem boost_mem_leftWedge_iff {a μ : ℝ} (hμ : 0 < μ) (p : Pt) :
    boost μ p ∈ leftWedge (μ * a) ↔ p ∈ leftWedge a := by
  change (μ * a < μ * p.1 ∧ p.2 / μ < 0) ↔
    (a < p.1 ∧ p.2 < 0)
  have hv : p.2 / μ < 0 ↔ p.2 < 0 := by
    simpa only [zero_div] using
      (div_lt_div_pos (x := p.2) (y := 0) hμ)
  rw [mul_lt_mul_iff_of_pos_left hμ, hv]

theorem boost_mem_rightWedge_iff {b μ : ℝ} (hμ : 0 < μ) (p : Pt) :
    boost μ p ∈ rightWedge (b / μ) ↔ p ∈ rightWedge b := by
  change (μ * p.1 < 0 ∧ b / μ < p.2 / μ) ↔
    (p.1 < 0 ∧ b < p.2)
  have hu : μ * p.1 < 0 ↔ p.1 < 0 := by
    simpa only [mul_zero] using
      (mul_lt_mul_iff_of_pos_left hμ : μ * p.1 < μ * 0 ↔ p.1 < 0)
  rw [hu, div_lt_div_pos hμ]

theorem Diamond.boost_mem_toSet_iff
    (Y : Diamond) {μ : ℝ} (hμ : 0 < μ) (p : Pt) :
    _root_.CTheorem.boost μ p ∈ (Y.boost μ hμ).toSet ↔ p ∈ Y.toSet := by
  change
    (μ * Y.u0 < μ * p.1 ∧ μ * p.1 < μ * Y.u1 ∧
      Y.v0 / μ < p.2 / μ ∧ p.2 / μ < Y.v1 / μ) ↔
    (Y.u0 < p.1 ∧ p.1 < Y.u1 ∧ Y.v0 < p.2 ∧ p.2 < Y.v1)
  simp only [mul_lt_mul_iff_of_pos_left hμ, div_lt_div_pos hμ]

theorem Diamond.boost_toSet (Y : Diamond) {μ : ℝ} (hμ : 0 < μ) :
    (Y.boost μ hμ).toSet = _root_.CTheorem.boost μ '' Y.toSet := by
  ext p
  constructor
  · intro hp
    refine ⟨_root_.CTheorem.boost μ⁻¹ p, ?_, boost_apply_inv hμ p⟩
    apply (Diamond.boost_mem_toSet_iff Y hμ (_root_.CTheorem.boost μ⁻¹ p)).mp
    rw [boost_apply_inv hμ p]
    exact hp
  · rintro ⟨q, hq, rfl⟩
    exact (Diamond.boost_mem_toSet_iff Y hμ q).mpr hq

theorem Diamond.boost_subset_rightWedge_iff
    (Y : Diamond) {b μ : ℝ} (hμ : 0 < μ) :
    (Y.boost μ hμ).toSet ⊆ rightWedge (b / μ) ↔
      Y.toSet ⊆ rightWedge b := by
  constructor
  · intro h p hp
    apply (boost_mem_rightWedge_iff (b := b) hμ p).mp
    apply h
    rw [Diamond.boost_toSet Y hμ]
    exact ⟨p, hp, rfl⟩
  · intro h p hp
    rw [Diamond.boost_toSet Y hμ] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact (boost_mem_rightWedge_iff hμ q).mpr (h hq)

theorem Diamond.boost_subset_leftWedge_iff
    (Y : Diamond) {a μ : ℝ} (hμ : 0 < μ) :
    (Y.boost μ hμ).toSet ⊆ leftWedge (μ * a) ↔
      Y.toSet ⊆ leftWedge a := by
  constructor
  · intro h p hp
    apply (boost_mem_leftWedge_iff (a := a) hμ p).mp
    apply h
    rw [Diamond.boost_toSet Y hμ]
    exact ⟨p, hp, rfl⟩
  · intro h p hp
    rw [Diamond.boost_toSet Y hμ] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact (boost_mem_leftWedge_iff hμ q).mpr (h hq)

theorem Diamond.boost_inv_then_boost
    (Y : Diamond) {μ : ℝ} (hμ : 0 < μ) :
    (Y.boost μ⁻¹ (inv_pos.mpr hμ)).boost μ hμ = Y := by
  apply Diamond.ext <;>
    dsimp [Diamond.boost] <;>
    field_simp [ne_of_gt hμ]

theorem Diamond.exists_boost_of_subset_rightWedge
    (Y' : Diamond) {b μ : ℝ} (hμ : 0 < μ)
    (hY' : Y'.toSet ⊆ rightWedge (b / μ)) :
    ∃ Y : Diamond, Y.toSet ⊆ rightWedge b ∧ Y' = Y.boost μ hμ := by
  let Y : Diamond := Y'.boost μ⁻¹ (inv_pos.mpr hμ)
  have heq : Y.boost μ hμ = Y' :=
    Diamond.boost_inv_then_boost Y' hμ
  refine ⟨Y, ?_, heq.symm⟩
  apply (Diamond.boost_subset_rightWedge_iff (b := b) Y hμ).mp
  rw [heq]
  exact hY'

theorem Diamond.exists_boost_of_subset_leftWedge
    (Y' : Diamond) {a μ : ℝ} (hμ : 0 < μ)
    (hY' : Y'.toSet ⊆ leftWedge (μ * a)) :
    ∃ Y : Diamond, Y.toSet ⊆ leftWedge a ∧ Y' = Y.boost μ hμ := by
  let Y : Diamond := Y'.boost μ⁻¹ (inv_pos.mpr hμ)
  have heq : Y.boost μ hμ = Y' :=
    Diamond.boost_inv_then_boost Y' hμ
  refine ⟨Y, ?_, heq.symm⟩
  apply (Diamond.boost_subset_leftWedge_iff (a := a) Y hμ).mp
  rw [heq]
  exact hY'

/- 6. Directedness, using the coordinate bounding box. -/

/-- The smallest coordinate bounding box containing two diamonds. -/
def Diamond.hull (Y Z : Diamond) : Diamond where
  u0 := min Y.u0 Z.u0
  u1 := max Y.u1 Z.u1
  v0 := min Y.v0 Z.v0
  v1 := max Y.v1 Z.v1
  hu := lt_of_le_of_lt (min_le_left _ _)
    (lt_of_lt_of_le Y.hu (le_max_left _ _))
  hv := lt_of_le_of_lt (min_le_left _ _)
    (lt_of_lt_of_le Y.hv (le_max_left _ _))

theorem Diamond.subset_hull_left (Y Z : Diamond) :
    Y.toSet ⊆ (Y.hull Z).toSet := by
  apply (Diamond.toSet_subset_iff Y (Y.hull Z)).mpr
  exact ⟨min_le_left _ _, le_max_left _ _,
    min_le_left _ _, le_max_left _ _⟩

theorem Diamond.subset_hull_right (Y Z : Diamond) :
    Z.toSet ⊆ (Y.hull Z).toSet := by
  apply (Diamond.toSet_subset_iff Z (Y.hull Z)).mpr
  exact ⟨min_le_right _ _, le_max_right _ _,
    min_le_right _ _, le_max_right _ _⟩

theorem Diamond.rightWedge_directed (b : ℝ) :
    ∀ Y Z : Diamond,
      Y.toSet ⊆ rightWedge b →
      Z.toSet ⊆ rightWedge b →
      ∃ W : Diamond,
        W.toSet ⊆ rightWedge b ∧
        Y.toSet ⊆ W.toSet ∧ Z.toSet ⊆ W.toSet := by
  intro Y Z hY hZ
  have hy := (Diamond.subset_rightWedge_iff Y b).mp hY
  have hz := (Diamond.subset_rightWedge_iff Z b).mp hZ
  refine ⟨Y.hull Z, ?_,
    Diamond.subset_hull_left Y Z, Diamond.subset_hull_right Y Z⟩
  apply (Diamond.subset_rightWedge_iff (Y.hull Z) b).mpr
  exact ⟨max_le hy.1 hz.1, le_min hy.2 hz.2⟩

theorem Diamond.leftWedge_directed (a : ℝ) :
    ∀ Y Z : Diamond,
      Y.toSet ⊆ leftWedge a →
      Z.toSet ⊆ leftWedge a →
      ∃ W : Diamond,
        W.toSet ⊆ leftWedge a ∧
        Y.toSet ⊆ W.toSet ∧ Z.toSet ⊆ W.toSet := by
  intro Y Z hY hZ
  have hy := (Diamond.subset_leftWedge_iff Y a).mp hY
  have hz := (Diamond.subset_leftWedge_iff Z a).mp hZ
  refine ⟨Y.hull Z, ?_,
    Diamond.subset_hull_left Y Z, Diamond.subset_hull_right Y Z⟩
  apply (Diamond.subset_leftWedge_iff (Y.hull Z) a).mpr
  exact ⟨le_min hy.1 hz.1, max_le hy.2 hz.2⟩

/- 7. Separating diamonds with strictly positive collars. -/

theorem Diamond.exists_separating_of_subset_rightWedge
    (Y : Diamond) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hY : Y.toSet ⊆ rightWedge b) :
    ∃ D : Diamond,
      Y.CompactIn D ∧ SpacelikeSets (leftWedge a) D.toSet := by
  rcases (Diamond.subset_rightWedge_iff Y b).mp hY with ⟨hyu, hyv⟩
  let D : Diamond :=
    { u0 := Y.u0 - 1
      u1 := Y.u1 + a / 2
      v0 := Y.v0 - b / 2
      v1 := Y.v1 + 1
      hu := by linarith [Y.hu]
      hv := by linarith [Y.hv] }
  refine ⟨D, ?_, ?_⟩
  · change
      Y.u0 - 1 < Y.u0 ∧ Y.u1 < Y.u1 + a / 2 ∧
      Y.v0 - b / 2 < Y.v0 ∧ Y.v1 < Y.v1 + 1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro p hp q hq
    rcases hp with ⟨hpu, hpv⟩
    change
      Y.u0 - 1 < q.1 ∧ q.1 < Y.u1 + a / 2 ∧
      Y.v0 - b / 2 < q.2 ∧ q.2 < Y.v1 + 1 at hq
    rcases hq with ⟨hqu0, hqu1, hqv0, hqv1⟩
    change (p.1 - q.1) * (p.2 - q.2) < 0
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem Diamond.exists_separating_of_subset_leftWedge
    (X : Diamond) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hX : X.toSet ⊆ leftWedge a) :
    ∃ D : Diamond,
      X.CompactIn D ∧ SpacelikeSets D.toSet (rightWedge b) := by
  rcases (Diamond.subset_leftWedge_iff X a).mp hX with ⟨hxu, hxv⟩
  let D : Diamond :=
    { u0 := X.u0 - a / 2
      u1 := X.u1 + 1
      v0 := X.v0 - 1
      v1 := X.v1 + b / 2
      hu := by linarith [X.hu]
      hv := by linarith [X.hv] }
  refine ⟨D, ?_, ?_⟩
  · change
      X.u0 - a / 2 < X.u0 ∧ X.u1 < X.u1 + 1 ∧
      X.v0 - 1 < X.v0 ∧ X.v1 < X.v1 + b / 2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro p hp q hq
    change
      X.u0 - a / 2 < p.1 ∧ p.1 < X.u1 + 1 ∧
      X.v0 - 1 < p.2 ∧ p.2 < X.v1 + b / 2 at hp
    rcases hp with ⟨hpu0, hpu1, hpv0, hpv1⟩
    rcases hq with ⟨hqu, hqv⟩
    change (p.1 - q.1) * (p.2 - q.2) < 0
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/- 8. Explicit exhaustion by strictly nested inner diamonds. -/

private def shrinkMargin (w : ℝ) (n : ℕ) : ℝ :=
  w / ((n : ℝ) + 3)

private theorem shrinkMargin_pos {w : ℝ} (hw : 0 < w) (n : ℕ) :
    0 < shrinkMargin w n := by
  unfold shrinkMargin
  exact div_pos hw (by positivity)

private theorem shrinkMargin_twice_lt {w : ℝ} (hw : 0 < w) (n : ℕ) :
    2 * shrinkMargin w n < w := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hd : 0 < (n : ℝ) + 3 := by positivity
  have hprod : 0 ≤ w * (n : ℝ) := mul_nonneg hw.le hn
  have hq : w / ((n : ℝ) + 3) < w / 2 := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  change 2 * (w / ((n : ℝ) + 3)) < w
  linarith

private theorem shrinkMargin_succ_lt {w : ℝ} (hw : 0 < w) (n : ℕ) :
    shrinkMargin w (n + 1) < shrinkMargin w n := by
  have hd0 : 0 < (n : ℝ) + 3 := by positivity
  have hd1 : 0 < ((n + 1 : ℕ) : ℝ) + 3 := by positivity
  unfold shrinkMargin
  apply (div_lt_div_iff₀ hd1 hd0).mpr
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

/--
An explicit Archimedean estimate, uniform for all sufficiently large indices.
The width need not be positive for this estimate.
-/
private theorem shrinkMargin_eventually_lt
    (w : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → shrinkMargin w m < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (w / ε)
  refine ⟨n, ?_⟩
  intro m hnm
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hnm
  have hw : w < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  have hmul : (n : ℝ) * ε ≤ (m : ℝ) * ε :=
    mul_le_mul_of_nonneg_right hnm' hε.le
  have hd : 0 < (m : ℝ) + 3 := by positivity
  unfold shrinkMargin
  apply (div_lt_iff₀ hd).mpr
  nlinarith

/-- Shrink each coordinate interval by its width divided by `n + 3` on each side. -/
def Diamond.shrink (Y : Diamond) (n : ℕ) : Diamond where
  u0 := Y.u0 + shrinkMargin (Y.u1 - Y.u0) n
  u1 := Y.u1 - shrinkMargin (Y.u1 - Y.u0) n
  v0 := Y.v0 + shrinkMargin (Y.v1 - Y.v0) n
  v1 := Y.v1 - shrinkMargin (Y.v1 - Y.v0) n
  hu := by
    have h := shrinkMargin_twice_lt (sub_pos.mpr Y.hu) n
    linarith
  hv := by
    have h := shrinkMargin_twice_lt (sub_pos.mpr Y.hv) n
    linarith

theorem Diamond.shrink_compactIn_succ (Y : Diamond) (n : ℕ) :
    (Y.shrink n).CompactIn (Y.shrink (n + 1)) := by
  have hu := shrinkMargin_succ_lt (sub_pos.mpr Y.hu) n
  have hv := shrinkMargin_succ_lt (sub_pos.mpr Y.hv) n
  dsimp only [Diamond.CompactIn, Diamond.shrink]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem Diamond.shrink_compactIn (Y : Diamond) (n : ℕ) :
    (Y.shrink n).CompactIn Y := by
  have hu := shrinkMargin_pos (sub_pos.mpr Y.hu) n
  have hv := shrinkMargin_pos (sub_pos.mpr Y.hv) n
  dsimp only [Diamond.CompactIn, Diamond.shrink]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem Diamond.exists_subset_shrink (Y Z : Diamond)
    (hZ : Z.CompactIn Y) :
    ∃ n : ℕ, Z.toSet ⊆ (Y.shrink n).toSet := by
  rcases hZ with ⟨hz0, hz1, hz2, hz3⟩
  obtain ⟨n0, hn0⟩ := shrinkMargin_eventually_lt
    (Y.u1 - Y.u0) (show 0 < Z.u0 - Y.u0 by linarith)
  obtain ⟨n1, hn1⟩ := shrinkMargin_eventually_lt
    (Y.u1 - Y.u0) (show 0 < Y.u1 - Z.u1 by linarith)
  obtain ⟨n2, hn2⟩ := shrinkMargin_eventually_lt
    (Y.v1 - Y.v0) (show 0 < Z.v0 - Y.v0 by linarith)
  obtain ⟨n3, hn3⟩ := shrinkMargin_eventually_lt
    (Y.v1 - Y.v0) (show 0 < Y.v1 - Z.v1 by linarith)
  let n : ℕ := n0 + n1 + n2 + n3
  have h0 := hn0 n (by dsimp [n]; omega)
  have h1 := hn1 n (by dsimp [n]; omega)
  have h2 := hn2 n (by dsimp [n]; omega)
  have h3 := hn3 n (by dsimp [n]; omega)
  refine ⟨n, ?_⟩
  apply (Diamond.toSet_subset_iff Z (Y.shrink n)).mpr
  change
    Y.u0 + shrinkMargin (Y.u1 - Y.u0) n ≤ Z.u0 ∧
    Z.u1 ≤ Y.u1 - shrinkMargin (Y.u1 - Y.u0) n ∧
    Y.v0 + shrinkMargin (Y.v1 - Y.v0) n ≤ Z.v0 ∧
    Z.v1 ≤ Y.v1 - shrinkMargin (Y.v1 - Y.v0) n
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem Diamond.exhaustion :
    ∀ Y : Diamond, ∃ D : ℕ → Diamond,
      (∀ n, (D n).CompactIn (D (n + 1))) ∧
      (∀ n, (D n).CompactIn Y) ∧
      (∀ Z : Diamond, Z.CompactIn Y →
        ∃ n, Z.toSet ⊆ (D n).toSet) := by
  intro Y
  refine ⟨fun n => Y.shrink n, ?_, ?_, ?_⟩
  · intro n
    exact Diamond.shrink_compactIn_succ Y n
  · intro n
    exact Diamond.shrink_compactIn Y n
  · intro Z hZ
    exact Diamond.exists_subset_shrink Y Z hZ

/- 9. Compact containment. -/

theorem Diamond.CompactIn.subset {Y Z : Diamond}
    (h : Y.CompactIn Z) :
    Y.toSet ⊆ Z.toSet := by
  apply (Diamond.toSet_subset_iff Y Z).mpr
  exact ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

/- 10. Monotonicity and symmetry of spacelike separation. -/

theorem Spacelike.symm {p q : Pt} (h : Spacelike p q) :
    Spacelike q p := by
  have heq :
      (q.1 - p.1) * (q.2 - p.2) =
        (p.1 - q.1) * (p.2 - q.2) := by
    ring
  change (q.1 - p.1) * (q.2 - p.2) < 0
  rw [heq]
  exact h

theorem SpacelikeSets.mono {S T S' T' : Set Pt}
    (h : SpacelikeSets S T) (hS : S' ⊆ S) (hT : T' ⊆ T) :
    SpacelikeSets S' T' := by
  intro p hp q hq
  exact h p (hS hp) q (hT hq)

theorem SpacelikeSets.symm {S T : Set Pt}
    (h : SpacelikeSets S T) :
    SpacelikeSets T S := by
  intro q hq p hp
  exact (h p hp q hq).symm

end

end CTheorem

