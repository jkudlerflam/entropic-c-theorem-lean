import ModularCTheorem.Geometry

/-!
# Extra geometry for the net layer

* `Diamond.CompactInLeft D a`, `Diamond.CompactInRight D b`: the closure of the diamond `D` lies
  in the open wedge `L_a`, resp. `R_b`. A diamond `D' ⋐ D` with `D ⊆ L_a` is of this kind
  (`Diamond.CompactIn.compactInLeft`).
* `leftExhaust a n`, `rightExhaust b n`: explicit exhaustions of the wedges by diamonds, nested in
  the sense of `CompactIn`, cofinal among the diamonds compactly inside the wedge
  (`exists_subset_leftExhaust`, `exists_subset_rightExhaust`).
* `Diamond.CompactIn.of_subset`: `D ⋐ Y ⊆ Y'` gives `D ⋐ Y'`.
-/

namespace CTheorem

noncomputable section

/-! ### Diamonds compactly inside a wedge -/

/-- The closure of `D` lies in the open left wedge `L_a = {u > a, v < 0}`. -/
def Diamond.CompactInLeft (D : Diamond) (a : ℝ) : Prop :=
  a < D.u0 ∧ D.v1 < 0

/-- The closure of `D` lies in the open right wedge `R_b = {u < 0, v > b}`. -/
def Diamond.CompactInRight (D : Diamond) (b : ℝ) : Prop :=
  D.u1 < 0 ∧ b < D.v0

theorem Diamond.CompactInLeft.subset {D : Diamond} {a : ℝ} (h : D.CompactInLeft a) :
    D.toSet ⊆ leftWedge a :=
  (D.subset_leftWedge_iff a).mpr ⟨h.1.le, h.2.le⟩

theorem Diamond.CompactInRight.subset {D : Diamond} {b : ℝ} (h : D.CompactInRight b) :
    D.toSet ⊆ rightWedge b :=
  (D.subset_rightWedge_iff b).mpr ⟨h.1.le, h.2.le⟩

theorem Diamond.CompactInLeft.anti {D : Diamond} {a A : ℝ} (h : D.CompactInLeft A)
    (haA : a ≤ A) : D.CompactInLeft a :=
  ⟨lt_of_le_of_lt haA h.1, h.2⟩

theorem Diamond.CompactInRight.anti {D : Diamond} {b B : ℝ} (h : D.CompactInRight B)
    (hbB : b ≤ B) : D.CompactInRight b :=
  ⟨h.1, lt_of_le_of_lt hbB h.2⟩

/-- A diamond compactly inside a diamond of `L_a` is compactly inside `L_a`. -/
theorem Diamond.CompactIn.compactInLeft {D E : Diamond} {a : ℝ} (h : D.CompactIn E)
    (hE : E.toSet ⊆ leftWedge a) : D.CompactInLeft a := by
  obtain ⟨h1, h2⟩ := (E.subset_leftWedge_iff a).mp hE
  exact ⟨lt_of_le_of_lt h1 h.1, lt_of_lt_of_le h.2.2.2 h2⟩

/-- A diamond compactly inside a diamond of `R_b` is compactly inside `R_b`. -/
theorem Diamond.CompactIn.compactInRight {D E : Diamond} {b : ℝ} (h : D.CompactIn E)
    (hE : E.toSet ⊆ rightWedge b) : D.CompactInRight b := by
  obtain ⟨h1, h2⟩ := (E.subset_rightWedge_iff b).mp hE
  exact ⟨lt_of_lt_of_le h.2.1 h1, lt_of_le_of_lt h2 h.2.2.1⟩

/-- `D ⋐ Y` and `Y ⊆ Y'` give `D ⋐ Y'`. -/
theorem Diamond.CompactIn.of_subset {D Y Y' : Diamond} (h : D.CompactIn Y)
    (hY : Y.toSet ⊆ Y'.toSet) : D.CompactIn Y' := by
  obtain ⟨h1, h2, h3, h4⟩ := (Y.toSet_subset_iff Y').mp hY
  exact ⟨lt_of_le_of_lt h1 h.1, lt_of_lt_of_le h.2.1 h2, lt_of_le_of_lt h3 h.2.2.1,
    lt_of_lt_of_le h.2.2.2 h4⟩

/-! ### Margins of the explicit exhaustions -/

/-- Inner margin `1 / (n + 2)`. -/
private def em (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

/-- Outer extent `n + 2`. -/
private def eM (n : ℕ) : ℝ := (n : ℝ) + 2

private theorem eM_ge_two (n : ℕ) : 2 ≤ eM n := by
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold eM
  linarith

private theorem em_pos (n : ℕ) : 0 < em n := by
  unfold em
  positivity

private theorem em_lt_eM (n : ℕ) : em n < eM n := by
  have h2 := eM_ge_two n
  have hpos : (0 : ℝ) < eM n := by linarith
  have : em n = 1 / eM n := rfl
  rw [this, div_lt_iff₀ hpos]
  nlinarith

private theorem em_succ_lt (n : ℕ) : em (n + 1) < em n := by
  unfold em
  apply one_div_lt_one_div_of_lt (by positivity)
  push_cast
  linarith

private theorem eM_lt_succ (n : ℕ) : eM n < eM (n + 1) := by
  unfold eM
  push_cast
  linarith

private theorem exists_em_lt_eM_gt {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∃ n : ℕ, em n < ε ∧ M < eM n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / ε) M)
  have h1 : 1 / ε < n := lt_of_le_of_lt (le_max_left _ _) hn
  have h2 : M < n := lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n, ?_, ?_⟩
  · have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3 : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp h1
    unfold em
    rw [div_lt_iff₀ hpos]
    linarith
  · unfold eM
    linarith

/-! ### The left wedge -/

/-- Explicit exhaustion of `L_a`: `{a + 1/(n+2) < u < a + n + 2, -(n+2) < v < -1/(n+2)}`. -/
def leftExhaust (a : ℝ) (n : ℕ) : Diamond where
  u0 := a + em n
  u1 := a + eM n
  v0 := -eM n
  v1 := -em n
  hu := by have := em_lt_eM n; linarith
  hv := by have := em_lt_eM n; linarith

theorem leftExhaust_compactIn_succ (a : ℝ) (n : ℕ) :
    (leftExhaust a n).CompactIn (leftExhaust a (n + 1)) := by
  have h1 := em_succ_lt n
  have h2 := eM_lt_succ n
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [leftExhaust] <;> linarith

theorem leftExhaust_compactInLeft (a : ℝ) (n : ℕ) : (leftExhaust a n).CompactInLeft a := by
  have h := em_pos n
  refine ⟨?_, ?_⟩ <;> dsimp only [leftExhaust] <;> linarith

theorem leftExhaust_subset (a : ℝ) (n : ℕ) : (leftExhaust a n).toSet ⊆ leftWedge a :=
  (leftExhaust_compactInLeft a n).subset

/-- Cofinality: every diamond compactly inside `L_a` lies in some `leftExhaust a n`. -/
theorem exists_subset_leftExhaust {D : Diamond} {a : ℝ} (h : D.CompactInLeft a) :
    ∃ n, D.toSet ⊆ (leftExhaust a n).toSet := by
  have hε : 0 < min (D.u0 - a) (-D.v1) := lt_min (by linarith [h.1]) (by linarith [h.2])
  obtain ⟨n, hn1, hn2⟩ := exists_em_lt_eM_gt hε (max (D.u1 - a) (-D.v0))
  have e1 := min_le_left (D.u0 - a) (-D.v1)
  have e2 := min_le_right (D.u0 - a) (-D.v1)
  have e3 := le_max_left (D.u1 - a) (-D.v0)
  have e4 := le_max_right (D.u1 - a) (-D.v0)
  refine ⟨n, (D.toSet_subset_iff _).mpr ⟨?_, ?_, ?_, ?_⟩⟩ <;> dsimp only [leftExhaust] <;>
    linarith

/-! ### The right wedge -/

/-- Explicit exhaustion of `R_b`: `{-(n+2) < u < -1/(n+2), b + 1/(n+2) < v < b + n + 2}`. -/
def rightExhaust (b : ℝ) (n : ℕ) : Diamond where
  u0 := -eM n
  u1 := -em n
  v0 := b + em n
  v1 := b + eM n
  hu := by have := em_lt_eM n; linarith
  hv := by have := em_lt_eM n; linarith

theorem rightExhaust_compactIn_succ (b : ℝ) (n : ℕ) :
    (rightExhaust b n).CompactIn (rightExhaust b (n + 1)) := by
  have h1 := em_succ_lt n
  have h2 := eM_lt_succ n
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [rightExhaust] <;> linarith

theorem rightExhaust_compactInRight (b : ℝ) (n : ℕ) :
    (rightExhaust b n).CompactInRight b := by
  have h := em_pos n
  refine ⟨?_, ?_⟩ <;> dsimp only [rightExhaust] <;> linarith

theorem rightExhaust_subset (b : ℝ) (n : ℕ) : (rightExhaust b n).toSet ⊆ rightWedge b :=
  (rightExhaust_compactInRight b n).subset

/-- Cofinality: every diamond compactly inside `R_b` lies in some `rightExhaust b n`. -/
theorem exists_subset_rightExhaust {D : Diamond} {b : ℝ} (h : D.CompactInRight b) :
    ∃ n, D.toSet ⊆ (rightExhaust b n).toSet := by
  have hε : 0 < min (-D.u1) (D.v0 - b) := lt_min (by linarith [h.1]) (by linarith [h.2])
  obtain ⟨n, hn1, hn2⟩ := exists_em_lt_eM_gt hε (max (-D.u0) (D.v1 - b))
  have e1 := min_le_left (-D.u1) (D.v0 - b)
  have e2 := min_le_right (-D.u1) (D.v0 - b)
  have e3 := le_max_left (-D.u0) (D.v1 - b)
  have e4 := le_max_right (-D.u0) (D.v1 - b)
  refine ⟨n, (D.toSet_subset_iff _).mpr ⟨?_, ?_, ?_, ?_⟩⟩ <;> dsimp only [rightExhaust] <;>
    linarith

end

end CTheorem
