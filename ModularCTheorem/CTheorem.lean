import ModularCTheorem.Net
import ModularCTheorem.TypeI.SSA
import ModularCTheorem.Araki.MIContinuity
import ModularCTheorem.RealCore

/-!
# M. Increasing differences, the functions `𝒟_R`, `𝒟_L`, and the entropic c-theorem

* `fourTerm_of_ladders`, the four-term inequality `I(Xs:Zb) + I(Xb:Zs) ≤ I(Xb:Zb) + I(Xs:Zs)` for
  algebras with type I ladders, from the type I case (`TypeI/SSA.lean`) and upward continuity
  (`Araki/MIContinuity.lean`).
* `CNet.ymono`, **Prop. Ymono**. For `0 < a ≤ A`, `b > 0` and diamonds `Y₁ ⊆ Y₂ ⊆ R_b`,
  `I(L_a:Y₁) − I(L_A:Y₁) ≤ I(L_a:Y₂) − I(L_A:Y₂)`. The mirror statement is `CNet.xmono`.
* `CNet.DRe`, `CNet.DLe` (`EReal` suprema), `CNet.DR`, `CNet.DL` (their real parts), and the
  one-sided c-functions `CNet.CR`, `CNet.CL`.
* `oneSidedData_of_lub`, the order-theoretic step. A least-upper-bound family of increasing
  differences satisfies `OneSidedData` (`CNet.oneSidedData_DR`, `CNet.oneSidedData_DL`).
* `CNet.cTheorem`, **the entropic c-theorem** (note, Thm. 1).

The mirror statement `xmono` needs no `mutualInfo_comm`: `fourTerm_of_ladders` is applied with the
diamonds `X₁ ⊆ X₂` on the first side and the wedges `R_B ⊆ R_b` on the second.
-/

open scoped VonNeumannAlgebra Topology
open VonNeumannAlgebra Filter Set

namespace CTheorem

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The four-term inequality for algebras with type I ladders -/

/-- Finite `EReal` inequalities `x + y ≤ z + w` pass to real parts. -/
theorem toReal_add_le_of_add_le {x y z w : EReal} (hx : x ≠ ⊤) (hx' : x ≠ ⊥)
    (hy : y ≠ ⊤) (hy' : y ≠ ⊥) (hz : z ≠ ⊤) (hz' : z ≠ ⊥) (hw : w ≠ ⊤) (hw' : w ≠ ⊥)
    (h : x + y ≤ z + w) : x.toReal + y.toReal ≤ z.toReal + w.toReal := by
  rw [← EReal.coe_toReal hx hx', ← EReal.coe_toReal hy hy', ← EReal.coe_toReal hz hz',
    ← EReal.coe_toReal hw hw'] at h
  exact_mod_cast h

/-- **Four-term inequality for algebras with type I ladders.** If `Xs ≤ Xb` and `Zs ≤ Zb` have type
I ladders, `Xb ≤ Zb′` and `I(Xb:Zb) < ∞`, then
`I(Xs:Zb) + I(Xb:Zs) ≤ I(Xb:Zb) + I(Xs:Zs)` (all four terms finite, stated for real parts). The
type I four-term inequality holds along the ladders and passes to the limit by upward continuity. -/
theorem fourTerm_of_ladders [TopologicalSpace.SeparableSpace H] {Ω : H}
    {Xb Xs Zb Zs : VonNeumannAlgebra H} (hX : HasTypeILadder Xb Xs) (hZ : HasTypeILadder Zb Zs)
    (hcomm : Xb ≤ Zb′) (hfin : mutualInfo Ω Xb Zb ≠ ⊤) :
    (mutualInfo Ω Xs Zb).toReal + (mutualInfo Ω Xb Zs).toReal ≤
      (mutualInfo Ω Xb Zb).toReal + (mutualInfo Ω Xs Zs).toReal := by
  obtain ⟨X, X', hXm, hX'm, hXI, hX'I, hX'X, hXb, hXs⟩ := hX
  obtain ⟨Z, Z', hZm, hZ'm, hZI, hZ'I, hZ'Z, hZb, hZs⟩ := hZ
  have hXk : ∀ k, X k ≤ Xb := fun k x hx => by
    rw [hXb]
    exact mem_generated_of_mem (Set.mem_iUnion.mpr ⟨k, hx⟩)
  have hZk : ∀ k, Z k ≤ Zb := fun k x hx => by
    rw [hZb]
    exact mem_generated_of_mem (Set.mem_iUnion.mpr ⟨k, hx⟩)
  have hXsb : Xs ≤ Xb := by
    rw [hXs, hXb]
    exact generated_mono (Set.iUnion_mono fun k => SetLike.coe_subset_coe.mpr (hX'X k))
  have hZsb : Zs ≤ Zb := by
    rw [hZs, hZb]
    exact generated_mono (Set.iUnion_mono fun k => SetLike.coe_subset_coe.mpr (hZ'Z k))
  -- every pair below `(Xb, Zb)` commutes and has finite mutual information
  have hc : ∀ {P Q : VonNeumannAlgebra H}, P ≤ Xb → Q ≤ Zb → P ≤ Q′ := fun hP hQ =>
    hP.trans (hcomm.trans (commutant_le hQ))
  have hf : ∀ {P Q : VonNeumannAlgebra H}, P ≤ Xb → Q ≤ Zb →
      mutualInfo Ω P Q ≠ ⊤ ∧ mutualInfo Ω P Q ≠ ⊥ := fun hP hQ =>
    ⟨ne_top_of_le_ne_top hfin (mutualInfo_mono hP hQ),
      mutualInfo_ne_bot_of_le_commutant (hc hP hQ)⟩
  have hX'k : ∀ k, X' k ≤ Xb := fun k => (hX'X k).trans (hXk k)
  have hZ'k : ∀ k, Z' k ≤ Zb := fun k => (hZ'Z k).trans (hZk k)
  -- the four limits
  have t1 := tendsto_mutualInfo_of_monotone (Ω := Ω) hX'm hZm hXs hZb (hc hXsb le_rfl)
    (hf hXsb le_rfl).1
  have t2 := tendsto_mutualInfo_of_monotone (Ω := Ω) hXm hZ'm hXb hZs (hc le_rfl hZsb)
    (hf le_rfl hZsb).1
  have t3 := tendsto_mutualInfo_of_monotone (Ω := Ω) hXm hZm hXb hZb hcomm hfin
  have t4 := tendsto_mutualInfo_of_monotone (Ω := Ω) hX'm hZ'm hXs hZs (hc hXsb hZsb)
    (hf hXsb hZsb).1
  have r1 := (EReal.tendsto_toReal (hf hXsb le_rfl).1 (hf hXsb le_rfl).2).comp t1
  have r2 := (EReal.tendsto_toReal (hf le_rfl hZsb).1 (hf le_rfl hZsb).2).comp t2
  have r3 := (EReal.tendsto_toReal (hf le_rfl le_rfl).1 (hf le_rfl le_rfl).2).comp t3
  have r4 := (EReal.tendsto_toReal (hf hXsb hZsb).1 (hf hXsb hZsb).2).comp t4
  refine le_of_tendsto_of_tendsto' (r1.add r2) (r3.add r4) fun k => ?_
  -- the type I four-term inequality at level `k`
  have hk := mutualInfo_add_le_of_isTypeIFactor (Ω := Ω) (hXI k) (hX'I k) (hZI k) (hZ'I k)
    (hX'X k) (hZ'Z k) (hc (hXk k) (hZk k)) (hf (hXk k) (hZk k)).1
  exact toReal_add_le_of_add_le (hf (hX'k k) (hZk k)).1 (hf (hX'k k) (hZk k)).2
    (hf (hXk k) (hZ'k k)).1 (hf (hXk k) (hZ'k k)).2 (hf (hXk k) (hZk k)).1
    (hf (hXk k) (hZk k)).2 (hf (hX'k k) (hZ'k k)).1 (hf (hX'k k) (hZ'k k)).2 hk

/-! ### From least upper bounds of increasing differences to `OneSidedData` -/

/-- **The order-theoretic step.** Let `Dfun x X y` be the least upper bound of the differences
`i x Z - i X Z` over a nonempty directed family `T y` of diamonds, where `x ↦ i x Z` is antitone,
the differences increase with `Z` (Prop. Ymono), the family shrinks as `y` grows, and a boost `φ`
maps `T y` onto `T (y / μ)` with `i (μ x) (φ Z) = i x Z`. Then, under the UV bound, `Dfun` is a
`OneSidedData`: additivity is the limit of a sum along the directed family. -/
theorem oneSidedData_of_lub {c : ℝ} {Dfun : ℝ → ℝ → ℝ → ℝ}
    (T : ℝ → Diamond → Prop) (i : ℝ → Diamond → ℝ)
    (lub1 : ∀ x X y Z, 0 < x → x ≤ X → 0 < y → T y Z → i x Z - i X Z ≤ Dfun x X y)
    (lub2 : ∀ x X y r, 0 < x → x ≤ X → 0 < y → (∀ Z, T y Z → i x Z - i X Z ≤ r) →
      Dfun x X y ≤ r)
    (hne : ∀ y, 0 < y → ∃ Z, T y Z)
    (hdir : ∀ y Z₁ Z₂, 0 < y → T y Z₁ → T y Z₂ →
      ∃ Z₃, T y Z₃ ∧ Z₁.toSet ⊆ Z₃.toSet ∧ Z₂.toSet ⊆ Z₃.toSet)
    (hmono : ∀ x X y Z, 0 < x → x ≤ X → 0 < y → T y Z → i X Z ≤ i x Z)
    (hincr : ∀ x X y Z₁ Z₂, 0 < x → x ≤ X → 0 < y → T y Z₁ → T y Z₂ →
      Z₁.toSet ⊆ Z₂.toSet → i x Z₁ - i X Z₁ ≤ i x Z₂ - i X Z₂)
    (hboost : ∀ μ, 0 < μ → ∃ φ : Diamond → Diamond,
      (∀ y Z, 0 < y → T y Z → T (y / μ) (φ Z)) ∧
      (∀ y Z', 0 < y → T (y / μ) Z' → ∃ Z, T y Z ∧ Z' = φ Z) ∧
      (∀ x y Z, 0 < x → 0 < y → T y Z → i (μ * x) (φ Z) = i x Z))
    (hanti : ∀ y y' Z, 0 < y → y ≤ y' → T y' Z → T y Z)
    (huv : ∀ x X y, 0 < x → x ≤ X → 0 < y → Dfun x X y ≤ c / 6 * Real.log (X / x)) :
    OneSidedData Dfun c where
  nonneg := by
    intro a A b ha haA hb
    obtain ⟨Z, hZ⟩ := hne b hb
    have h1 := lub1 a A b Z ha haA hb hZ
    have h2 := hmono a A b Z ha haA hb hZ
    linarith
  add := by
    intro a A A' b ha haA hAA' hb
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have haA' : a ≤ A' := haA.trans hAA'
    apply le_antisymm
    · have key : ∀ Z₁, T b Z₁ → i a Z₁ - i A Z₁ ≤ Dfun a A' b - Dfun A A' b := by
        intro Z₁ hZ₁
        have hle : Dfun A A' b ≤ Dfun a A' b - (i a Z₁ - i A Z₁) := by
          apply lub2 A A' b _ hA hAA' hb
          intro Z₂ hZ₂
          obtain ⟨Z₃, hZ₃, h13, h23⟩ := hdir b Z₁ Z₂ hb hZ₁ hZ₂
          have e1 := hincr a A b Z₁ Z₃ ha haA hb hZ₁ hZ₃ h13
          have e2 := hincr A A' b Z₂ Z₃ hA hAA' hb hZ₂ hZ₃ h23
          have e3 := lub1 a A' b Z₃ ha haA' hb hZ₃
          linarith
        linarith
      have h := lub2 a A b _ ha haA hb key
      linarith
    · apply lub2 a A' b _ ha haA' hb
      intro Z hZ
      have e1 := lub1 a A b Z ha haA hb hZ
      have e2 := lub1 A A' b Z hA hAA' hb hZ
      linarith
  boost := by
    intro μ a A b hμ ha haA hb
    obtain ⟨φ, hφ1, hφ2, hφ3⟩ := hboost μ hμ
    have hμa : 0 < μ * a := mul_pos hμ ha
    have hμaA : μ * a ≤ μ * A := mul_le_mul_of_nonneg_left haA hμ.le
    have hbμ : 0 < b / μ := div_pos hb hμ
    have hA : 0 < A := lt_of_lt_of_le ha haA
    apply le_antisymm
    · apply lub2 _ _ _ _ hμa hμaA hbμ
      intro Z' hZ'
      obtain ⟨Z, hZ, rfl⟩ := hφ2 b Z' hb hZ'
      rw [hφ3 a b Z ha hb hZ, hφ3 A b Z hA hb hZ]
      exact lub1 a A b Z ha haA hb hZ
    · apply lub2 _ _ _ _ ha haA hb
      intro Z hZ
      rw [← hφ3 a b Z ha hb hZ, ← hφ3 A b Z hA hb hZ]
      exact lub1 _ _ _ _ hμa hμaA hbμ (hφ1 b Z hb hZ)
  anti_b := by
    intro a A b B ha haA hb hbB
    apply lub2 _ _ _ _ ha haA (lt_of_lt_of_le hb hbB)
    intro Z hZ
    exact lub1 a A b Z ha haA hb (hanti b B Z hb hbB hZ)
  uv := huv

namespace CNet

variable (N : CNet H)

/-! ### Prop. Ymono (increasing differences) -/

/-- **Prop. Ymono.** For `0 < a ≤ A`, `b > 0` and diamonds `Y₁ ⊆ Y₂ ⊆ R_b`,
`I(L_a:Y₁) − I(L_A:Y₁) ≤ I(L_a:Y₂) − I(L_A:Y₂)`. -/
theorem ymono [TopologicalSpace.SeparableSpace H] {a A b : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hb : 0 < b) {Y₁ Y₂ : Diamond} (h12 : Y₁.toSet ⊆ Y₂.toSet) (h2 : Y₂.toSet ⊆ rightWedge b) :
    (mutualInfo N.Ω (N.AL a) (N.A Y₁)).toReal - (mutualInfo N.Ω (N.AL A) (N.A Y₁)).toReal ≤
      (mutualInfo N.Ω (N.AL a) (N.A Y₂)).toReal - (mutualInfo N.Ω (N.AL A) (N.A Y₂)).toReal := by
  have h := fourTerm_of_ladders (Ω := N.Ω) (N.hasTypeILadder_AL haA) (N.hasTypeILadder_A h12)
    (N.AL_le_commutant ha.le hb.le h2) (N.mutualInfo_AL_ne_top ha hb h2)
  linarith

/-- **Prop. Ymono, mirror.** For `a > 0`, `0 < b ≤ B` and diamonds `X₁ ⊆ X₂ ⊆ L_a`,
`I(X₁:R_b) − I(X₁:R_B) ≤ I(X₂:R_b) − I(X₂:R_B)`. -/
theorem xmono [TopologicalSpace.SeparableSpace H] {a b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hbB : b ≤ B) {X₁ X₂ : Diamond} (h12 : X₁.toSet ⊆ X₂.toSet) (h2 : X₂.toSet ⊆ leftWedge a) :
    (mutualInfo N.Ω (N.A X₁) (N.AR b)).toReal - (mutualInfo N.Ω (N.A X₁) (N.AR B)).toReal ≤
      (mutualInfo N.Ω (N.A X₂) (N.AR b)).toReal - (mutualInfo N.Ω (N.A X₂) (N.AR B)).toReal := by
  have h := fourTerm_of_ladders (Ω := N.Ω) (N.hasTypeILadder_A h12) (N.hasTypeILadder_AR hbB)
    (N.A_le_commutant_AR ha.le hb.le h2) (N.mutualInfo_AR_ne_top ha hb h2)
  linarith

/-! ### The functions `𝒟_R`, `𝒟_L` and the one-sided c-functions -/

/-- `𝒟_R(a,A;b) = sup_{Y ⊆ R_b} [I(L_a:Y) − I(L_A:Y)]`, as an `EReal` supremum over diamonds. -/
def DRe (a A b : ℝ) : EReal :=
  ⨆ (Y : Diamond) (_ : Y.toSet ⊆ rightWedge b),
    (mutualInfo N.Ω (N.AL a) (N.A Y) - mutualInfo N.Ω (N.AL A) (N.A Y))

/-- `𝒟_L(a;b,B) = sup_{X ⊆ L_a} [I(X:R_b) − I(X:R_B)]`, as an `EReal` supremum over diamonds. -/
def DLe (a b B : ℝ) : EReal :=
  ⨆ (X : Diamond) (_ : X.toSet ⊆ leftWedge a),
    (mutualInfo N.Ω (N.A X) (N.AR b) - mutualInfo N.Ω (N.A X) (N.AR B))

/-- The real value of `𝒟_R` (finite under the UV assumption). -/
def DR (a A b : ℝ) : ℝ := (N.DRe a A b).toReal

/-- The real value of `𝒟_L` (finite under the UV assumption). -/
def DL (a b B : ℝ) : ℝ := (N.DLe a b B).toReal

/-- `C_R(a,b) = 6 a ∂⁺_A 𝒟_R(a,A;b)|_{A=a}`. -/
def CR (a b : ℝ) : ℝ := 6 * a * derivWithin (fun A => N.DR a A b) (Ici a) a

/-- `C_L(a,b) = 6 b ∂⁺_B 𝒟_L(a;b,B)|_{B=b}`. -/
def CL (a b : ℝ) : ℝ := 6 * b * derivWithin (fun B => N.DL a b B) (Ici b) b

/-! ### `𝒟_R` as a least upper bound -/

theorem DRe_term {a A b : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) {Y : Diamond}
    (hY : Y.toSet ⊆ rightWedge b) :
    mutualInfo N.Ω (N.AL a) (N.A Y) - mutualInfo N.Ω (N.AL A) (N.A Y) =
      (((mutualInfo N.Ω (N.AL a) (N.A Y)).toReal -
        (mutualInfo N.Ω (N.AL A) (N.A Y)).toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_toReal (N.mutualInfo_AL_ne_top ha hb hY)
      (N.mutualInfo_AL_ne_bot ha.le hb.le hY),
    EReal.coe_toReal (N.mutualInfo_AL_ne_top hA hb hY) (N.mutualInfo_AL_ne_bot hA.le hb.le hY)]

theorem le_DRe {a A b : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) {Y : Diamond}
    (hY : Y.toSet ⊆ rightWedge b) :
    (((mutualInfo N.Ω (N.AL a) (N.A Y)).toReal -
        (mutualInfo N.Ω (N.AL A) (N.A Y)).toReal : ℝ) : EReal) ≤ N.DRe a A b := by
  rw [← N.DRe_term ha hA hb hY]
  exact le_iSup₂_of_le Y hY le_rfl

theorem DRe_le {a A b r : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b)
    (h : ∀ Y : Diamond, Y.toSet ⊆ rightWedge b →
      (mutualInfo N.Ω (N.AL a) (N.A Y)).toReal - (mutualInfo N.Ω (N.AL A) (N.A Y)).toReal ≤ r) :
    N.DRe a A b ≤ (r : EReal) := by
  refine iSup₂_le fun Y hY => ?_
  rw [N.DRe_term ha hA hb hY]
  exact EReal.coe_le_coe_iff.mpr (h Y hY)

theorem DRe_ne_bot {a A b : ℝ} (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) : N.DRe a A b ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (N.le_DRe ha hA hb (rightExhaust_subset b 0))

/-- The UV assumption on `𝒟_R`. -/
def UVR (c : ℝ) : Prop :=
  ∀ a A b : ℝ, 0 < a → a ≤ A → 0 < b → N.DRe a A b ≤ ((c / 6 * Real.log (A / a) : ℝ) : EReal)

/-- The UV assumption on `𝒟_L`. -/
def UVL (c : ℝ) : Prop :=
  ∀ a b B : ℝ, 0 < a → 0 < b → b ≤ B → N.DLe a b B ≤ ((c / 6 * Real.log (B / b) : ℝ) : EReal)

/-- **`𝒟_R` is a `OneSidedData`**: nonnegativity, additivity (Prop. Ymono and directedness of the
diamonds in `R_b`), boost covariance, decrease in `b`, and the UV bound. -/
theorem oneSidedData_DR [TopologicalSpace.SeparableSpace H] {c : ℝ} (huv : N.UVR c) :
    OneSidedData N.DR c := by
  have hfin : ∀ a A b, 0 < a → a ≤ A → 0 < b → N.DRe a A b ≠ ⊤ := fun a A b ha haA hb =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (huv a A b ha haA hb)
  refine oneSidedData_of_lub (fun b Y => Y.toSet ⊆ rightWedge b)
    (fun a Y => (mutualInfo N.Ω (N.AL a) (N.A Y)).toReal) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- least upper bound, (i)
    intro a A b Y ha haA hb hY
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have h := EReal.toReal_le_toReal (N.le_DRe ha hA hb hY) (EReal.coe_ne_bot _)
      (hfin a A b ha haA hb)
    rwa [EReal.toReal_coe] at h
  · -- least upper bound, (ii)
    intro a A b r ha haA hb h
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have h' := EReal.toReal_le_toReal (N.DRe_le ha hA hb h) (N.DRe_ne_bot ha hA hb)
      (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at h'
  · -- nonempty
    intro b _
    exact ⟨rightExhaust b 0, rightExhaust_subset b 0⟩
  · -- directed
    intro b Y₁ Y₂ _ hY₁ hY₂
    exact Diamond.rightWedge_directed b Y₁ Y₂ hY₁ hY₂
  · -- `a ↦ I(L_a:Y)` is antitone
    intro a A b Y ha haA hb hY
    have hA : 0 < A := lt_of_lt_of_le ha haA
    exact EReal.toReal_le_toReal (mutualInfo_mono (N.AL_anti haA) le_rfl)
      (N.mutualInfo_AL_ne_bot hA.le hb.le hY) (N.mutualInfo_AL_ne_top ha hb hY)
  · -- Prop. Ymono
    intro a A b Y₁ Y₂ ha haA hb _ hY₂ h12
    exact N.ymono ha haA hb h12 hY₂
  · -- boost covariance
    intro μ hμ
    obtain ⟨U, hUΩ, hUD, hUL, -⟩ := N.exists_boost μ hμ
    refine ⟨fun Y => Y.boost μ hμ, fun b Y _ hY => (Y.boost_subset_rightWedge_iff hμ).mpr hY,
      fun b Y' _ hY' => Y'.exists_boost_of_subset_rightWedge hμ hY', ?_⟩
    intro a b Y _ _ _
    simp only
    rw [← hUL a, ← hUD Y, mutualInfo_conj_self U hUΩ]
  · -- diamonds in `R_B` are diamonds in `R_b`
    intro b B Y _ hbB hY
    exact hY.trans (rightWedge_anti hbB)
  · -- UV bound
    intro a A b ha haA hb
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have h := EReal.toReal_le_toReal (huv a A b ha haA hb) (N.DRe_ne_bot ha hA hb)
      (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at h

/-! ### `𝒟_L` as a least upper bound -/

theorem DLe_term {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) {X : Diamond}
    (hX : X.toSet ⊆ leftWedge a) :
    mutualInfo N.Ω (N.A X) (N.AR b) - mutualInfo N.Ω (N.A X) (N.AR B) =
      (((mutualInfo N.Ω (N.A X) (N.AR b)).toReal -
        (mutualInfo N.Ω (N.A X) (N.AR B)).toReal : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.coe_toReal (N.mutualInfo_AR_ne_top ha hb hX)
      (N.mutualInfo_AR_ne_bot ha.le hb.le hX),
    EReal.coe_toReal (N.mutualInfo_AR_ne_top ha hB hX) (N.mutualInfo_AR_ne_bot ha.le hB.le hX)]

theorem le_DLe {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) {X : Diamond}
    (hX : X.toSet ⊆ leftWedge a) :
    (((mutualInfo N.Ω (N.A X) (N.AR b)).toReal -
        (mutualInfo N.Ω (N.A X) (N.AR B)).toReal : ℝ) : EReal) ≤ N.DLe a b B := by
  rw [← N.DLe_term ha hb hB hX]
  exact le_iSup₂_of_le X hX le_rfl

theorem DLe_le {a b B r : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 0 < B)
    (h : ∀ X : Diamond, X.toSet ⊆ leftWedge a →
      (mutualInfo N.Ω (N.A X) (N.AR b)).toReal - (mutualInfo N.Ω (N.A X) (N.AR B)).toReal ≤ r) :
    N.DLe a b B ≤ (r : EReal) := by
  refine iSup₂_le fun X hX => ?_
  rw [N.DLe_term ha hb hB hX]
  exact EReal.coe_le_coe_iff.mpr (h X hX)

theorem DLe_ne_bot {a b B : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) : N.DLe a b B ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (N.le_DLe ha hb hB (leftExhaust_subset a 0))

/-- **`𝒟_L` is a `OneSidedData`** in the variables `(b, B; a)`. -/
theorem oneSidedData_DL [TopologicalSpace.SeparableSpace H] {c : ℝ} (huv : N.UVL c) :
    OneSidedData (fun b B a => N.DL a b B) c := by
  have hfin : ∀ a b B, 0 < a → 0 < b → b ≤ B → N.DLe a b B ≠ ⊤ := fun a b B ha hb hbB =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (huv a b B ha hb hbB)
  refine oneSidedData_of_lub (fun a X => X.toSet ⊆ leftWedge a)
    (fun b X => (mutualInfo N.Ω (N.A X) (N.AR b)).toReal) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- least upper bound, (i)
    intro b B a X hb hbB ha hX
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    have h := EReal.toReal_le_toReal (N.le_DLe ha hb hB hX) (EReal.coe_ne_bot _)
      (hfin a b B ha hb hbB)
    rwa [EReal.toReal_coe] at h
  · -- least upper bound, (ii)
    intro b B a r hb hbB ha h
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    have h' := EReal.toReal_le_toReal (N.DLe_le ha hb hB h) (N.DLe_ne_bot ha hb hB)
      (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at h'
  · -- nonempty
    intro a _
    exact ⟨leftExhaust a 0, leftExhaust_subset a 0⟩
  · -- directed
    intro a X₁ X₂ _ hX₁ hX₂
    exact Diamond.leftWedge_directed a X₁ X₂ hX₁ hX₂
  · -- `b ↦ I(X:R_b)` is antitone
    intro b B a X hb hbB ha hX
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    exact EReal.toReal_le_toReal (mutualInfo_mono le_rfl (N.AR_anti hbB))
      (N.mutualInfo_AR_ne_bot ha.le hB.le hX) (N.mutualInfo_AR_ne_top ha hb hX)
  · -- Prop. Ymono, mirror
    intro b B a X₁ X₂ hb hbB ha _ hX₂ h12
    exact N.xmono ha hb hbB h12 hX₂
  · -- boost covariance, through the boost by `μ⁻¹`
    intro μ hμ
    have hμ' : 0 < μ⁻¹ := inv_pos.mpr hμ
    obtain ⟨U, hUΩ, hUD, -, hUR⟩ := N.exists_boost μ⁻¹ hμ'
    refine ⟨fun X => X.boost μ⁻¹ hμ', fun a X _ hX => ?_, fun a X' _ hX' => ?_, ?_⟩
    · rw [div_eq_inv_mul]
      exact (X.boost_subset_leftWedge_iff hμ').mpr hX
    · rw [div_eq_inv_mul] at hX'
      exact X'.exists_boost_of_subset_leftWedge hμ' hX'
    · intro b a X _ _ _
      simp only
      rw [show μ * b = b / μ⁻¹ by rw [div_inv_eq_mul, mul_comm], ← hUR b, ← hUD X,
        mutualInfo_conj_self U hUΩ]
  · -- diamonds in `L_{a'}` are diamonds in `L_a`
    intro a a' X _ haa' hX
    exact hX.trans (leftWedge_anti haa')
  · -- UV bound
    intro b B a hb hbB ha
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    have h := EReal.toReal_le_toReal (huv a b B ha hb hbB) (N.DLe_ne_bot ha hb hB)
      (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at h

/-! ### The entropic c-theorem -/

/-- **The entropic c-theorem** (note, Thm. 1). For a net satisfying the hypotheses of `CNet` on a
separable Hilbert space, with the UV bounds `𝒟_R(a,A;b) ≤ (c_R/6) log(A/a)` and
`𝒟_L(a;b,B) ≤ (c_L/6) log(B/b)`, the right derivatives defining `C_R`, `C_L` exist and
`C_R(a,b) = f_R(√(ab))`, `C_L(a,b) = f_L(√(ab))` with `f_R, f_L` non-negative, bounded by the UV
constants, and non-increasing on `(0, ∞)`. -/
theorem cTheorem [TopologicalSpace.SeparableSpace H] {cUVR cUVL : ℝ}
    (huvR : ∀ a A b : ℝ, 0 < a → a ≤ A → 0 < b →
      N.DRe a A b ≤ ((cUVR / 6 * Real.log (A / a) : ℝ) : EReal))
    (huvL : ∀ a b B : ℝ, 0 < a → 0 < b → b ≤ B →
      N.DLe a b B ≤ ((cUVL / 6 * Real.log (B / b) : ℝ) : EReal)) :
    ∃ fR fL : ℝ → ℝ,
      (∀ r, 0 < r → 0 ≤ fR r) ∧ (∀ r, 0 < r → fR r ≤ cUVR) ∧ AntitoneOn fR (Ioi 0) ∧
      (∀ r, 0 < r → 0 ≤ fL r) ∧ (∀ r, 0 < r → fL r ≤ cUVL) ∧ AntitoneOn fL (Ioi 0) ∧
      (∀ a b, 0 < a → 0 < b →
        HasDerivWithinAt (fun A => N.DR a A b) (fR (Real.sqrt (a * b)) / (6 * a)) (Ici a) a) ∧
      (∀ a b, 0 < a → 0 < b →
        HasDerivWithinAt (fun B => N.DL a b B) (fL (Real.sqrt (a * b)) / (6 * b)) (Ici b) b) ∧
      (∀ a b, 0 < a → 0 < b → N.CR a b = fR (Real.sqrt (a * b))) ∧
      (∀ a b, 0 < a → 0 < b → N.CL a b = fL (Real.sqrt (a * b))) := by
  obtain ⟨fR, hR0, hRc, hRanti, hRderiv, hRC⟩ := (N.oneSidedData_DR huvR).cTheorem_with_cR
  obtain ⟨fL, hL0, hLc, hLanti, hLderiv, hLC⟩ := (N.oneSidedData_DL huvL).cTheorem_with_cR
  refine ⟨fR, fL, hR0, hRc, hRanti, hL0, hLc, hLanti, hRderiv, ?_, ?_, ?_⟩
  · intro a b ha hb
    have h := hLderiv b a hb ha
    rw [mul_comm b a] at h
    exact h
  · intro a b ha hb
    exact hRC a b ha hb
  · intro a b ha hb
    have h := hLC b a hb ha
    rw [mul_comm b a] at h
    exact h

end CNet

end

end CTheorem
