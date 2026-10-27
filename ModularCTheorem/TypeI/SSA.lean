import ModularCTheorem.Araki.MutualInfo
import ModularCTheorem.Araki.MatrixFactor
import ModularCTheorem.Araki.MIContinuity
import ModularCTheorem.TypeI.Approximation

/-!
# T3. Four-term inequality for type I factors

The type I ladder proof of Prop. Ymono needs, for type I factors `X' ≤ X`, `Z' ≤ Z` with `X ≤ Z′`
and `I(X:Z) < ∞`, the four-term inequality `I(X':Z) + I(X:Z') ≤ I(X:Z) + I(X':Z')` (blueprint §1).

## Route

* **Approximation (T4).** `X' ≤ X` is approximated by increasing unital matrix subfactors
  `P n ↑ X'` and `R n ≤ X'′` with `P n ∨ R n ↑ X` (`CTheorem.SSA.IsMatrixApprox`); likewise
  `Z' ≤ Z` by `P' n`, `R' n`.
* **Finite level (T6).** For each `n` the four matrix subfactors `P n, R n, P' n, R' n` commute
  pairwise (`X ≤ Z′` across, `R n ≤ X'′` within), so B's `mutualInfo_fourTerm` (finite-dimensional
  strong subadditivity) gives
  `I(P n : Q' n) + I(Q n : P' n) ≤ I(Q n : Q' n) + I(P n : P' n)`, `Q n = P n ∨ R n`,
  `Q' n = P' n ∨ R' n`.
* **Limit (T1).** `tendsto_mutualInfo_of_monotone` four times; all limits are finite
  (`mutualInfo_mono`, `hfin`), so the `EReal` sums pass to the limit.
* **Normalisation.** `mutualInfo_fourTerm` is stated for `‖Ω‖ = 1`. The general case follows by
  rescaling: `I_{cΩ}(X:Z) = c² I_Ω(X:Z) - c² ‖Ω‖² log c²` for `c > 0`
  (`CTheorem.SSA.mutualInfo_smul_eq`), an increasing affine map with the same constant for all four
  terms; `Ω = 0` gives `I = 0` throughout.

## Main results

* `CTheorem.mutualInfo_add_le_of_approx` — the four-term inequality from matrix approximations,
  for any `Ω`.
* `CTheorem.mutualInfo_add_le_of_isTypeIFactor` — the type I statement (T4, in the iso form of
  `CTheorem.SSA.IsMatrixApprox`, is `CTheorem.exists_matrixSubfactor_seq_pair`).
-/

open scoped VonNeumannAlgebra InnerProductSpace Araki Topology
open VonNeumannAlgebra Filter

namespace CTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace SSA

/-- **Tensor-compatible matrix approximation** of `X' ≤ X`: increasing unital matrix subfactors
`P n ↑ X'` and `R n` commuting with `X'`, such that the joins `P n ∨ R n` increase to `X`. Each
`P n`, `R n` comes with a `⋆`-isomorphism onto a full matrix algebra `B(ℂ^d)`. -/
structure IsMatrixApprox (X' X : VonNeumannAlgebra H) (P R : ℕ → VonNeumannAlgebra H) : Prop where
  P_mono : Monotone P
  R_mono : Monotone R
  P_le : ∀ n, P n ≤ X'
  R_le_commutant : ∀ n, R n ≤ X'.commutant
  P_gen : X' = generated (⋃ n, (P n : Set (H →L[ℂ] H)))
  join_gen : X = generated (⋃ n, (join (P n) (R n) : Set (H →L[ℂ] H)))
  P_mat : ∀ n, ∃ d : ℕ,
    Nonempty (P n ≃⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
  R_mat : ∀ n, ∃ d : ℕ,
    Nonempty (R n ≃⋆ₐ[ℂ] (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))

namespace IsMatrixApprox

variable {X' X : VonNeumannAlgebra H} {P R : ℕ → VonNeumannAlgebra H}

lemma join_le (h : IsMatrixApprox X' X P R) (n : ℕ) : join (P n) (R n) ≤ X := by
  rw [h.join_gen]
  exact fun y hy => mem_generated_of_mem (Set.mem_iUnion.2 ⟨n, hy⟩)

lemma P_le_of (h : IsMatrixApprox X' X P R) (n : ℕ) : P n ≤ X :=
  (le_join_left _ _).trans (h.join_le n)

lemma R_le (h : IsMatrixApprox X' X P R) (n : ℕ) : R n ≤ X :=
  (le_join_right _ _).trans (h.join_le n)

lemma join_mono (h : IsMatrixApprox X' X P R) : Monotone fun n => join (P n) (R n) :=
  fun _ _ hmn => CTheorem.join_mono (h.P_mono hmn) (h.R_mono hmn)

/-- Within one approximation, `P n` and `R n` commute. -/
lemma P_le_commutant_R (h : IsMatrixApprox X' X P R) (n : ℕ) : P n ≤ (R n)′ :=
  le_commutant_comm ((h.R_le_commutant n).trans (commutant_le (h.P_le n)))

end IsMatrixApprox

/-! ### Finiteness and rescaling of the mutual information -/

/-- A finite mutual information of commuting algebras is a real number (it is never `⊥`). -/
lemma mutualInfo_eq_coe_toReal {Ω : H} {A B : VonNeumannAlgebra H} (hAB : A ≤ B′)
    (h : mutualInfo Ω A B ≠ ⊤) : mutualInfo Ω A B = ((mutualInfo Ω A B).toReal : EReal) := by
  obtain ⟨φ, hφ⟩ := exists_isProduct_of_ne_top h
  have hbot : mutualInfo Ω A B ≠ ⊥ := by
    rw [mutualInfo_eq_arakiEntropy hAB hφ]
    exact arakiEntropy_ne_bot _ _
  exact (EReal.coe_toReal h hbot).symm

/-- `(ω_{cΩ})(y) = c² ω_Ω(y)` for real `c`. -/
lemma ofVector_smul_apply (M : VonNeumannAlgebra H) (Ω : H) (c : ℝ) (y : M) :
    (NormalFunctional.ofVector M ((c : ℂ) • Ω)).1 y =
      ((c ^ 2 : ℝ) : ℂ) * (NormalFunctional.ofVector M Ω).1 y := by
  change ⟪(c : ℂ) • Ω, (y : H →L[ℂ] H) ((c : ℂ) • Ω)⟫_ℂ =
    ((c ^ 2 : ℝ) : ℂ) * ⟪Ω, (y : H →L[ℂ] H) Ω⟫_ℂ
  rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

/-- `Re ω_Ω(1) = ‖Ω‖²`. -/
lemma re_ofVector_one (M : VonNeumannAlgebra H) (Ω : H) :
    ((NormalFunctional.ofVector M Ω).1 1).re = ‖Ω‖ ^ 2 := by
  change (⟪Ω, ((1 : M) : H →L[ℂ] H) Ω⟫_ℂ).re = ‖Ω‖ ^ 2
  rw [OneMemClass.coe_one, one_apply_eq_self]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) Ω

/-- **Rescaling the vector.** For commuting `X, Z` with a product functional for `Ω`, `c > 0`
and `I_Ω(X:Z) < ∞`: `I_{cΩ}(X:Z) = c² I_Ω(X:Z) - c² ‖Ω‖² log c²`. The product functional for `cΩ`
is `c⁴ φ`, realised as the amplified vector functional of `c² Ξ_φ`. -/
lemma mutualInfo_smul_eq {Ω : H} {X Z : VonNeumannAlgebra H} (hXZ : X ≤ Z′)
    (hfin : mutualInfo Ω X Z ≠ ⊤) {c : ℝ} (hc : 0 < c) :
    mutualInfo ((c : ℂ) • Ω) X Z =
      ((c ^ 2 * (mutualInfo Ω X Z).toReal - c ^ 2 * ‖Ω‖ ^ 2 * Real.log (c ^ 2) : ℝ) : EReal) := by
  obtain ⟨φ, hφ⟩ := exists_isProduct_of_ne_top hfin
  -- the rescaled product functional `c⁴ φ`
  set φc : (join X Z).NormalFunctional :=
    NormalFunctional.ofAmplifiedVector (join X Z) (((c ^ 2 : ℝ) : ℂ) • φ.2.vec) with hφc_def
  have hφc : ∀ y, φc.1 y = ((c ^ 2 * c ^ 2 : ℝ) : ℂ) * φ.1 y := fun y => by
    change ⟪((c ^ 2 : ℝ) : ℂ) • φ.2.vec,
      (HilbertTensor.amplifyRight (y : H →L[ℂ] H)) (((c ^ 2 : ℝ) : ℂ) • φ.2.vec)⟫_ℂ = _
    rw [map_smul, inner_smul_left, inner_smul_right, φ.2.inner_vec_amplifyRight y,
      Complex.conj_ofReal]
    push_cast
    ring
  have hφcP : IsProduct ((c : ℂ) • Ω) X Z φc := by
    intro x hx z hz
    rw [hφc, hφ x hx z hz, map_smul, inner_smul_left, inner_smul_right, map_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  have hψc := ofVector_smul_apply (join X Z) Ω c
  rw [mutualInfo_eq_arakiEntropy hXZ hφcP, mutualInfo_eq_arakiEntropy hXZ hφ,
    arakiEntropy_of_apply_eq_mul_right (by positivity) hφc,
    arakiEntropy_of_apply_eq_mul_left hψc]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, S⟦NormalFunctional.ofVector (join X Z) Ω ∥ φ⟧ = a := by
    refine ⟨_, (EReal.coe_toReal ?_ (arakiEntropy_ne_bot _ _)).symm⟩
    rwa [← mutualInfo_eq_arakiEntropy hXZ hφ]
  have h1 : ((NormalFunctional.ofVector (join X Z) ((c : ℂ) • Ω)).1 1).re = c ^ 2 * ‖Ω‖ ^ 2 := by
    rw [hψc, Complex.re_ofReal_mul, re_ofVector_one]
  have hlog : Real.log (c ^ 2 * c ^ 2) = Real.log (c ^ 2) + Real.log (c ^ 2) :=
    Real.log_mul (by positivity) (by positivity)
  rw [ha, EReal.toReal_coe, h1, re_ofVector_one, hlog, ← EReal.coe_add, ← EReal.coe_mul,
    ← EReal.coe_sub, EReal.coe_eq_coe_iff]
  ring

/-- For `Ω = 0` the mutual information of commuting algebras vanishes. -/
lemma mutualInfo_zero_vector {A B : VonNeumannAlgebra H} (hAB : A ≤ B′) :
    mutualInfo (0 : H) A B = 0 := by
  have hP : IsProduct (0 : H) A B (NormalFunctional.ofVector (join A B) 0) := by
    intro x hx z hz
    change ⟪(0 : H), (x * z) 0⟫_ℂ = ⟪(0 : H), x 0⟫_ℂ * ⟪(0 : H), z 0⟫_ℂ
    simp
  rw [mutualInfo_eq_arakiEntropy hAB hP, arakiEntropy_self]

end SSA

open SSA

/-! ### The four-term inequality from matrix approximations -/

/-- **Four-term inequality from matrix approximations, `‖Ω‖ = 1`.** -/
theorem mutualInfo_add_le_of_approx_of_norm_eq_one {Ω : H} (hΩ : ‖Ω‖ = 1)
    {X X' Z Z' : VonNeumannAlgebra H} {P R P' R' : ℕ → VonNeumannAlgebra H}
    (hXa : IsMatrixApprox X' X P R) (hZa : IsMatrixApprox Z' Z P' R')
    (hXX' : X' ≤ X) (hZZ' : Z' ≤ Z) (hXZ : X ≤ Z′) (hfin : mutualInfo Ω X Z ≠ ⊤) :
    mutualInfo Ω X' Z + mutualInfo Ω X Z' ≤ mutualInfo Ω X Z + mutualInfo Ω X' Z' := by
  -- commutation across the two sides
  have hc : ∀ {A B : VonNeumannAlgebra H}, A ≤ X → B ≤ Z → A ≤ B′ := fun hA hB =>
    (hA.trans hXZ).trans (commutant_le hB)
  -- the finite-dimensional four-term inequality at level `n`
  have hineq : ∀ n, mutualInfo Ω (P n) (join (P' n) (R' n)) +
      mutualInfo Ω (join (P n) (R n)) (P' n) ≤
        mutualInfo Ω (join (P n) (R n)) (join (P' n) (R' n)) + mutualInfo Ω (P n) (P' n) := by
    intro n
    obtain ⟨_, ⟨ΦP⟩⟩ := hXa.P_mat n
    obtain ⟨_, ⟨ΦR⟩⟩ := hXa.R_mat n
    obtain ⟨_, ⟨ΦP'⟩⟩ := hZa.P_mat n
    obtain ⟨_, ⟨ΦR'⟩⟩ := hZa.R_mat n
    exact mutualInfo_fourTerm hΩ ΦP ΦR ΦP' ΦR' (hXa.P_le_commutant_R n)
      (hc (hXa.P_le_of n) (hZa.P_le_of n)) (hc (hXa.P_le_of n) (hZa.R_le n))
      (hc (hXa.R_le n) (hZa.P_le_of n)) (hc (hXa.R_le n) (hZa.R_le n))
      (hZa.P_le_commutant_R n)
  -- the four limits, all finite
  have hX'Z : X' ≤ Z′ := hXX'.trans hXZ
  have hXZ' : X ≤ Z'′ := hXZ.trans (commutant_le hZZ')
  have hX'Z' : X' ≤ Z'′ := hX'Z.trans (commutant_le hZZ')
  have hf₁ : mutualInfo Ω X' Z ≠ ⊤ := ne_top_of_le_ne_top hfin (mutualInfo_mono hXX' le_rfl)
  have hf₂ : mutualInfo Ω X Z' ≠ ⊤ := ne_top_of_le_ne_top hfin (mutualInfo_mono le_rfl hZZ')
  have hf₄ : mutualInfo Ω X' Z' ≠ ⊤ := ne_top_of_le_ne_top hfin (mutualInfo_mono hXX' hZZ')
  have h₁ := tendsto_mutualInfo_of_monotone (Ω := Ω) (X := P) (Z := fun n => join (P' n) (R' n))
    hXa.P_mono hZa.join_mono hXa.P_gen hZa.join_gen hX'Z hf₁
  have h₂ := tendsto_mutualInfo_of_monotone (Ω := Ω) (X := fun n => join (P n) (R n)) (Z := P')
    hXa.join_mono hZa.P_mono hXa.join_gen hZa.P_gen hXZ' hf₂
  have h₃ := tendsto_mutualInfo_of_monotone (Ω := Ω) (X := fun n => join (P n) (R n))
    (Z := fun n => join (P' n) (R' n)) hXa.join_mono hZa.join_mono hXa.join_gen hZa.join_gen hXZ
    hfin
  have h₄ := tendsto_mutualInfo_of_monotone (Ω := Ω) (X := P) (Z := P') hXa.P_mono hZa.P_mono
    hXa.P_gen hZa.P_gen hX'Z' hf₄
  -- addition is continuous at pairs of finite values
  have hsum : ∀ {a b : ℕ → EReal} {A B : EReal}, Tendsto a atTop (𝓝 A) →
      Tendsto b atTop (𝓝 B) → A ≠ ⊤ → B ≠ ⊤ →
        Tendsto (fun n => a n + b n) atTop (𝓝 (A + B)) := fun ha hb hA hB =>
    (EReal.continuousAt_add (p := (_, _)) (Or.inl hA) (Or.inr hB)).tendsto.comp
      (ha.prodMk_nhds hb)
  exact le_of_tendsto_of_tendsto' (hsum h₁ h₂ hf₁ hf₂) (hsum h₃ h₄ hfin hf₄) hineq

/-- **Four-term inequality from matrix approximations.** Let `X' ≤ X`, `Z' ≤ Z` be approximated by
matrix subfactors (`IsMatrixApprox`), `X ≤ Z′` and `I(X:Z) < ∞`. Then
`I(X':Z) + I(X:Z') ≤ I(X:Z) + I(X':Z')`, for any vector `Ω`. -/
theorem mutualInfo_add_le_of_approx {Ω : H} {X X' Z Z' : VonNeumannAlgebra H}
    {P R P' R' : ℕ → VonNeumannAlgebra H}
    (hXa : IsMatrixApprox X' X P R) (hZa : IsMatrixApprox Z' Z P' R')
    (hXX' : X' ≤ X) (hZZ' : Z' ≤ Z) (hXZ : X ≤ Z′) (hfin : mutualInfo Ω X Z ≠ ⊤) :
    mutualInfo Ω X' Z + mutualInfo Ω X Z' ≤ mutualInfo Ω X Z + mutualInfo Ω X' Z' := by
  have hX'Z : X' ≤ Z′ := hXX'.trans hXZ
  have hXZ' : X ≤ Z'′ := hXZ.trans (commutant_le hZZ')
  have hX'Z' : X' ≤ Z'′ := hX'Z.trans (commutant_le hZZ')
  rcases eq_or_ne Ω 0 with rfl | hΩ0
  · rw [mutualInfo_zero_vector hX'Z, mutualInfo_zero_vector hXZ', mutualInfo_zero_vector hXZ,
      mutualInfo_zero_vector hX'Z']
  -- normalise: `Ω₁ = ‖Ω‖⁻¹ Ω`
  have hc : 0 < ‖Ω‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hΩ0)
  have hΩ₁ : ‖((‖Ω‖⁻¹ : ℝ) : ℂ) • Ω‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc.le, inv_mul_cancel₀ (norm_ne_zero_iff.2 hΩ0)]
  have hf₁ : mutualInfo Ω X' Z ≠ ⊤ := ne_top_of_le_ne_top hfin (mutualInfo_mono hXX' le_rfl)
  have hf₂ : mutualInfo Ω X Z' ≠ ⊤ := ne_top_of_le_ne_top hfin (mutualInfo_mono le_rfl hZZ')
  have hf₄ : mutualInfo Ω X' Z' ≠ ⊤ := ne_top_of_le_ne_top hfin (mutualInfo_mono hXX' hZZ')
  have hfin₁ : mutualInfo (((‖Ω‖⁻¹ : ℝ) : ℂ) • Ω) X Z ≠ ⊤ := by
    rw [mutualInfo_smul_eq hXZ hfin hc]
    exact EReal.coe_ne_top _
  have key := mutualInfo_add_le_of_approx_of_norm_eq_one hΩ₁ hXa hZa hXX' hZZ' hXZ hfin₁
  rw [mutualInfo_smul_eq hX'Z hf₁ hc, mutualInfo_smul_eq hXZ' hf₂ hc,
    mutualInfo_smul_eq hXZ hfin hc, mutualInfo_smul_eq hX'Z' hf₄ hc, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at key
  rw [mutualInfo_eq_coe_toReal hX'Z hf₁, mutualInfo_eq_coe_toReal hXZ' hf₂,
    mutualInfo_eq_coe_toReal hXZ hfin, mutualInfo_eq_coe_toReal hX'Z' hf₄, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hpos : 0 < (‖Ω‖⁻¹) ^ 2 := by positivity
  have key' : (‖Ω‖⁻¹) ^ 2 * ((mutualInfo Ω X' Z).toReal + (mutualInfo Ω X Z').toReal) ≤
      (‖Ω‖⁻¹) ^ 2 * ((mutualInfo Ω X Z).toReal + (mutualInfo Ω X' Z').toReal) := by
    linarith
  exact le_of_mul_le_mul_left key' hpos

/-- **Four-term inequality for type I factors.** For type I factors `X' ≤ X`, `Z' ≤ Z`
with `X ≤ Z′` and `I(X:Z) < ∞`,
`I(X':Z) + I(X:Z') ≤ I(X:Z) + I(X':Z')`. -/
theorem mutualInfo_add_le_of_isTypeIFactor [TopologicalSpace.SeparableSpace H] {Ω : H}
    {X X' Z Z' : VonNeumannAlgebra H}
    (hX : IsTypeIFactor X) (hX' : IsTypeIFactor X') (hZ : IsTypeIFactor Z)
    (hZ' : IsTypeIFactor Z') (hXX' : X' ≤ X) (hZZ' : Z' ≤ Z) (hXZ : X ≤ Z′)
    (hfin : mutualInfo Ω X Z ≠ ⊤) :
    mutualInfo Ω X' Z + mutualInfo Ω X Z' ≤ mutualInfo Ω X Z + mutualInfo Ω X' Z' := by
  obtain ⟨P, R, hPm, hRm, hPX', -, hRc, hPg, hJg, hPd, hRd⟩ :=
    exists_matrixSubfactor_seq_pair hX' hX hXX'
  obtain ⟨P', R', hP'm, hR'm, hP'Z', -, hR'c, hP'g, hJ'g, hP'd, hR'd⟩ :=
    exists_matrixSubfactor_seq_pair hZ' hZ hZZ'
  exact mutualInfo_add_le_of_approx ⟨hPm, hRm, hPX', hRc, hPg, hJg, hPd, hRd⟩
    ⟨hP'm, hR'm, hP'Z', hR'c, hP'g, hJ'g, hP'd, hR'd⟩ hXX' hZZ' hXZ hfin

end CTheorem
