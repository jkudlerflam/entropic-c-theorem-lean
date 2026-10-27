import ModularCTheorem.Araki.MutualInfo
import QuantumSystem.InformationTheory.Entropy.VonNeumann.StrongSubadditivity
import QuantumSystem.InformationTheory.Entropy.Umegaki.Monotonicity
import QuantumSystem.Analysis.VonNeumannAlgebra.DoubleCommutant.TFAE

/-!
# T6. Matrix subfactors: Araki = Umegaki, mutual information, four-term SSA

Compiled, no `sorry`.

A *unital matrix subfactor* of `B(H)` is a von Neumann algebra `F` together with a `⋆`-isomorphism
`Φ : F ≃⋆ₐ[ℂ] B(K)` for a finite-dimensional Hilbert space `K`. All statements take the
isomorphisms as data.

## Main results

* `arakiEntropy_eq_umegakiEntropy` — (a) on `F ≅ B(K)` Araki's relative entropy is Umegaki's
  entropy of the functionals transported to `B(K)` (DPI along `Φ⁻¹` and `Φ`, both normal).
* `joinEquiv` — (b) for commuting `F ≅ B(K₁)`, `G ≅ B(K₂)`, `F ∨ G ≅ B(K₁ ⊗ K₂)` with
  `a ⊗ b ↦ Φ₁⁻¹(a) Φ₂⁻¹(b)`. Injective because `B(K₁ ⊗ K₂)` is simple, onto `F ∨ G` because the
  finite-dimensional range is WOT-closed (bicommutant theorem).
* `mutualInfo_eq_mutualInformation` — (b) `I(F:G)` is the finite-dimensional mutual information of
  the transported vacuum state; `mutualInfo_eq_entropy` — `I(F:G) = S(F) + S(G) - S(F ∨ G)`.
* `mutualInfo_fourTerm` — (c) for pairwise commuting matrix subfactors `P, R, P', R'`, with
  `Q = P ∨ R`, `Q' = P' ∨ R'`: `I(P:Q') + I(Q:P') ≤ I(Q:Q') + I(P:P')`, from
  `vonNeumannEntropy_strong_subadditivity` with `A = R`, `B = P ∨ P'`, `C = R'`.
-/

open scoped InnerProductSpace InnerProduct VonNeumannAlgebra Araki QuantumInfo ComplexOrder
  TensorProduct
open VonNeumannAlgebra

namespace CTheorem

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Finite-dimensional von Neumann algebras: everything is normal -/

section FiniteDimensional

variable {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- The σ-weak copy of `M` is linearly isomorphic to `M`. -/
def sigmaWeakEquiv (M : VonNeumannAlgebra K') : M.sigmaWeak ≃ₗ[ℂ] M :=
  { M.ofSigmaWeak with
    invFun := M.toSigmaWeak
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

instance finiteDimensional_sigmaWeak (M : VonNeumannAlgebra K') [FiniteDimensional ℂ M] :
    FiniteDimensional ℂ M.sigmaWeak :=
  LinearEquiv.finiteDimensional (sigmaWeakEquiv M).symm

/-- Positive functionals on a finite-dimensional von Neumann algebra are normal (on any `K'`). -/
theorem isNormal_of_finiteDimensional' {M : VonNeumannAlgebra K'} [FiniteDimensional ℂ M]
    (ω : M →ₚ[ℂ] ℂ) : M.IsNormal ω :=
  LinearMap.continuous_of_finiteDimensional (ω.toLinearMap ∘ₗ M.ofSigmaWeak)

/-- Linear maps out of a finite-dimensional von Neumann algebra are normal (on any `K'`). -/
theorem isNormalMap_of_finiteDimensional' {M : VonNeumannAlgebra K'} [FiniteDimensional ℂ M]
    {N : VonNeumannAlgebra H} {F' : Type*} [FunLike F' M N] [LinearMapClass F' ℂ M N] (α : F') :
    IsNormalMap α := by
  let e : N →ₗ[ℂ] N.sigmaWeak :=
    { toFun := N.toSigmaWeak
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearMap.continuous_of_finiteDimensional (e ∘ₗ (LinearMap.ofClass α) ∘ₗ M.ofSigmaWeak)

lemma finiteDimensional_of_starAlgEquiv {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] {M : VonNeumannAlgebra K'}
    (Φ : M ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : FiniteDimensional ℂ M :=
  LinearEquiv.finiteDimensional Φ.symm.toAlgEquiv.toLinearEquiv

end FiniteDimensional

/-! ### Matrix subfactors and transport to `B(K)` -/

section Transport

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

variable (K) in
/-- The von Neumann algebra `𝓑(K)` as the operator algebra `K →L[ℂ] K`. -/
def bEquiv : 𝓑(K) ≃⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun x := (x : K →L[ℂ] K)
  invFun x := ⟨x, mem_boundedLinearOperators x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

variable {X : VonNeumannAlgebra H} (Φ : X ≃⋆ₐ[ℂ] (K →L[ℂ] K))

/-- `Φ⁻¹`, as a `⋆`-isomorphism `𝓑(K) ≃ X` of von Neumann algebras. -/
def matEquiv : 𝓑(K) ≃⋆ₐ[ℂ] X := (bEquiv K).trans Φ.symm

lemma isNormalMap_matEquiv :
    IsNormalMap (SchwarzMapClass.toSchwarzMap (matEquiv Φ) : SchwarzMap 𝓑(K) X) :=
  isNormalMap_of_finiteDimensional (SchwarzMapClass.toSchwarzMap (matEquiv Φ) : SchwarzMap 𝓑(K) X)

lemma isNormalMap_matEquiv_symm :
    IsNormalMap (SchwarzMapClass.toSchwarzMap (matEquiv Φ).symm : SchwarzMap X 𝓑(K)) := by
  have := finiteDimensional_of_starAlgEquiv Φ
  exact isNormalMap_of_finiteDimensional'
    (SchwarzMapClass.toSchwarzMap (matEquiv Φ).symm : SchwarzMap X 𝓑(K))

/-- A positive functional on `X` transported to `B(K)`: `a ↦ ψ(Φ⁻¹ a)`. -/
def transportFun (ψ : X →ₚ[ℂ] ℂ) : (K →L[ℂ] K) →ₚ[ℂ] ℂ :=
  ψ.comp (PositiveLinearMap.ofClass
    (SchwarzMapClass.toSchwarzMap Φ.symm : SchwarzMap (K →L[ℂ] K) X))

@[simp] lemma transportFun_apply (ψ : X →ₚ[ℂ] ℂ) (a : K →L[ℂ] K) :
    transportFun Φ ψ a = ψ (Φ.symm a) := rfl

/-- **(T6.a) Araki = Umegaki on a matrix subfactor.** For `Φ : X ≃ B(K)` and normal `ψ, φ` on `X`,
`S(ψ ‖ φ) = D(ψ ∘ Φ⁻¹ ‖ φ ∘ Φ⁻¹)`. -/
theorem arakiEntropy_eq_umegakiEntropy (ψ φ : X.NormalFunctional) :
    S⟦ψ ∥ φ⟧ = D(transportFun Φ ψ.1 ∥ transportFun Φ φ.1) := by
  have e : ∀ χ : X.NormalFunctional,
      (PositiveLinearMap.ofClass (transportFun Φ χ.1)).toNormalFunctional =
        χ.comp (SchwarzMapClass.toSchwarzMap (matEquiv Φ) : SchwarzMap 𝓑(K) X)
          (isNormalMap_matEquiv Φ) :=
    fun χ => Subtype.ext (PositiveLinearMap.ext fun _ => rfl)
  rw [umegakiEntropy_def, e ψ, e φ]
  exact (arakiEntropy_comp_starAlgEquiv (matEquiv Φ) (isNormalMap_matEquiv Φ)
    (isNormalMap_matEquiv_symm Φ) ψ φ).symm

end Transport

/-! ### The transported vacuum state and its entropy -/

section Vacuum

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
  {X : VonNeumannAlgebra H} {Ω : H}

lemma vectorFunctional_one (hΩ : ‖Ω‖ = 1) (M : VonNeumannAlgebra H) :
    M.vectorFunctional Ω 1 = 1 := by
  rw [vectorFunctional_apply, OneMemClass.coe_one, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K, hΩ]
  norm_num

/-- The vacuum state transported to `B(K)` through `Φ : X ≃ B(K)`, `a ↦ ⟪Ω, Φ⁻¹(a) Ω⟫`. -/
def vacState (hΩ : ‖Ω‖ = 1) (Φ : X ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : State (K →L[ℂ] K) :=
  State.ofPositiveLinearMap (transportFun Φ (X.vectorFunctional Ω)) (by
    rw [transportFun_apply, map_one]
    exact vectorFunctional_one hΩ X)

lemma vacState_apply (hΩ : ‖Ω‖ = 1) (Φ : X ≃⋆ₐ[ℂ] (K →L[ℂ] K)) (a : K →L[ℂ] K) :
    vacState hΩ Φ a = ⟪Ω, ((Φ.symm a : X) : H →L[ℂ] H) Ω⟫_ℂ := rfl

/-- The entropy of the vacuum on a matrix subfactor does not depend on the identification
`X ≃ B(K)` (invariance of the von Neumann entropy under `⋆`-isomorphisms). -/
lemma vonNeumannEntropy_vacState_eq (hΩ : ‖Ω‖ = 1) {K₂ : Type*} [NormedAddCommGroup K₂]
    [InnerProductSpace ℂ K₂] [FiniteDimensional ℂ K₂] (Φ₁ : X ≃⋆ₐ[ℂ] (K →L[ℂ] K))
    (Φ₂ : X ≃⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) : S(vacState hΩ Φ₂) = S(vacState hΩ Φ₁) := by
  have h : ∀ a, vacState hΩ Φ₂ a =
      (vacState hΩ Φ₁).comp (Φ₂.symm.trans Φ₁) (map_one (Φ₂.symm.trans Φ₁)) a := fun a => by
    change ⟪Ω, ((Φ₂.symm a : X) : H →L[ℂ] H) Ω⟫_ℂ =
      ⟪Ω, ((Φ₁.symm (Φ₁ (Φ₂.symm a)) : X) : H →L[ℂ] H) Ω⟫_ℂ
    rw [StarAlgEquiv.symm_apply_apply]
  rw [vonNeumannEntropy_congr h, State.vonNeumannEntropy_comp_starAlgEquiv]

/-- The same for two isomorphisms out of equal algebras. -/
lemma vonNeumannEntropy_vacState_congr (hΩ : ‖Ω‖ = 1) {Y : VonNeumannAlgebra H} (hXY : X = Y)
    {K₂ : Type*}
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [FiniteDimensional ℂ K₂]
    (Φ₁ : X ≃⋆ₐ[ℂ] (K →L[ℂ] K)) (Φ₂ : Y ≃⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) :
    S(vacState hΩ Φ₁) = S(vacState hΩ Φ₂) := by
  subst hXY
  exact (vonNeumannEntropy_vacState_eq hΩ Φ₁ Φ₂).symm

end Vacuum

/-! ### The join of two commuting matrix subfactors -/

section JoinEquiv

variable {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [FiniteDimensional ℂ K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [FiniteDimensional ℂ K₂]
  {F G : VonNeumannAlgebra H}

/-- `a ↦ Φ⁻¹ a` as a linear map into `B(H)`. -/
def leftLin {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (Φ : F ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : (K →L[ℂ] K) →ₗ[ℂ] (H →L[ℂ] H) :=
  (SMulMemClass.subtype F) ∘ₗ Φ.symm.toAlgEquiv.toLinearMap

variable (Φ₁ : F ≃⋆ₐ[ℂ] (K₁ →L[ℂ] K₁)) (Φ₂ : G ≃⋆ₐ[ℂ] (K₂ →L[ℂ] K₂))

/-- `a ⊗ b ↦ Φ₁⁻¹(a) Φ₂⁻¹(b)`, as a linear map on `B(K₁ ⊗ K₂) ≅ B(K₁) ⊗ B(K₂)`. -/
def joinLin : (K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) →ₗ[ℂ] (H →L[ℂ] H) :=
  TensorProduct.lift ((LinearMap.mul ℂ (H →L[ℂ] H)).compl₁₂ (leftLin Φ₁) (leftLin Φ₂)) ∘ₗ
    (TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂).symm.toLinearMap

lemma joinLin_mapL (a : K₁ →L[ℂ] K₁) (b : K₂ →L[ℂ] K₂) :
    joinLin Φ₁ Φ₂ (TensorProduct.mapL a b) =
      ((Φ₁.symm a : F) : H →L[ℂ] H) * ((Φ₂.symm b : G) : H →L[ℂ] H) := by
  have hs : (TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂).symm (TensorProduct.mapL a b) = a ⊗ₜ b :=
    (LinearEquiv.symm_apply_eq _).mpr (TensorProduct.mapLEquiv_tmul a b).symm
  simp only [joinLin, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hs,
    TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
  rfl

lemma joinLin_comm (hFG : F ≤ G′) (a : K₁ →L[ℂ] K₁) (b : K₂ →L[ℂ] K₂) :
    ((Φ₂.symm b : G) : H →L[ℂ] H) * ((Φ₁.symm a : F) : H →L[ℂ] H) =
      ((Φ₁.symm a : F) : H →L[ℂ] H) * ((Φ₂.symm b : G) : H →L[ℂ] H) :=
  mem_commutant_iff.mp (hFG (Φ₁.symm a).2) _ (Φ₂.symm b).2

lemma joinLin_mul (hFG : F ≤ G′) (X Y : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) :
    joinLin Φ₁ Φ₂ (X * Y) = joinLin Φ₁ Φ₂ X * joinLin Φ₁ Φ₂ Y := by
  have hgen : ∀ (a a' : K₁ →L[ℂ] K₁) (b b' : K₂ →L[ℂ] K₂),
      joinLin Φ₁ Φ₂ (TensorProduct.mapL a b * TensorProduct.mapL a' b') =
        joinLin Φ₁ Φ₂ (TensorProduct.mapL a b) * joinLin Φ₁ Φ₂ (TensorProduct.mapL a' b') := by
    intro a a' b b'
    have hc := joinLin_comm Φ₁ Φ₂ hFG a' b
    rw [← TensorProduct.mapL_mul, joinLin_mapL, joinLin_mapL, joinLin_mapL, map_mul, map_mul,
      MulMemClass.coe_mul, MulMemClass.coe_mul]
    set A := ((Φ₁.symm a : F) : H →L[ℂ] H)
    set A' := ((Φ₁.symm a' : F) : H →L[ℂ] H)
    set B := ((Φ₂.symm b : G) : H →L[ℂ] H)
    set B' := ((Φ₂.symm b' : G) : H →L[ℂ] H)
    calc A * A' * (B * B') = A * (A' * B) * B' := by simp only [mul_assoc]
      _ = A * (B * A') * B' := by rw [hc]
      _ = A * B * (A' * B') := by simp only [mul_assoc]
  have h1 : ∀ (a' : K₁ →L[ℂ] K₁) (b' : K₂ →L[ℂ] K₂) (X : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂),
      joinLin Φ₁ Φ₂ (X * TensorProduct.mapL a' b') =
        joinLin Φ₁ Φ₂ X * joinLin Φ₁ Φ₂ (TensorProduct.mapL a' b') := by
    intro a' b' X
    have h := TensorProduct.ext_mapL
      (u := joinLin Φ₁ Φ₂ ∘ₗ LinearMap.mulRight ℂ (TensorProduct.mapL a' b'))
      (v := LinearMap.mulRight ℂ (joinLin Φ₁ Φ₂ (TensorProduct.mapL a' b')) ∘ₗ joinLin Φ₁ Φ₂)
      (fun a b => hgen a a' b b')
    exact LinearMap.congr_fun h X
  have h := TensorProduct.ext_mapL (u := joinLin Φ₁ Φ₂ ∘ₗ LinearMap.mulLeft ℂ X)
    (v := LinearMap.mulLeft ℂ (joinLin Φ₁ Φ₂ X) ∘ₗ joinLin Φ₁ Φ₂) (fun a' b' => h1 a' b' X)
  exact LinearMap.congr_fun h Y

lemma joinLin_one : joinLin Φ₁ Φ₂ 1 = 1 := by
  have h1 : (1 : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) = TensorProduct.mapL 1 1 := by
    rw [ContinuousLinearMap.one_def, ContinuousLinearMap.one_def, ContinuousLinearMap.one_def,
      TensorProduct.mapL_id_id]
  rw [h1, joinLin_mapL, map_one, map_one, OneMemClass.coe_one, OneMemClass.coe_one, one_mul]

lemma star_mapL (a : K₁ →L[ℂ] K₁) (b : K₂ →L[ℂ] K₂) :
    star (TensorProduct.mapL a b) = TensorProduct.mapL (star a) (star b) := by
  rw [ContinuousLinearMap.star_eq_adjoint, TensorProduct.adjoint_mapL,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint]

lemma joinLin_star (hFG : F ≤ G′) (X : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) :
    joinLin Φ₁ Φ₂ (star X) = star (joinLin Φ₁ Φ₂ X) := by
  obtain ⟨z, rfl⟩ := (TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂).surjective X
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    have hc : star ((Φ₂.symm b : G) : H →L[ℂ] H) * star ((Φ₁.symm a : F) : H →L[ℂ] H) =
        star ((Φ₁.symm a : F) : H →L[ℂ] H) * star ((Φ₂.symm b : G) : H →L[ℂ] H) :=
      mem_commutant_iff.mp (hFG (star_mem (Φ₁.symm a).2)) _ (star_mem (Φ₂.symm b).2)
    rw [TensorProduct.mapLEquiv_tmul, star_mapL, joinLin_mapL, joinLin_mapL, map_star, map_star,
      StarMemClass.coe_star, StarMemClass.coe_star, star_mul, hc]
  | add z z' hz hz' =>
    have e : star ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) (z + z')) =
        star ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) z) +
          star ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) z') := by
      rw [map_add]
      exact star_add _ _
    calc joinLin Φ₁ Φ₂ (star ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) (z + z')))
        = joinLin Φ₁ Φ₂ (star ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) z)) +
            joinLin Φ₁ Φ₂ (star ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) z')) := by
          rw [e, map_add]
      _ = star (joinLin Φ₁ Φ₂ ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) z)) +
            star (joinLin Φ₁ Φ₂ ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) z')) := by
          rw [hz, hz']
      _ = star (joinLin Φ₁ Φ₂ ((TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂) (z + z'))) := by
          rw [map_add, map_add, star_add]

lemma joinLin_mem (X : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) : joinLin Φ₁ Φ₂ X ∈ join F G := by
  obtain ⟨z, rfl⟩ := (TensorProduct.mapLEquiv ℂ K₁ K₁ K₂ K₂).surjective X
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.mapLEquiv_tmul, joinLin_mapL]
    exact mul_mem (le_join_left F G (Φ₁.symm a).2) (le_join_right F G (Φ₂.symm b).2)
  | add z z' hz hz' =>
    rw [map_add, map_add]
    exact add_mem hz hz'


/-- The range of `joinLin`, a unital `⋆`-subalgebra of `B(H)`. -/
def rangeAlg (hFG : F ≤ G′) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  { (LinearMap.range (joinLin Φ₁ Φ₂)).toSubalgebra
      (LinearMap.mem_range.mpr ⟨1, joinLin_one Φ₁ Φ₂⟩)
      (fun _ _ hx hy => by
        obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp hx
        obtain ⟨Y, rfl⟩ := LinearMap.mem_range.mp hy
        exact LinearMap.mem_range.mpr ⟨X * Y, joinLin_mul Φ₁ Φ₂ hFG X Y⟩) with
    star_mem' := fun {a} ha => by
      obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp ha
      exact LinearMap.mem_range.mpr ⟨star X, joinLin_star Φ₁ Φ₂ hFG X⟩ }

lemma coe_rangeAlg (hFG : F ≤ G′) :
    (rangeAlg Φ₁ Φ₂ hFG : Set (H →L[ℂ] H)) = (LinearMap.range (joinLin Φ₁ Φ₂) : Set (H →L[ℂ] H)) :=
  rfl

/-- **Injectivity** (`B(K₁ ⊗ K₂)` is simple): if `joinLin X = 0` with `X v ≠ 0`, then
`1 = Σᵢ c⁻¹ |bᵢ⟩⟨Xv| X |v⟩⟨bᵢ|` (`c = ‖Xv‖²`) gives `1 = 0` in `B(H)`, so `F = 0`, `K₁ = 0`, and
`K₁ ⊗ K₂ = 0`, contradicting `X v ≠ 0`. -/
lemma joinLin_injective (hFG : F ≤ G′) : Function.Injective (joinLin Φ₁ Φ₂) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, X v ≠ 0 := by
    by_contra! h
    exact hne (ContinuousLinearMap.ext h)
  set c : ℂ := ⟪X v, X v⟫_ℂ with hc
  have hc0 : c ≠ 0 := inner_self_ne_zero.mpr hv
  let b := stdOrthonormalBasis ℂ (K₁ ⊗[ℂ] K₂)
  have hterm : ∀ (i : Fin (Module.finrank ℂ (K₁ ⊗[ℂ] K₂))) (w : K₁ ⊗[ℂ] K₂),
      (c⁻¹ • (InnerProductSpace.rankOne ℂ (b i) (X v) * X *
        InnerProductSpace.rankOne ℂ v (b i))) w = ⟪b i, w⟫_ℂ • b i := by
    intro i w
    simp only [smul_apply, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul, smul_smul]
    congr 1
    rw [← hc]
    field_simp
  have hone : (1 : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) =
      ∑ i, c⁻¹ • (InnerProductSpace.rankOne ℂ (b i) (X v) * X *
        InnerProductSpace.rankOne ℂ v (b i)) :=
    ContinuousLinearMap.ext fun w => by
      simp only [sum_apply, hterm, b.sum_repr', one_apply_eq_self]
  have h1 : joinLin Φ₁ Φ₂ 1 = 0 := by
    rw [hone, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, joinLin_mul Φ₁ Φ₂ hFG, joinLin_mul Φ₁ Φ₂ hFG, hX, mul_zero, zero_mul, smul_zero]
  rw [joinLin_one] at h1
  have hF : (1 : F) = 0 :=
    Subtype.ext (by rw [OneMemClass.coe_one, ZeroMemClass.coe_zero]; exact h1)
  have hK : (1 : K₁ →L[ℂ] K₁) = 0 := by rw [← map_one Φ₁, hF, map_zero]
  have hK₁ : ∀ k : K₁, k = 0 := fun k => by
    simpa using congrArg (fun T : K₁ →L[ℂ] K₁ => T k) hK
  have hall : ∀ w : K₁ ⊗[ℂ] K₂, w = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul k k' => rw [hK₁ k, TensorProduct.zero_tmul]
    | add p q hp hq => rw [hp, hq, add_zero]
  exact hv (hall _)


/-- **Surjectivity onto `F ∨ G`**: the range is a finite-dimensional, hence WOT-closed, unital
`⋆`-algebra containing `F ∪ G`, so it is its own bicommutant and contains `F ∨ G`. -/
lemma exists_joinLin_eq (hFG : F ≤ G′) {y : H →L[ℂ] H} (hy : y ∈ join F G) :
    ∃ X, joinLin Φ₁ Φ₂ X = y := by
  have hWOT : WeakOperatorTopology.IsWOTClosed (H := H)
      (rangeAlg Φ₁ Φ₂ hFG : Set (H →L[ℂ] H)) := by
    have : FiniteDimensional ℂ (WeakOperatorTopology.submoduleToWOT (H := H)
        (LinearMap.range (joinLin Φ₁ Φ₂))) := by
      unfold WeakOperatorTopology.submoduleToWOT
      rw [Submodule.comap_equiv_eq_map_symm]
      infer_instance
    rw [coe_rangeAlg]
    unfold WeakOperatorTopology.IsWOTClosed
    rw [← WeakOperatorTopology.coe_submoduleToWOT]
    exact Submodule.closed_of_finiteDimensional _
  have hsub : (F : Set (H →L[ℂ] H)) ∪ G ⊆ (rangeAlg Φ₁ Φ₂ hFG : Set (H →L[ℂ] H)) := by
    rw [coe_rangeAlg]
    rintro w (hw | hw)
    · refine LinearMap.mem_range.mpr ⟨TensorProduct.mapL (Φ₁ ⟨w, hw⟩) 1, ?_⟩
      rw [joinLin_mapL, StarAlgEquiv.symm_apply_apply, map_one, OneMemClass.coe_one, mul_one]
    · refine LinearMap.mem_range.mpr ⟨TensorProduct.mapL 1 (Φ₂ ⟨w, hw⟩), ?_⟩
      rw [joinLin_mapL, StarAlgEquiv.symm_apply_apply, map_one, OneMemClass.coe_one, one_mul]
  have hy' : y ∈ (generated (rangeAlg Φ₁ Φ₂ hFG : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) :=
    generated_mono hsub hy
  rw [generated_coe_of_isWOTClosed _ hWOT, coe_rangeAlg] at hy'
  exact LinearMap.mem_range.mp hy'

/-- The inverse of `joinEquiv`: `B(K₁ ⊗ K₂) ≃⋆ₐ F ∨ G`, `X ↦ joinLin X`. -/
def joinEquivSymm (hFG : F ≤ G′) : (K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) ≃⋆ₐ[ℂ] join F G where
  toFun X := ⟨joinLin Φ₁ Φ₂ X, joinLin_mem Φ₁ Φ₂ X⟩
  invFun y := (exists_joinLin_eq Φ₁ Φ₂ hFG y.2).choose
  left_inv X := joinLin_injective Φ₁ Φ₂ hFG
    (exists_joinLin_eq Φ₁ Φ₂ hFG (joinLin_mem Φ₁ Φ₂ X)).choose_spec
  right_inv y := Subtype.ext (exists_joinLin_eq Φ₁ Φ₂ hFG y.2).choose_spec
  map_mul' X Y := Subtype.ext (joinLin_mul Φ₁ Φ₂ hFG X Y)
  map_add' X Y := Subtype.ext (map_add (joinLin Φ₁ Φ₂) X Y)
  map_smul' c X := Subtype.ext (map_smul (joinLin Φ₁ Φ₂) c X)
  map_star' X := Subtype.ext (joinLin_star Φ₁ Φ₂ hFG X)

/-- **(T6.b) Two commuting matrix subfactors generate `B(K₁ ⊗ K₂)`**:
`F ∨ G ≃⋆ₐ B(K₁ ⊗ K₂)`, inverse `a ⊗ b ↦ Φ₁⁻¹(a) Φ₂⁻¹(b)`. -/
def joinEquiv (hFG : F ≤ G′) : join F G ≃⋆ₐ[ℂ] (K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) :=
  (joinEquivSymm Φ₁ Φ₂ hFG).symm

lemma coe_joinEquiv_symm_apply (hFG : F ≤ G′) (X : K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂) :
    (((joinEquiv Φ₁ Φ₂ hFG).symm X : join F G) : H →L[ℂ] H) = joinLin Φ₁ Φ₂ X := by
  rw [joinEquiv, StarAlgEquiv.symm_symm]
  rfl


lemma coe_joinEquiv_symm_mapL (hFG : F ≤ G′) (a : K₁ →L[ℂ] K₁) (b : K₂ →L[ℂ] K₂) :
    (((joinEquiv Φ₁ Φ₂ hFG).symm (TensorProduct.mapL a b) : join F G) : H →L[ℂ] H) =
      ((Φ₁.symm a : F) : H →L[ℂ] H) * ((Φ₂.symm b : G) : H →L[ℂ] H) := by
  rw [coe_joinEquiv_symm_apply, joinLin_mapL]

lemma joinEquiv_left (hFG : F ≤ G′) (f : H →L[ℂ] H) (hf : f ∈ F) :
    joinEquiv Φ₁ Φ₂ hFG ⟨f, le_join_left F G hf⟩ = TensorProduct.mapL (Φ₁ ⟨f, hf⟩) 1 := by
  rw [← (joinEquiv Φ₁ Φ₂ hFG).apply_symm_apply (TensorProduct.mapL (Φ₁ ⟨f, hf⟩) 1)]
  congr 1
  apply Subtype.ext
  rw [coe_joinEquiv_symm_mapL, StarAlgEquiv.symm_apply_apply, map_one, OneMemClass.coe_one,
    mul_one]

lemma joinEquiv_right (hFG : F ≤ G′) (g : H →L[ℂ] H) (hg : g ∈ G) :
    joinEquiv Φ₁ Φ₂ hFG ⟨g, le_join_right F G hg⟩ = TensorProduct.mapL 1 (Φ₂ ⟨g, hg⟩) := by
  rw [← (joinEquiv Φ₁ Φ₂ hFG).apply_symm_apply (TensorProduct.mapL 1 (Φ₂ ⟨g, hg⟩))]
  congr 1
  apply Subtype.ext
  rw [coe_joinEquiv_symm_mapL, StarAlgEquiv.symm_apply_apply, map_one, OneMemClass.coe_one,
    one_mul]

end JoinEquiv

/-! ### Mutual information of commuting matrix subfactors -/

section MutualInformation

variable {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [FiniteDimensional ℂ K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [FiniteDimensional ℂ K₂]
  {F G : VonNeumannAlgebra H} {Ω : H} (hΩ : ‖Ω‖ = 1)
  (Φ₁ : F ≃⋆ₐ[ℂ] (K₁ →L[ℂ] K₁)) (Φ₂ : G ≃⋆ₐ[ℂ] (K₂ →L[ℂ] K₂)) (hFG : F ≤ G′)

omit [FiniteDimensional ℂ K₁] [FiniteDimensional ℂ K₂] in
lemma rTensor_eq_mapL (a : K₁ →L[ℂ] K₁) : a.rTensor K₂ = TensorProduct.mapL a 1 :=
  ContinuousLinearMap.coe_inj.mp <| TensorProduct.ext' fun _ _ => rfl

omit [FiniteDimensional ℂ K₁] [FiniteDimensional ℂ K₂] in
lemma lTensor_eq_mapL (b : K₂ →L[ℂ] K₂) : b.lTensor K₁ = TensorProduct.mapL 1 b :=
  ContinuousLinearMap.coe_inj.mp <| TensorProduct.ext' fun _ _ => rfl

lemma vacState_joinEquiv_mapL (a : K₁ →L[ℂ] K₁) (b : K₂ →L[ℂ] K₂) :
    vacState hΩ (joinEquiv Φ₁ Φ₂ hFG) (TensorProduct.mapL a b) =
      ⟪Ω, (((Φ₁.symm a : F) : H →L[ℂ] H) * ((Φ₂.symm b : G) : H →L[ℂ] H)) Ω⟫_ℂ := by
  rw [vacState_apply, coe_joinEquiv_symm_mapL]

/-- The first marginal of the transported vacuum is the vacuum transported to `F`. -/
lemma vacState_traceRight (a : K₁ →L[ℂ] K₁) :
    (vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).traceRight a = vacState hΩ Φ₁ a := by
  rw [State.traceRight_apply, rTensor_eq_mapL, vacState_joinEquiv_mapL, map_one,
    OneMemClass.coe_one, mul_one, vacState_apply]

/-- The second marginal of the transported vacuum is the vacuum transported to `G`. -/
lemma vacState_traceLeft (b : K₂ →L[ℂ] K₂) :
    (vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).traceLeft b = vacState hΩ Φ₂ b := by
  rw [State.traceLeft_apply, lTensor_eq_mapL, vacState_joinEquiv_mapL, map_one,
    OneMemClass.coe_one, one_mul, vacState_apply]

/-- The product functional on `F ∨ G`: `y ↦ (ω_F ⊗ ω_G)(Ψ y)` for `Ψ = joinEquiv`. -/
def prodFunctional : (join F G).NormalFunctional :=
  haveI := finiteDimensional_of_starAlgEquiv (joinEquiv Φ₁ Φ₂ hFG)
  ⟨(PositiveLinearMap.ofClass ((vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).traceRight.tensorProduct
      (vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).traceLeft)).comp
    (PositiveLinearMap.ofClass (SchwarzMapClass.toSchwarzMap (joinEquiv Φ₁ Φ₂ hFG) :
      SchwarzMap (join F G) (K₁ ⊗[ℂ] K₂ →L[ℂ] K₁ ⊗[ℂ] K₂))),
    isNormal_of_finiteDimensional' _⟩

lemma prodFunctional_apply (y : join F G) :
    (prodFunctional hΩ Φ₁ Φ₂ hFG).1 y =
      ((vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).traceRight.tensorProduct
        (vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).traceLeft) (joinEquiv Φ₁ Φ₂ hFG y) := rfl

lemma isProduct_prodFunctional : IsProduct Ω F G (prodFunctional hΩ Φ₁ Φ₂ hFG) := by
  intro f hf g hg
  have e1 : (⟨f * g, mul_mem (le_join_left F G hf) (le_join_right F G hg)⟩ : join F G) =
      ⟨f, le_join_left F G hf⟩ * ⟨g, le_join_right F G hg⟩ := rfl
  rw [prodFunctional_apply, e1, map_mul, joinEquiv_left Φ₁ Φ₂ hFG f hf,
    joinEquiv_right Φ₁ Φ₂ hFG g hg, ← TensorProduct.mapL_mul, mul_one, one_mul,
    State.tensorProduct_mapL, vacState_traceRight, vacState_traceLeft, vacState_apply,
    vacState_apply, StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]

/-- **(T6.b) Mutual information of commuting matrix subfactors** is the finite-dimensional mutual
information of the vacuum transported to `B(K₁ ⊗ K₂)`. -/
theorem mutualInfo_eq_mutualInformation :
    mutualInfo Ω F G = ((vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)).mutualInformation : EReal) := by
  rw [mutualInfo_eq_arakiEntropy hFG (isProduct_prodFunctional hΩ Φ₁ Φ₂ hFG),
    arakiEntropy_eq_umegakiEntropy (joinEquiv Φ₁ Φ₂ hFG),
    ← State.umegakiEntropy_eq_mutualInformation]
  refine umegakiEntropy_congr _ _ (fun _ => rfl) (fun A => ?_)
  rw [transportFun_apply, prodFunctional_apply, StarAlgEquiv.apply_symm_apply]

/-- `I(F:G) = S(F) + S(G) - S(F ∨ G)`, with the entropies of the transported vacuum states. -/
theorem mutualInfo_eq_entropy :
    mutualInfo Ω F G = ((S(vacState hΩ Φ₁) + S(vacState hΩ Φ₂) -
      S(vacState hΩ (joinEquiv Φ₁ Φ₂ hFG)) : ℝ) : EReal) := by
  rw [mutualInfo_eq_mutualInformation hΩ Φ₁ Φ₂ hFG, State.mutualInformation,
    vonNeumannEntropy_congr (vacState_traceRight hΩ Φ₁ Φ₂ hFG),
    vonNeumannEntropy_congr (vacState_traceLeft hΩ Φ₁ Φ₂ hFG)]

end MutualInformation

/-! ### Four-term strong subadditivity -/

section SSA

variable {Ω : H} (hΩ : ‖Ω‖ = 1)

lemma join_swap3 (P R P' : VonNeumannAlgebra H) : join (join P R) P' = join R (join P P') :=
  le_antisymm
    (join_le (join_le (le_join_of_le_right (le_join_left P P')) (le_join_left R _))
      (le_join_of_le_right (le_join_right P P')))
    (join_le (le_join_of_le_left (le_join_right P R))
      (join_le (le_join_of_le_left (le_join_left P R)) (le_join_right _ P')))

lemma join_four (P R P' R' : VonNeumannAlgebra H) :
    join (join P R) (join P' R') = join (join R (join P P')) R' :=
  le_antisymm
    (join_le
      (join_le (le_join_of_le_left (le_join_of_le_right (le_join_left P P')))
        (le_join_of_le_left (le_join_left R _)))
      (join_le (le_join_of_le_left (le_join_of_le_right (le_join_right P P')))
        (le_join_right _ R')))
    (join_le
      (join_le (le_join_of_le_left (le_join_right P R))
        (join_le (le_join_of_le_left (le_join_left P R))
          (le_join_of_le_right (le_join_left P' R'))))
      (le_join_of_le_right (le_join_right P' R')))

variable {KA KB KC : Type*}
  [NormedAddCommGroup KA] [InnerProductSpace ℂ KA] [FiniteDimensional ℂ KA]
  [NormedAddCommGroup KB] [InnerProductSpace ℂ KB] [FiniteDimensional ℂ KB]
  [NormedAddCommGroup KC] [InnerProductSpace ℂ KC] [FiniteDimensional ℂ KC]
  {A B C : VonNeumannAlgebra H}

set_option maxSynthPendingDepth 2 in
/-- **Strong subadditivity for three commuting matrix subfactors**:
`S(ABC) + S(B) ≤ S(AB) + S(BC)` for the transported vacuum states, from the library's
`vonNeumannEntropy_strong_subadditivity` on `B((K_A ⊗ K_B) ⊗ K_C)`. -/
theorem ssa_core (ΦA : A ≃⋆ₐ[ℂ] (KA →L[ℂ] KA)) (ΦB : B ≃⋆ₐ[ℂ] (KB →L[ℂ] KB))
    (ΦC : C ≃⋆ₐ[ℂ] (KC →L[ℂ] KC)) (hAB : A ≤ B′) (hABC : join A B ≤ C′) (hBC : B ≤ C′) :
    S(vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)) + S(vacState hΩ ΦB) ≤
      S(vacState hΩ (joinEquiv ΦA ΦB hAB)) + S(vacState hΩ (joinEquiv ΦB ΦC hBC)) := by
  have hssa := State.vonNeumannEntropy_strong_subadditivity
    (vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC))
  have h1 : S((vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)).traceRight) =
      S(vacState hΩ (joinEquiv ΦA ΦB hAB)) :=
    vonNeumannEntropy_congr (vacState_traceRight hΩ (joinEquiv ΦA ΦB hAB) ΦC hABC)
  have h2 : S((vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)).traceRight.traceLeft) =
      S(vacState hΩ ΦB) := vonNeumannEntropy_congr fun Y => by
    rw [State.traceLeft_apply, vacState_traceRight, ← State.traceLeft_apply, vacState_traceLeft]
  have h3 : S((vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)).traceFirst) =
      S(vacState hΩ (joinEquiv ΦB ΦC hBC)) := by
    refine vonNeumannEntropy_congr fun W => ?_
    have h := TensorProduct.ext_mapL
      (u := (PositiveLinearMap.ofClass
        (vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)).traceFirst).toLinearMap)
      (v := (PositiveLinearMap.ofClass (vacState hΩ (joinEquiv ΦB ΦC hBC))).toLinearMap)
      fun Y Z => by
        change (vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)).traceFirst
            (TensorProduct.mapL Y Z) = vacState hΩ (joinEquiv ΦB ΦC hBC) (TensorProduct.mapL Y Z)
        have lhs : (vacState hΩ (joinEquiv (joinEquiv ΦA ΦB hAB) ΦC hABC)).traceFirst
            (TensorProduct.mapL Y Z) =
            ⟪Ω, (((ΦB.symm Y : B) : H →L[ℂ] H) * ((ΦC.symm Z : C) : H →L[ℂ] H)) Ω⟫_ℂ := by
          rw [State.traceFirst_apply, CompletelyPositiveMap.lTensorTensor_mapL,
            vacState_joinEquiv_mapL, lTensor_eq_mapL, coe_joinEquiv_symm_mapL, map_one,
            OneMemClass.coe_one, one_mul]
        rw [lhs, vacState_joinEquiv_mapL]
    exact LinearMap.congr_fun h W
  rw [h1, h2, h3] at hssa
  exact hssa

variable {KP KR KP' KR' : Type*}
  [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [FiniteDimensional ℂ KP]
  [NormedAddCommGroup KR] [InnerProductSpace ℂ KR] [FiniteDimensional ℂ KR]
  [NormedAddCommGroup KP'] [InnerProductSpace ℂ KP'] [FiniteDimensional ℂ KP']
  [NormedAddCommGroup KR'] [InnerProductSpace ℂ KR'] [FiniteDimensional ℂ KR']
  {P R P' R' : VonNeumannAlgebra H}

include hΩ in
set_option maxSynthPendingDepth 3 in
/-- **(T6.c) Four-term SSA for nested matrix subfactors.** For pairwise commuting matrix subfactors
`P, R, P', R'` and `Q = P ∨ R ≅ P ⊗ R`, `Q' = P' ∨ R' ≅ P' ⊗ R'`,
`I(P:Q') + I(Q:P') ≤ I(Q:Q') + I(P:P')`. All four terms are finite. The difference is
`S(AB) + S(BC) - S(ABC) - S(B)` with `A = R`, `B = P ∨ P'`, `C = R'`. -/
theorem mutualInfo_fourTerm (ΦP : P ≃⋆ₐ[ℂ] (KP →L[ℂ] KP)) (ΦR : R ≃⋆ₐ[ℂ] (KR →L[ℂ] KR))
    (ΦP' : P' ≃⋆ₐ[ℂ] (KP' →L[ℂ] KP')) (ΦR' : R' ≃⋆ₐ[ℂ] (KR' →L[ℂ] KR'))
    (hPR : P ≤ R′) (hPP' : P ≤ P'′) (hPR' : P ≤ R'′) (hRP' : R ≤ P'′) (hRR' : R ≤ R'′)
    (hP'R' : P' ≤ R'′) :
    mutualInfo Ω P (join P' R') + mutualInfo Ω (join P R) P' ≤
      mutualInfo Ω (join P R) (join P' R') + mutualInfo Ω P P' := by
  have hPQ' : P ≤ (join P' R')′ := le_commutant_join hPP' hPR'
  have hQP' : join P R ≤ P'′ := join_le hPP' hRP'
  have hQQ' : join P R ≤ (join P' R')′ := join_le hPQ' (le_commutant_join hRP' hRR')
  have hRB : R ≤ (join P P')′ := le_commutant_join (le_commutant_comm hPR) hRP'
  have hBC : join P P' ≤ R'′ := join_le hPR' hP'R'
  have hABC : join R (join P P') ≤ R'′ := join_le hRR' hBC
  rw [mutualInfo_eq_entropy hΩ ΦP (joinEquiv ΦP' ΦR' hP'R') hPQ',
    mutualInfo_eq_entropy hΩ (joinEquiv ΦP ΦR hPR) ΦP' hQP',
    mutualInfo_eq_entropy hΩ (joinEquiv ΦP ΦR hPR) (joinEquiv ΦP' ΦR' hP'R') hQQ',
    mutualInfo_eq_entropy hΩ ΦP ΦP' hPP']
  have e1 : S(vacState hΩ (joinEquiv (joinEquiv ΦP ΦR hPR) (joinEquiv ΦP' ΦR' hP'R') hQQ')) =
      S(vacState hΩ (joinEquiv (joinEquiv ΦR (joinEquiv ΦP ΦP' hPP') hRB) ΦR' hABC)) :=
    vonNeumannEntropy_vacState_congr hΩ (join_four P R P' R') _ _
  have e2 : S(vacState hΩ (joinEquiv ΦP (joinEquiv ΦP' ΦR' hP'R') hPQ')) =
      S(vacState hΩ (joinEquiv (joinEquiv ΦP ΦP' hPP') ΦR' hBC)) :=
    vonNeumannEntropy_vacState_congr hΩ (join_assoc P P' R').symm _ _
  have e3 : S(vacState hΩ (joinEquiv (joinEquiv ΦP ΦR hPR) ΦP' hQP')) =
      S(vacState hΩ (joinEquiv ΦR (joinEquiv ΦP ΦP' hPP') hRB)) :=
    vonNeumannEntropy_vacState_congr hΩ (join_swap3 P R P') _ _
  have hssa := ssa_core hΩ ΦR (joinEquiv ΦP ΦP' hPP') ΦR' hRB hABC hBC
  rw [e1, e2, e3, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

end SSA

end

end CTheorem
