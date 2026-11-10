module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomTwist
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DiscreteInternalHom
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeDual
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypePermutation
public import StacksFrontier.Algebra.Module.CharacterModule.CyclicHomPairing

/-!
# The dual of the twist `Hom(A, M)` is `Hom(M, A)`

Let `R` be a ring, `Γ` a topological group, `A` a finite cyclic group of order `n` with a
continuous action of `Γ`, and `M` a finite `R`-module with a continuous action of `Γ` killed by
`n`. Then the character dual of the twist `Hom_ℤ(A, M)` (`Stacks.GroupCohomology.homTwistObj`) is
`Hom_ℤ(M, A)` with the conjugation action and the `Rᵐᵒᵖ`-module structure through `M`
(`Stacks.GroupCohomology.homDualObj`), by the composition pairing
`Hom(A, M) × Hom(M, A) → End(A) = ℤ/n ⊂ ℚ/ℤ` of `Stacks.CharacterModule.cyclicHomPairing`,
naturally in `M` and without any choice. For `A = μ_n` this is
`M(-1)^∨ = Hom(M, μ_n)`.

## Main definitions

* `Stacks.GroupCohomology.homDualObj`, `Stacks.GroupCohomology.homDualFunctor`:
  `M ↦ Hom_ℤ(M, A)`, contravariant, valued in finite `Rᵐᵒᵖ`-modules with a continuous action.
* `Stacks.GroupCohomology.homTwistDualIso`: `Hom_ℤ(A, M)^∨ ≅ Hom_ℤ(M, A)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.ContinuousCohomology.InternalHomAction CharacterModule.MulOppositeAction

universe u v w w'

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology (continuousModuleRho_mul_apply continuousModuleRho_one_apply)

open scoped Stacks.DiscreteModuleTopology

variable (R : Type u) [Ring R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
  (A : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Γ)

/-- Conjugation by `γ` on `Hom_ℤ(M, A)`: `ψ ↦ γ ∘ ψ ∘ γ⁻¹`. -/
def homDualConj (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (γ : Γ) :
    (M.obj.obj.V →+ A.obj.obj.V) →ₗ[Rᵐᵒᵖ] (M.obj.obj.V →+ A.obj.obj.V) where
  toFun ψ := (A.obj.obj.ρ γ).asHom.hom.toAddMonoidHom.comp
    (ψ.comp (M.obj.obj.ρ γ⁻¹).asHom.hom.toAddMonoidHom)
  map_add' ψ ψ' := AddMonoidHom.ext fun m ↦ map_add (A.obj.obj.ρ γ).asHom.hom _ _
  map_smul' r ψ := AddMonoidHom.ext fun m ↦ by
    change (A.obj.obj.ρ γ).asHom.hom (ψ (r.unop • (M.obj.obj.ρ γ⁻¹).asHom.hom m)) =
      (A.obj.obj.ρ γ).asHom.hom (ψ ((M.obj.obj.ρ γ⁻¹).asHom.hom (r.unop • m)))
    rw [(M.obj.obj.ρ γ⁻¹).asHom.hom.map_smul]

/-- **The conjugation action of `Γ` on `Hom_ℤ(M, A)`.** -/
def homDualRepresentation (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    Representation Rᵐᵒᵖ Γ (M.obj.obj.V →+ A.obj.obj.V) where
  toFun γ := homDualConj R A M γ
  map_one' := LinearMap.ext fun ψ ↦ AddMonoidHom.ext fun m ↦ by
    change (A.obj.obj.ρ 1).asHom.hom (ψ ((M.obj.obj.ρ 1⁻¹).asHom.hom m)) = ψ m
    rw [inv_one, continuousModuleRho_one_apply ℤ A, continuousModuleRho_one_apply R M]
  map_mul' g h := LinearMap.ext fun ψ ↦ AddMonoidHom.ext fun m ↦ by
    change (A.obj.obj.ρ (g * h)).asHom.hom (ψ ((M.obj.obj.ρ (g * h)⁻¹).asHom.hom m)) =
      (A.obj.obj.ρ g).asHom.hom ((A.obj.obj.ρ h).asHom.hom (ψ ((M.obj.obj.ρ h⁻¹).asHom.hom
        ((M.obj.obj.ρ g⁻¹).asHom.hom m))))
    rw [mul_inv_rev, continuousModuleRho_mul_apply ℤ A, continuousModuleRho_mul_apply R M]

/-- The conjugation action sends `ψ` to `m ↦ γ (ψ (γ⁻¹ m))`. -/
lemma homDualRepresentation_apply (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (γ : Γ)
    (ψ : M.obj.obj.V →+ A.obj.obj.V) (m : M.obj.obj.V) :
    homDualRepresentation R A M γ ψ m =
      (A.obj.obj.ρ γ).asHom.hom (ψ ((M.obj.obj.ρ γ⁻¹).asHom.hom m)) :=
  rfl

private lemma rho_apply_rho_inv_apply (N : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ)
    (γ : Γ) (x : N.obj.obj.V) : (N.obj.obj.ρ γ).asHom.hom ((N.obj.obj.ρ γ⁻¹).asHom.hom x) = x := by
  rw [← continuousModuleRho_mul_apply, mul_inv_cancel, continuousModuleRho_one_apply]

variable [IsTopologicalGroup Γ]

/-- The conjugation action on `Hom_ℤ(M, A)` is continuous for `M` finite. -/
lemma isContinuous_homDualRepresentation (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ)
    [Finite M.obj.obj.V] :
    (actionOfRepresentation Rᵐᵒᵖ Γ (M.obj.obj.V →+ A.obj.obj.V)
      (homDualRepresentation R A M)).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro ψ
  let H : Subgroup Γ :=
    { carrier := {γ | homDualRepresentation R A M γ ψ = ψ}
      mul_mem' := fun {a b} ha hb ↦ by
        change homDualRepresentation R A M (a * b) ψ = ψ
        rw [map_mul, Module.End.mul_apply, show homDualRepresentation R A M b ψ = ψ from hb, ha]
      one_mem' := by
        change homDualRepresentation R A M 1 ψ = ψ
        rw [map_one]
        rfl
      inv_mem' := fun {a} ha ↦ by
        change homDualRepresentation R A M a⁻¹ ψ = ψ
        conv_lhs => rw [← (show homDualRepresentation R A M a ψ = ψ from ha)]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  change IsOpen (H : Set Γ)
  let O : Set Γ := ⋂ m : M.obj.obj.V, ({γ | (M.obj.obj.ρ γ).asHom.hom m = m} ∩
    {γ | (A.obj.obj.ρ γ).asHom.hom (ψ m) = ψ m})
  have hO : IsOpen O := isOpen_iInter_of_finite fun m ↦
    (isOpen_stabilizer R Γ M m).inter (isOpen_stabilizer ℤ Γ A (ψ m))
  have h1 : (1 : Γ) ∈ O := Set.mem_iInter.mpr fun m ↦
    ⟨continuousModuleRho_one_apply R M m, continuousModuleRho_one_apply ℤ A (ψ m)⟩
  refine Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds h1) ?_)
  intro γ hγ
  have hγ' := Set.mem_iInter.mp hγ
  change homDualRepresentation R A M γ ψ = ψ
  refine AddMonoidHom.ext fun m ↦ ?_
  change (A.obj.obj.ρ γ).asHom.hom (ψ ((M.obj.obj.ρ γ⁻¹).asHom.hom m)) = ψ m
  have hinv : (M.obj.obj.ρ γ⁻¹).asHom.hom m = m := by
    have := rho_apply_rho_inv_apply R M γ⁻¹ m
    rwa [inv_inv, (hγ' m).1] at this
  rw [hinv]
  exact (hγ' m).2

variable [Finite R] [Finite A.obj.obj.V]

/-- **`Hom_ℤ(M, A)` as a finite `Rᵐᵒᵖ`-module with a continuous action of `Γ`.** -/
def homDualObj (M : FiniteTypeContinuousModule.{u, v, w} R Γ) :
    FiniteTypeContinuousModule.{u, v, max w w'} Rᵐᵒᵖ Γ :=
  haveI : Module.Finite R M.obj.obj.obj.V := M.property
  haveI : Finite M.obj.obj.obj.V := Module.finite_of_finite R
  ⟨ofRepresentation (homDualRepresentation R A M.obj)
      (isContinuous_homDualRepresentation R A M.obj), by
    have : Finite (M.obj.obj.obj.V →+ A.obj.obj.V) :=
      Finite.of_injective _ DFunLike.coe_injective
    change Module.Finite Rᵐᵒᵖ (M.obj.obj.obj.V →+ A.obj.obj.V)
    exact Module.Finite.of_finite⟩

/-- Precomposition `Hom_ℤ(M, A) → Hom_ℤ(M', A)` with a morphism `M' ⟶ M`. -/
def homDualPrecomp {M M' : FiniteTypeContinuousModule.{u, v, w} R Γ} (f : M' ⟶ M) :
    (M.obj.obj.obj.V →+ A.obj.obj.V) →ₗ[Rᵐᵒᵖ] (M'.obj.obj.obj.V →+ A.obj.obj.V) where
  toFun ψ := ψ.comp f.hom.hom.hom.hom.hom.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' r ψ := AddMonoidHom.ext fun m ↦ by
    change ψ (r.unop • f.hom.hom.hom.hom.hom m) = ψ (f.hom.hom.hom.hom.hom (r.unop • m))
    rw [f.hom.hom.hom.hom.hom.map_smul]

/-- **`M ↦ Hom_ℤ(M, A)`**, contravariant, from finite `R`-modules with a continuous action of `Γ`
to finite `Rᵐᵒᵖ`-modules with a continuous action of `Γ`. -/
def homDualFunctor :
    (FiniteTypeContinuousModule.{u, v, w} R Γ)ᵒᵖ ⥤
      FiniteTypeContinuousModule.{u, v, max w w'} Rᵐᵒᵖ Γ where
  obj M := homDualObj R A M.unop
  map {M M'} f := ObjectProperty.homMk ((homEquiv Rᵐᵒᵖ Γ _ _).symm
    ⟨homDualPrecomp R A f.unop, fun γ (ψ : M.unop.obj.obj.obj.V →+ A.obj.obj.V) ↦
      AddMonoidHom.ext fun m ↦ by
        change (A.obj.obj.ρ γ).asHom.hom (ψ ((M.unop.obj.obj.obj.ρ γ⁻¹).asHom.hom
            (f.unop.hom.hom.hom.hom.hom m))) =
          (A.obj.obj.ρ γ).asHom.hom
            (ψ (f.unop.hom.hom.hom.hom.hom ((M'.unop.obj.obj.obj.ρ γ⁻¹).asHom.hom m)))
        exact congrArg (fun x ↦ (A.obj.obj.ρ γ).asHom.hom (ψ x))
          (ConcreteCategory.congr_hom (f.unop.hom.hom.hom.comm γ⁻¹) m).symm⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### The pairing -/

section Pairing

variable {n : ℕ} [NeZero n] [IsAddCyclic A.obj.obj.V] (hA : Nat.card A.obj.obj.V = n)

/-- The pairing `Hom_ℤ(M, A) → Hom_ℤ(A, M)^∨` as an `Rᵐᵒᵖ`-linear map. -/
def homTwistPairingLinear (M : FiniteTypeContinuousModule.{u, v, w} R Γ) :
    (M.obj.obj.obj.V →+ A.obj.obj.V) →ₗ[Rᵐᵒᵖ] CharacterModule (A.obj.obj.V →+ M.obj.obj.obj.V) where
  toFun ψ := Stacks.CharacterModule.cyclicHomPairing hA ψ
  map_add' := map_add _
  map_smul' _ _ := rfl

omit [IsTopologicalGroup Γ] [Finite R] [Finite A.obj.obj.V] in
include hA in
/-- The pairing intertwines the conjugation actions. -/
theorem homTwistPairingLinear_comm (M : FiniteTypeContinuousModule.{u, v, w} R Γ) (γ : Γ)
    (ψ : M.obj.obj.obj.V →+ A.obj.obj.V) :
    homTwistPairingLinear R A hA M (homDualRepresentation R A M.obj γ ψ) =
      characterRepresentation (homTwistRepresentation R A M.obj) γ
        (homTwistPairingLinear R A hA M ψ) := by
  refine DFunLike.ext _ _ fun φ ↦ ?_
  change Stacks.CharacterModule.zmodToRatCircle n (Stacks.CharacterModule.cyclicEndScalar hA
      ((homDualRepresentation R A M.obj γ ψ).comp φ)) =
    Stacks.CharacterModule.zmodToRatCircle n (Stacks.CharacterModule.cyclicEndScalar hA
      (ψ.comp (homTwistRepresentation R A M.obj γ⁻¹ φ)))
  congr 1
  let σ : A.obj.obj.V →+ A.obj.obj.V := (A.obj.obj.ρ γ).asHom.hom.toAddMonoidHom
  let σ' : A.obj.obj.V →+ A.obj.obj.V := (A.obj.obj.ρ γ⁻¹).asHom.hom.toAddMonoidHom
  have hσ : ∀ a, σ (σ' a) = a := rho_apply_rho_inv_apply ℤ A γ
  rw [← Stacks.CharacterModule.cyclicEndScalar_conj hA
    (ψ.comp (homTwistRepresentation R A M.obj γ⁻¹ φ)) σ σ' hσ]
  congr 1
  refine AddMonoidHom.ext fun a ↦ ?_
  change (A.obj.obj.ρ γ).asHom.hom (ψ ((M.obj.obj.obj.ρ γ⁻¹).asHom.hom (φ a))) =
    (A.obj.obj.ρ γ).asHom.hom (ψ ((M.obj.obj.obj.ρ γ⁻¹).asHom.hom (φ ((A.obj.obj.ρ γ⁻¹⁻¹).asHom.hom
      ((A.obj.obj.ρ γ⁻¹).asHom.hom a)))))
  rw [inv_inv, rho_apply_rho_inv_apply]

variable (hM : ∀ (M : FiniteTypeContinuousModule.{u, v, w} R Γ) (m : M.obj.obj.obj.V), n • m = 0)

/-- **`Hom_ℤ(A, M)^∨ ≅ Hom_ℤ(M, A)`**, for `A` cyclic of order `n` and `n M = 0`: the inverse of
the composition pairing `Hom(A, M) × Hom(M, A) → End(A) = ℤ/n ⊂ ℚ/ℤ`. For `A = μ_n` this is
`M(-1)^∨ ≅ Hom(M, μ_n)`. -/
def homTwistDualIso (M : FiniteTypeContinuousModule.{u, v, w} R Γ) :
    (finiteTypeContinuousModuleDual.{u, v, max w' w} R Γ).obj
        (Opposite.op (homTwistObj R A M)) ≅ homDualObj R A M :=
  haveI : Module.Finite R M.obj.obj.obj.V := M.property
  haveI : Finite M.obj.obj.obj.V := Module.finite_of_finite R
  (finiteTypeContinuousModuleIsoMk (M := homDualObj R A M)
    (N := (finiteTypeContinuousModuleDual.{u, v, max w' w} R Γ).obj
      (Opposite.op (homTwistObj R A M)))
    (LinearEquiv.ofBijective (homTwistPairingLinear R A hA M)
      (Stacks.CharacterModule.cyclicHomPairing_bijective hA (hM M)))
    (homTwistPairingLinear_comm R A hA M)).symm

/-- **`M(-1)^∨ ≅ Hom(M, A)` naturally in `M`**: the isomorphisms `homTwistDualIso` form a natural
isomorphism `(Hom_ℤ(A, -))^∨ ≅ Hom_ℤ(-, A)` of contravariant functors. -/
def homTwistDualNatIso :
    (homTwistFunctor.{u, v, w, w'} R A).op ⋙ finiteTypeContinuousModuleDual.{u, v, max w' w} R Γ ≅
      homDualFunctor R A :=
  (NatIso.ofComponents (fun M ↦ (homTwistDualIso R A hA hM M.unop).symm) fun {M M'} f ↦ by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (ψ : M.unop.obj.obj.obj.V →+ A.obj.obj.V)
    exact DFunLike.ext (F := CharacterModule (A.obj.obj.V →+ M'.unop.obj.obj.obj.V)) _ _
      fun φ ↦ rfl).symm

end Pairing

end Stacks.GroupCohomology

end
