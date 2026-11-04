module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TildeQuasicoherent

/-!
# The presheaf `T ↦ 𝒪(T) ⊗_A M` is cartesian

Let `U` be a scheme over `S` with ring of global functions `A`, and let `M` be an `A`-module.  The
presheaf `T ↦ 𝒪(T) ⊗_A M` on the fppf site of `U` is cartesian: for `f : T' ⟶ T` the comparison
`𝒪(T') ⊗_{𝒪(T)} (𝒪(T) ⊗_A M) ⟶ 𝒪(T') ⊗_A M` is the cancellation of base change.  Since `M~` is
quasi-coherent, it is cartesian on affines as well, and the sheafification map
`(T ↦ 𝒪(T) ⊗_A M) ⟶ M~` is bijective on sections over every affine object.

## Main results

* `AlgebraicGeometry.Stack.isCartesianOnAffines_tildePresheaf`.
* `AlgebraicGeometry.Stack.bijective_tildeUnit_app`: `𝒪(T) ⊗_A M ≅ M~(T)` for `T` affine.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u w

namespace LinearMap

variable {A Sx Sy M N O : Type*} [CommRing A] [CommRing Sx] [CommRing Sy] [Algebra A Sx]
  [Algebra A Sy] [Algebra Sx Sy] [IsScalarTower A Sx Sy] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module Sx N] [Module A N] [IsScalarTower A Sx N]
  [AddCommGroup O] [Module Sy O] [Module Sx O] [Module A O] [IsScalarTower Sx Sy O]
  [IsScalarTower A Sx O] [IsScalarTower A Sy O]

/-- **Cancellation of base change**: if `N` is the base change of `M` to `Sx` and the composite
`M ⟶ N ⟶ O` exhibits `O` as the base change of `M` to `Sy`, then `Sy ⊗_{Sx} N ⟶ O` is
bijective. -/
theorem bijective_liftBaseChange_of_isBaseChange_comp {ix : M →ₗ[A] N} (hx : IsBaseChange Sx ix)
    (r : N →ₗ[Sx] O) (hy : IsBaseChange Sy ((r : N →ₗ[A] O) ∘ₗ ix)) :
    Function.Bijective (r.liftBaseChange Sy) := by
  have h := IsBaseChange.of_comp hx hy
  have he : ⇑(r.liftBaseChange Sy) = ⇑h.equiv := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s n => rw [LinearMap.liftBaseChange_tmul, IsBaseChange.equiv_tmul]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  rw [he]
  exact h.equiv.bijective

end LinearMap

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)

/-- **`T ↦ 𝒪(T) ⊗_A M` is cartesian**: its restriction maps are base changes. -/
theorem isCartesianOnAffines_tildePresheaf (M : ModuleCat.{u} (schemeGlobalRing U)) :
    FibredSite.IsCartesianOnAffines (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
      ((tildePresheafFunctor.{u, w} U).obj M) := by
  intro x y f _ _
  have hp := (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
  let iAx : Algebra (schemeGlobalRing U) (FibredSite.sectionRing hp x) :=
    (globalRingHomApp U (op x)).toAlgebra
  let iAy : Algebra (schemeGlobalRing U) (FibredSite.sectionRing hp y) :=
    (globalRingHomApp U (op y)).toAlgebra
  let ixy : Algebra (FibredSite.sectionRing hp x) (FibredSite.sectionRing hp y) :=
    FibredSite.sectionAlgebra hp f
  have hg : ∀ a, algebraMap (FibredSite.sectionRing hp x) (FibredSite.sectionRing hp y)
      (globalRingHomApp U (op x) a) = globalRingHomApp U (op y) a := fun a =>
    Stacks.PullbackModel.app_naturality_apply (schemeGlobalRingHom U) f.op a
  have : IsScalarTower (schemeGlobalRing U) (FibredSite.sectionRing hp x)
      (FibredSite.sectionRing hp y) :=
    IsScalarTower.of_algebraMap_eq (fun a => (hg a).symm)
  let : Module (FibredSite.sectionRing hp x) (((tildePresheafFunctor.{u, w} U).obj M).obj (op x)) :=
    FibredSite.sectionModule hp ((tildePresheafFunctor.{u, w} U).obj M) x
  let : Module (FibredSite.sectionRing hp y) (((tildePresheafFunctor.{u, w} U).obj M).obj (op y)) :=
    FibredSite.sectionModule hp ((tildePresheafFunctor.{u, w} U).obj M) y
  let : Module (FibredSite.sectionRing hp x) (((tildePresheafFunctor.{u, w} U).obj M).obj (op y)) :=
    FibredSite.sectionModuleAlong hp ((tildePresheafFunctor.{u, w} U).obj M) f
  have : IsScalarTower (FibredSite.sectionRing hp x) (FibredSite.sectionRing hp y)
      (((tildePresheafFunctor.{u, w} U).obj M).obj (op y)) :=
    FibredSite.sectionIsScalarTower hp ((tildePresheafFunctor.{u, w} U).obj M) f
  let : Module (schemeGlobalRing U) (((tildePresheafFunctor.{u, w} U).obj M).obj (op x)) :=
    Module.compHom (R := FibredSite.sectionRing hp x) _ (globalRingHomApp U (op x))
  let : Module (schemeGlobalRing U) (((tildePresheafFunctor.{u, w} U).obj M).obj (op y)) :=
    Module.compHom (R := FibredSite.sectionRing hp y) _ (globalRingHomApp U (op y))
  have : IsScalarTower (schemeGlobalRing U) (FibredSite.sectionRing hp x)
      (((tildePresheafFunctor.{u, w} U).obj M).obj (op x)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hAy : IsScalarTower (schemeGlobalRing U) (FibredSite.sectionRing hp y)
      (((tildePresheafFunctor.{u, w} U).obj M).obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower (schemeGlobalRing U) (FibredSite.sectionRing hp x)
      (((tildePresheafFunctor.{u, w} U).obj M).obj (op y)) :=
    IsScalarTower.of_algebraMap_smul fun a z => by
      change algebraMap (FibredSite.sectionRing hp x) (FibredSite.sectionRing hp y)
        (globalRingHomApp U (op x) a) • z = a • z
      rw [hg a]
      exact algebraMap_smul (FibredSite.sectionRing hp y) a z
  let ix : M →ₗ[schemeGlobalRing U] ((tildePresheafFunctor.{u, w} U).obj M).obj (op x) :=
    TensorProduct.mk (schemeGlobalRing U) (FibredSite.sectionRing hp x) M 1
  have hx : IsBaseChange (FibredSite.sectionRing hp x) ix :=
    TensorProduct.isBaseChange (schemeGlobalRing U) M (FibredSite.sectionRing hp x)
  have hcomp : ((FibredSite.restrictionLinearMap hp ((tildePresheafFunctor.{u, w} U).obj M)
      f).restrictScalars (schemeGlobalRing U)) ∘ₗ ix =
        TensorProduct.mk (schemeGlobalRing U) (FibredSite.sectionRing hp y) M 1 := by
    refine LinearMap.ext fun m => ?_
    change Stacks.PullbackModel.tmul (M := M) (globalRingHomApp U (op y))
      (((BigFppfOver.toScheme B S hS).map f.left).appTop.hom 1) m =
        Stacks.PullbackModel.tmul (M := M) (globalRingHomApp U (op y)) 1 m
    rw [map_one]
    rfl
  have hy : IsBaseChange (FibredSite.sectionRing hp y)
      (((FibredSite.restrictionLinearMap hp ((tildePresheafFunctor.{u, w} U).obj M)
        f).restrictScalars (schemeGlobalRing U)) ∘ₗ ix) := by
    rw [hcomp]
    exact TensorProduct.isBaseChange (schemeGlobalRing U) M (FibredSite.sectionRing hp y)
  exact LinearMap.bijective_liftBaseChange_of_isBaseChange_comp hx _ hy

/-- The sheafification map `(T ↦ 𝒪(T) ⊗_A M) ⟶ M~`. -/
noncomputable abbrev tildeUnit (M : ModuleCat.{u} (schemeGlobalRing U)) :=
  Stacks.SheafOfModules.TensorSheafification.toSheafify
    (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))
      ((tildePresheafFunctor.{u, w} U).obj M)

/-- **`𝒪(T) ⊗_A M = M~(T)` for `T` affine**: the sheafification map of `T ↦ 𝒪(T) ⊗_A M` is
bijective on sections over every affine object, both presheaves being cartesian on affines. -/
theorem bijective_tildeUnit_app (M : ModuleCat.{u} (schemeGlobalRing U))
    {x : (schemeStack.{u, w} B S hS U).val.val.obj}
    (hx : IsAffineOver B S hS ((schemeStack.{u, w} B S hS U).val.val.p.obj x)) :
    Function.Bijective ((tildeUnit.{u, w} U M).app (op x)) := by
  have hW := GrothendieckTopology.W_toSheafify
    (AlgebraicStacks.fppfSiteTopology B S hS (schemeStack.{u, w} B S hS U))
    ((tildePresheafFunctor.{u, w} U).obj M).presheaf
  have : PresheafOfModules.IsLocallyInjective _ (tildeUnit.{u, w} U M) := hW.isLocallyInjective
  have : PresheafOfModules.IsLocallySurjective _ (tildeUnit.{u, w} U M) := hW.isLocallySurjective
  exact FibredSite.bijective_app_of_isLocallyBijective_of_isCartesianOnAffines _
    (tildeUnit.{u, w} U M) (isCartesianOnAffines_tildePresheaf.{u, w} U M)
    (FibredSite.isCartesianOnAffines_of_isQuasicoherentOnSite _ ((tildeFunctor.{u, w} U).obj M)
      (isQuasicoherentOnSite_tilde.{u, w} M)) hx

end AlgebraicGeometry.Stack
