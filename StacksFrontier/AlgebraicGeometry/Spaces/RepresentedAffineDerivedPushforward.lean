module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareTransport

/-!
# Derived direct image along a morphism of affine representables is restriction of scalars

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` with affine underlying schemes,
with rings of global functions `R` and `R'`. Writing `Φ` for the derived associated-module
functors, the transpose `Φ_R(M|_R) ⟶ Rg_*(Φ_{R'} M)` of the affine base change isomorphism
`Lg^* Φ_R ≅ Φ_{R'}(- ⊗^L_R R')` followed by `Φ_{R'}` of the counit of derived extension of
scalars is an isomorphism, for every `M ∈ D(R')`, as soon as `g` is affine.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineTransportUnit`
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- The map `Φ_R(M|_R) ⟶ Rg_*(Φ_{R'} M)` transposed to the affine base change isomorphism
followed by `Φ_{R'}` of the counit of derived extension of scalars. -/
abbrev representedAffineTransportUnit
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) :=
  Stacks.CategoryTheory.BaseChange.transportUnit
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom)
    (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS g))
    (representedAffineDerivedAssociated B S hS U) (representedAffineDerivedAssociated B S hS U')
    (representedAffineDerivedBaseChangeIso B S hS g) M

/-- **`Rg_* Φ_{R'} ≅ Φ_R ∘ res` along an affine morphism of affine representables**: the
transposed unit is an isomorphism. -/
theorem isIso_representedAffineTransportUnit
    (hg : IsAffineHom B S hS (representedSpaceMap B S hS g).hom)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))) :
    IsIso (representedAffineTransportUnit B S hS g M) := by
  let adjU := representedAffineDerivedAdjunction B S hS U
  let adjU' := representedAffineDerivedAdjunction B S hS U'
  let t := representedAffineTransportUnit B S hS g M
  have h₁ : IsIso ((representedAffineDerivedSections B S hS U).map t) :=
    Stacks.CategoryTheory.BaseChange.isIso_map_transportUnit _ _ _ _ _ adjU adjU' M
  have hsrc := qcohDerived_representedAffineDerivedAssociated_obj B S hS U
    ((ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.obj M)
  have htgt := qcohDerived_derivedModulePushforward_obj B S hS (representedSpaceMap B S hS g)
    (isQuasiCompact_of_isAffineHom_hom _ hg) (isQuasiSeparated_of_isAffineHom_hom _ hg) _
    (qcohDerived_representedAffineDerivedAssociated_obj B S hS U' M)
  have e₁ := isIso_representedAffineDerivedAdjunction_counit_app B S hS U _ hsrc
  have e₂ := isIso_representedAffineDerivedAdjunction_counit_app B S hS U _ htgt
  have hn : (representedAffineDerivedAssociated B S hS U).map
        ((representedAffineDerivedSections B S hS U).map t) ≫ adjU.counit.app _ =
      adjU.counit.app _ ≫ t := adjU.counit.naturality t
  have : IsIso (adjU.counit.app _ ≫ t) := by
    rw [← hn]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      ((representedAffineDerivedAssociated B S hS U).map_isIso _) e₂
  exact IsIso.of_isIso_comp_left (adjU.counit.app _) t

end AlgebraicGeometry.Space

end
