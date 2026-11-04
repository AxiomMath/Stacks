module

public import StacksFrontier.Algebra.Category.ModuleCat.NatTransGeneratedByUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange

/-!
# The underived affine base change isomorphism is determined by its value at `R`

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` whose source and target have affine
underlying schemes, with rings of global functions `R = Γ(U, 𝒪)` and `R' = Γ(U', 𝒪)` and induced
ring map `φ : R ⟶ R'`. `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso` is the
isomorphism `g^*(M^~) ≅ (R' ⊗_R M)^~`, natural in the `R`-module `M`, normalized so that at
`M = R` it is the trivialization `AlgebraicGeometry.Space.representedAffinePullbackUnitIso` of
Stacks 03LU through `R' ⊗_R R = R'`.

This file records that the normalization *determines* it. The functor `M ↦ g^*(M^~)` is a
composite of two left adjoints — the associated module
(`AlgebraicGeometry.Space.representedAffineAssociatedAdjunction`) and the inverse image of
modules (`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`) — so it preserves
`u`-small colimits, and `ModuleCat.{u} R` is generated under `u`-small colimits by
`ModuleCat.of R R`. By `ModuleCat.natTrans_ext_of_eq_app_self_of_adjunction` a natural
transformation out of it is therefore determined by its value at `M = R`.

## Main results

* `AlgebraicGeometry.Space.natTrans_ext_representedAffineAssociated_comp_pullbackModules`: two
  natural transformations `g^*(M^~) ⟶ (R' ⊗_R M)^~` which agree at `M = R` are equal.
* `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_eq_of_hom_app_self`: **the
  underived affine base change isomorphism is the unique one normalized at the unit.**

## Implementation notes

The preservation of colimits is supplied as the composite of the two adjunctions
(`CategoryTheory.Adjunction.comp`): instance search does not assemble a
`PreservesColimitsOfSize.{u, u}` instance for the composite from instances for the two factors.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- **Two natural transformations `g^*(M^~) ⟶ (R' ⊗_R M)^~` which agree at `M = R` are equal.** -/
theorem natTrans_ext_representedAffineAssociated_comp_pullbackModules
    (Φ Ψ : representedAffineAssociated B S hS U ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ⟶
      ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineAssociated B S hS U')
    (h : Φ.app (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) =
        Ψ.app (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    Φ = Ψ :=
  ModuleCat.natTrans_ext_of_eq_app_self_of_adjunction Φ Ψ
    ((representedAffineAssociatedAdjunction B S hS U).comp
      (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)))) h

/-- **The underived affine base change isomorphism is the unique one normalized at the unit.**
Any isomorphism `g^*(M^~) ≅ (R' ⊗_R M)^~`, natural in `M`, which at `M = R` becomes the
trivialization `AlgebraicGeometry.Space.representedAffinePullbackUnitIso` through `R' ⊗_R R = R'`
is `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso`. -/
theorem representedAffineAssociatedPullbackIso_eq_of_hom_app_self
    (ρ : representedAffineAssociated B S hS U ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ≅
      ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineAssociated B S hS U')
    (hρ : ρ.hom.app (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≫
        (representedAffineAssociated B S hS U').map
          (ModuleCat.ExtendScalars.objSelfIso (representedAffineCommRingCatHom B S hS g).hom).hom =
      (representedAffinePullbackUnitIso B S hS g).hom) :
    ρ = representedAffineAssociatedPullbackIso B S hS g :=
  Iso.ext (natTrans_ext_representedAffineAssociated_comp_pullbackModules B S hS g _ _
    ((cancel_mono ((representedAffineAssociated B S hS U').map
      (ModuleCat.ExtendScalars.objSelfIso
        (representedAffineCommRingCatHom B S hS g).hom).hom)).1
      (hρ.trans (representedAffineAssociatedPullbackIso_hom_app_self B S hS g).symm)))

end AlgebraicGeometry.Space

end
