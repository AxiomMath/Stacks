module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedEpsilonChasePointwiseCocycle

/-!
# The underived base change cocycle of a composite of affine representables, unconditionally

Let `U'' --h--> U' --g--> U` be morphisms of the big fppf site over `S` whose underlying schemes
are affine, with rings of global functions `R`, `R'`, `R''`.  At every `R`-module `N` the
contraction `g^* ⋙ h^* ≅ (h ≫ g)^*` of the pullbacks, the underived base change isomorphism
`g^*(M^~) ≅ (R' ⊗_R M)^~` for `g` pushed along `h^*`, the one for `h`, and the associated module
of the contraction `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −` of the extensions of scalars compose to the
isomorphism for `h ≫ g`.

`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_cocycle_app` states this with the
composition coherence of the underived isomorphism — the underived half of [Stacks, Tag 0FJX] for
affine representables — as a hypothesis `hcoh`, written out as the seven-factor pasting of
`Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso`.  That coherence is
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_comp`: it says that
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackCompIso`, which *is* that pasting, is
the isomorphism of `h ≫ g`.  So it discharges `hcoh` by delta alone, with no reformulation, and
this file records the resulting unconditional statement.

## Main results

* `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_cocycle_app_unconditional`: the
  underived base change cocycle of a composite of affine representables, at a module, with no
  hypothesis beyond the affineness of the three underlying schemes.

## References

* [Stacks Project, Tag 0FJX](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

attribute [local instance] additive_extendScalars_ofRingHom
  additive_pullbackModules_ofRepresentedSpaceMap additive_associated_ofAffineRepresentable

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U'' U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (h : U'' ⟶ U') (g : U' ⟶ U)

/-- **The underived base change cocycle of a composite of affine representables, at a module.**
At every `R`-module `N` the contraction of the pullbacks, the underived base change isomorphism
for `g` pushed along `h^*`, the one for `h`, and the associated module of the contraction of the
extensions of scalars compose to the isomorphism for `h ≫ g`.

This is `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_cocycle_app` with its
hypothesis discharged by
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_comp`, the composition coherence
of the underived affine base change isomorphism. -/
theorem representedAffineAssociatedPullbackIso_cocycle_app_unconditional
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedSpacePullbackCompIso B S hS h g).inv.app
          ((representedAffineAssociated B S hS U).obj N) ≫
        (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom).map
          ((representedAffineAssociatedPullbackIso B S hS g).hom.app N) ≫
        (representedAffineAssociatedPullbackIso B S hS h).hom.app
          ((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).obj N) ≫
        (representedAffineAssociated B S hS U'').map
          ((representedAffineExtendScalarsCompIso B S hS h g).hom.app N) =
      (representedAffineAssociatedPullbackIso B S hS (h ≫ g)).hom.app N :=
  representedAffineAssociatedPullbackIso_cocycle_app B S hS h g
    (representedAffineAssociatedPullbackIso_comp B S hS h g) N

end AlgebraicGeometry.Space

end
