module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedExtendScalarsContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPullbackContraction
public import StacksFrontier.CategoryTheory.Functor.Derived.PastedBaseChangeCocycle

/-!
# The underived base change cocycle of a composite of affine representables, at a module

Let `U'' --h--> U' --g--> U` be morphisms of the big fppf site over `S` whose underlying schemes
are affine, with rings of global functions `R`, `R'`, `R''`.  The underived base change
isomorphism `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso`,
`g^*(M^~) ≅ (R' ⊗_R M)^~`, is compatible with composition: the contraction
`g^* ⋙ h^* ≅ (h ≫ g)^*` of the pullbacks, the isomorphism for `g` pushed along `h^*`, the
isomorphism for `h`, and the contraction `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −` of the extensions of
scalars compose to the isomorphism for `h ≫ g`.

This file records that cocycle **at a module**, which is the form a chase of derived base change
squares consumes, from the same statement **as an equation of isomorphisms of functors**, which is
the form in which it is proved.

## The hypothesis this file carries, and why

`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_cocycle_app` is **conditional**.
Its hypothesis `hcoh` is the composition coherence of
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso` itself, written out as the
pasting of the two base change isomorphisms along the two contractions:

`Φ_R ◁ cU⁻¹ ≫ (ρ ▷ h^*) ≫ ((R' ⊗_R −) ▷ σ) ≫ (δ ▷ Φ_{R''}) = κ`,

an isomorphism `Φ_R ⋙ (h ≫ g)^* ≅ (R'' ⊗_R −) ⋙ Φ_{R''}`.  That is a real mathematical
statement about the underived isomorphism, not a placeholder: it is the underived half of
[Stacks, Tag 0FJX] for affine representables, and it is proved — as
`representedAffineAssociatedPullbackIso_comp` — on a different branch, which this one cannot
import.  It is carried here, written out character for character in the shape
`Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq` asks for, precisely so that
the equation proved there discharges it by delta alone, with no reformulation.  **Nothing
downstream of this file is unconditional until that hypothesis is discharged.**

## Main results

* `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_cocycle_app`: the underived base
  change cocycle of a composite of affine representables, at a module, given the composition
  coherence of the underived isomorphism as an equation of isomorphisms of functors.

## Implementation notes

The whole content is `Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq`, which
performs the pasting on variables.  Performed on these concrete functors — inverse images of
sheaves of modules on algebraic spaces — the `isDefEq` checks a `simp` on the whiskered composite
would run exhaust the heartbeat budget; the whole declaration as it stands costs 106,052.

The hypothesis is kept in this file, alone, for the same reason: elaborating the seven-factor
pasting costs most of that 106,052, and a declaration that both states it and does anything else
does not fit.

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
Given the composition coherence `hcoh` of
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso` as an equation of isomorphisms of
functors, at every `R`-module `N` the contraction of the pullbacks, the isomorphism for `g` pushed
along `h^*`, the isomorphism for `h`, and the associated module of the contraction of the
extensions of scalars compose to the isomorphism for `h ≫ g`.

`hcoh` is an input: it is the underived half of [Stacks, Tag 0FJX] for affine representables,
proved elsewhere and not available to this module.  It is written out as the pasting so that the
equation proved elsewhere discharges it unchanged; see the note at the head of this file. -/
theorem representedAffineAssociatedPullbackIso_cocycle_app
    (hcoh : Functor.isoWhiskerLeft (representedAffineAssociated B S hS U)
          (representedSpacePullbackCompIso B S hS h g).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (representedAffineAssociatedPullbackIso B S hS g)
          (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
            (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS h)).toModulesHom) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom)
          (representedAffineAssociatedPullbackIso B S hS h) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (representedAffineExtendScalarsCompIso B S hS h g)
          (representedAffineAssociated B S hS U'') =
      representedAffineAssociatedPullbackIso B S hS (h ≫ g))
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
  Stacks.CategoryTheory.BaseChange.pastedBaseChangeIso_hom_app_of_eq _ _ _ _ _ hcoh N

end AlgebraicGeometry.Space

end
