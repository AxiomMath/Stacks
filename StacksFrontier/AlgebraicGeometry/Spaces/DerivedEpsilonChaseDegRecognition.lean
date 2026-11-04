module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedEpsilonChaseComplexRecognition
public import StacksFrontier.AlgebraicGeometry.Spaces.HomotopyFactorQuotientPullback
public import StacksFrontier.CategoryTheory.Functor.Derived.DerivedEpsilonChaseDegGeneric

/-!
# The four factors of the degreewise base change cocycle, read through the quotient

The degreewise base change cocycle of a composite of affine representables lives on complexes; the
chase of two derived base change squares that consumes it lives on the unbounded homotopy
categories.  Each of the four factors of the cocycle, and its right-hand side, is the image under
`CategoryTheory.HomotopyCategory.quotient` of a morphism of complexes.  This file records those
recognitions.

Two of the five are already available: the base change isomorphism on homotopy categories is the
image of the one on complexes by
`AlgebraicGeometry.Space.representedAffineHomotopyPullbackIso_hom_app`, which covers both the
third factor and the right-hand side.  The three recorded here are the leading contraction of the
two pullbacks, the second factor — a pullback of a base change isomorphism — and the fourth, the
associated module of the contraction of the two extensions of scalars.

No hypotheses are carried: every statement here is unconditional in `h` and `g`.

## Main results

* `AlgebraicGeometry.Space.representedSpaceHomotopyPullbackCompIso_inv_app_homotopyAssociated`:
  the contraction of the two pullbacks on homotopy categories, read backwards at a degreewise
  associated module, is the image of the degreewise contraction read backwards.  Its Mathlib-level
  half is
  `AlgebraicGeometry.Space.mapHomotopyCategoryCompIso_inv_app_representedAffineHomotopyAssociated`.
* `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy_map_representedAffineHomotopyPullbackIso`:
  the pullback along `h` of the base change isomorphism of `g` is the image of the degreewise
  pullback of the degreewise base change isomorphism.
* `AlgebraicGeometry.Space.representedAffineHomotopyAssociated_map`: the degreewise associated
  module on homotopy categories is the image of the degreewise associated module.

## Implementation notes

Every step here is an identity, but which identities may be asked of the elaborator *at these
functors* is tightly constrained, and the shape of this file is that constraint.

* `AlgebraicGeometry.Space.representedSpaceHomotopyPullbackCompIso_eq` costs 769 heartbeats; the
  same identification under an `CategoryTheory.Iso.inv` projection costs 185,876 when the object is
  the same on both sides, and does not terminate inside the budget when it is not, because
  projecting forces the isomorphism to a constructor application, which unfolds the construction of
  an inverse image of sheaves of modules.  The contraction is therefore recognised as an equation of
  isomorphisms and transported with `StacksDraft.ComparisonSquare.inv_app_congr`.
* For the same reason the base change isomorphism on homotopy categories is not projected here
  either: `AlgebraicGeometry.Space.representedAffineHomotopyPullbackIso_hom_app` does that once,
  in the file that builds it, and is transported under the pullback functor with
  `StacksDraft.ComparisonSquare.functor_map_congr`.
* The two remaining identities,
  `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy_map_quotient_map` and
  `AlgebraicGeometry.Space.representedAffineHomotopyAssociated_map`, are stated at a *variable*
  morphism of complexes, where `rfl` has nothing concrete to unfold.

## References

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

/-- **The degreewise associated module on homotopy categories is the image of the degreewise
associated module.**  `AlgebraicGeometry.Space.representedAffineHomotopyAssociated` is the
degreewise associated module followed by the quotient, so this holds by construction. -/
theorem representedAffineHomotopyAssociated_map (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {K L : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ℤ}
    (φ : K ⟶ L) :
    (representedAffineHomotopyAssociated B S hS V).map φ =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((representedAffineAssociated B S hS V).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  rfl

/-- **The degreewise pullback of complexes on homotopy categories is the image of the degreewise
pullback.**  `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy` is the functor induced on
homotopy categories by the degreewise pullback, so this holds by construction.

Stated at a variable morphism of complexes, which is what keeps it checkable; see the note at the
head of this file. -/
theorem smallEtalePullbackMapHomotopy_map_quotient_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {K L : HomologicalComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)} (φ : K ⟶ L) :
    (smallEtalePullbackMapHomotopy B S hS f).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS f).toModulesHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  rfl

variable {U'' U' U : BigFppfOver B S hS} (h : U'' ⟶ U') (g : U' ⟶ U)

/-- **The contraction `g^* ⋙ h^* ≅ (h ≫ g)^*` on homotopy categories is the comparison of the
induced functors of the degreewise contraction.**  This is
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso_eq` at the factorisation
`AlgebraicGeometry.Space.representedSpaceMap_comp`, whose own proof contracts the three factors of
the identification on variables.

It is recorded as an equation of isomorphisms rather than used under a projection; see the note at
the head of this file. -/
theorem representedSpaceHomotopyPullbackCompIso_eq :
    representedSpaceHomotopyPullbackCompIso B S hS h g =
      Functor.mapHomotopyCategoryCompIso (representedSpacePullbackCompIso B S hS h g)
        (ComplexShape.up ℤ) :=
  smallEtalePullbackMapHomotopyFactorIso_eq (representedSpaceMap B S hS h)
    (representedSpaceMap B S hS g) (representedSpaceMap B S hS (h ≫ g))
    (representedSpaceMap_comp B S hS h g)

/-- **The comparison of the induced pullbacks on homotopy categories, read backwards at a
degreewise associated module.**  It is the image under the quotient of the degreewise comparison
read backwards.

This is `StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient'`, which is
`rfl` on variables, with its three additivity instances written out so that nothing is left for
inference; it is the one step of this file that spends a sizeable fraction of the heartbeat budget,
because the degreewise associated module has to be recognised as an image of the quotient
underneath the comparison. -/
theorem mapHomotopyCategoryCompIso_inv_app_representedAffineHomotopyAssociated
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (Functor.mapHomotopyCategoryCompIso (representedSpacePullbackCompIso B S hS h g)
          (ComplexShape.up ℤ)).inv.app ((representedAffineHomotopyAssociated B S hS U).obj M) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (representedSpacePullbackCompIso B S hS h g)
          (ComplexShape.up ℤ)).inv.app
            (((representedAffineAssociated B S hS U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) :=
  @StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient'
    _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackModules_smallEtale_additive (representedSpaceMap B S hS g))
    (pullbackModules_smallEtale_additive (representedSpaceMap B S hS h))
    (pullbackModules_smallEtale_additive (representedSpaceMap B S hS (h ≫ g)))
    (representedSpacePullbackCompIso B S hS h g) (ComplexShape.up ℤ)
    (((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)

/-- **The contraction `g^* ⋙ h^* ≅ (h ≫ g)^*` on homotopy categories, read backwards at a
degreewise associated module.**  It is the image under the quotient of the degreewise contraction
read backwards.

`AlgebraicGeometry.Space.mapHomotopyCategoryCompIso_inv_app_representedAffineHomotopyAssociated`,
transported along `AlgebraicGeometry.Space.representedSpaceHomotopyPullbackCompIso_eq` with
`StacksDraft.ComparisonSquare.inv_app_congr` — not by identifying the two contractions underneath
the projection, which does not terminate inside the budget. -/
theorem representedSpaceHomotopyPullbackCompIso_inv_app_homotopyAssociated
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedSpaceHomotopyPullbackCompIso B S hS h g).inv.app
        ((representedAffineHomotopyAssociated B S hS U).obj M) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (representedSpacePullbackCompIso B S hS h g)
          (ComplexShape.up ℤ)).inv.app
            (((representedAffineAssociated B S hS U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) :=
  (StacksDraft.ComparisonSquare.inv_app_congr
        (representedSpaceHomotopyPullbackCompIso_eq B S hS h g) _).trans
    (mapHomotopyCategoryCompIso_inv_app_representedAffineHomotopyAssociated B S hS h g M)

/-- **The pullback along `h` of the base change isomorphism of `g`, on homotopy categories.**  It
is the image under the quotient of the degreewise pullback of the degreewise base change
isomorphism.

`AlgebraicGeometry.Space.representedAffineHomotopyPullbackIso_hom_app` transported under the
pullback functor, followed by
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy_map_quotient_map`. -/
theorem smallEtalePullbackMapHomotopy_map_representedAffineHomotopyPullbackIso
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS h)).map
        ((representedAffineHomotopyPullbackIso B S hS g).hom.app M) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((representedAffineComplexPullbackIso B S hS g).hom.app M)) :=
  (StacksDraft.ComparisonSquare.functor_map_congr
        (smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS h))
        (representedAffineHomotopyPullbackIso_hom_app B S hS g M)).trans
    (smallEtalePullbackMapHomotopy_map_quotient_map B S hS (representedSpaceMap B S hS h)
      ((representedAffineComplexPullbackIso B S hS g).hom.app M))

end AlgebraicGeometry.Space

end
