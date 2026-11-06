module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedEpsilonChaseDegRecognition

/-!
# The four factors of the degreewise base change cocycle, in the ascribed spelling

`StacksFrontier/AlgebraicGeometry/Spaces/DerivedEpsilonChaseDegRecognition.lean` recognises each
factor of the degreewise base change cocycle of a composite of affine representables as the image
under `CategoryTheory.HomotopyCategory.quotient` of a morphism of complexes, writing the morphism
of complexes with the *named* degreewise isomorphisms
`AlgebraicGeometry.Space.representedAffineComplexPullbackIso` and
`AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso`.

The generic degreewise cocycle
`StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans_pasted` concludes in the
*ascribed* spelling instead — each base change isomorphism read as

`mapHomologicalComplexCompIso ρ c ≪≫ (mapHomologicalComplexCompIso (Iso.refl _) c).symm`,

with every additivity argument written out, which is the spelling in which the named isomorphisms
are in fact defined.  This file is the translation: each recognition, transported along
`AlgebraicGeometry.Space.representedAffineComplexPullbackIso_eq` and
`AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso_eq`, so that a consumer of
the generic cocycle can discharge its four factors and its right-hand side by *instantiating*
these statements rather than by elaborating the transport inline.

Doing the transport here rather than at the consumer is the point.  Written inline, the five
transports account for 176,093 of the consumer's heartbeats and the declaration does not fit;
performed here, each is one declaration of its own and the consumer's remaining work is 147,101.
See the implementation notes.

No hypotheses are carried: every statement here is unconditional in `g` (resp. in `h` and `g`).

## Main results

* `AlgebraicGeometry.Space.representedAffineHomotopyPullbackIso_hom_app_ascribed`: the base change
  isomorphism on homotopy categories, at a complex, is the image of the ascribed degreewise one.
  It covers both the third factor of the cocycle (at `h`) and its right-hand side (at `h ≫ g`).
* `smallEtalePullbackMapHomotopy_map_representedAffineHomotopyPullbackIso_ascribed`, in
  `AlgebraicGeometry.Space`: the second factor — the pullback along `h` of the base change
  isomorphism of `g`.
* `AlgebraicGeometry.Space.representedAffineHomotopyAssociated_map_extendScalarsCompIso_ascribed`:
  the fourth factor — the associated module of the degreewise contraction of the two extensions of
  scalars.

The first factor of the cocycle needs no translation: the generic lemma reads the contraction of
the two pullbacks as `CategoryTheory.Functor.mapHomologicalComplexCompIso` of the underived
contraction, which is exactly what
`AlgebraicGeometry.Space.representedSpaceHomotopyPullbackCompIso_inv_app_homotopyAssociated`
already concludes.

## Implementation notes

Every statement here is written with the additivity arguments of
`CategoryTheory.Functor.mapHomologicalComplexCompIso` supplied in `@`-form, reproducing verbatim
the arguments of the definitions they are about.  That is not cosmetic: restating one of these
isomorphisms with inference left to run costs 200,169 heartbeats and fails, because inference for
`(R' ⊗_R − ⋙ Φ_{R'}).Additive` does not terminate inside the budget while the preadditive
arguments are still metavariables; with the arguments written out the expected type determines
every one of them and what is left is a delta step and proof irrelevance.  The same observation is
recorded at greater length in
`StacksFrontier/AlgebraicGeometry/Spaces/DerivedEpsilonChaseComplexRecognition.lean`.

Each proof is a single `Eq.trans` of an existing recognition lemma with a transport built from
`StacksDraft.ComparisonSquare.functor_map_congr` and
`StacksDraft.ComparisonSquare.hom_app_congr`.  Neither `rw` nor `simp` occurs, and none may: one
rewrite into a goal at these functors — degreewise inverse images of sheaves of modules on
algebraic spaces — costs 759,301 heartbeats.  Transport along an equation of *isomorphisms*, and
only then take a component, is the one affordable shape; taking the component first and
identifying the two isomorphisms underneath `CategoryTheory.Iso.hom` costs 185,876 when the object
is syntactically the same on both sides and does not terminate when it is not.

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

section OneMorphism

variable {V' V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (k : V' ⟶ V)

/-- **The base change isomorphism on homotopy categories, at a complex, is the image of the
ascribed degreewise one.**  `AlgebraicGeometry.Space.representedAffineHomotopyPullbackIso_hom_app`
read through `AlgebraicGeometry.Space.representedAffineComplexPullbackIso_eq`, so that the
degreewise isomorphism appears in the spelling the generic degreewise cocycle
`StacksDraft.ComparisonSquare.mapHomologicalComplexCompIso_cocycle_trans_pasted` concludes in. -/
theorem representedAffineHomotopyPullbackIso_hom_app_ascribed
    (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ℤ) :
    (representedAffineHomotopyPullbackIso B S hS k).hom.app N =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
              (representedAffineAssociatedPullbackIso B S hS k)
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_representedAffineAssociated B S hS V))
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (pullbackModules_smallEtale_additive (representedSpaceMap B S hS k)))
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_extendScalars_comp_representedAffineAssociated B S hS k))
              (ComplexShape.up ℤ) ≪≫
            (@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _
              (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS k).hom)
              (representedAffineAssociated B S hS V') _ (Iso.refl _)
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (ModuleCat.extendRestrictScalarsAdj
                (representedAffineCommRingCatHom B S hS k).hom).left_adjoint_additive)
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_representedAffineAssociated B S hS V'))
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_extendScalars_comp_representedAffineAssociated B S hS k))
              (ComplexShape.up ℤ)).symm).hom.app N) :=
  (representedAffineHomotopyPullbackIso_hom_app B S hS k N).trans
    (StacksDraft.ComparisonSquare.functor_map_congr _
      (StacksDraft.ComparisonSquare.hom_app_congr
        (representedAffineComplexPullbackIso_eq B S hS k) N))

end OneMorphism

variable {U'' U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (h : U'' ⟶ U') (g : U' ⟶ U)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] in
/-- **The pullback along `h` of the base change isomorphism of `g`, in the ascribed spelling.**
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopy_map_representedAffineHomotopyPullbackIso`
read through `AlgebraicGeometry.Space.representedAffineComplexPullbackIso_eq`.  This is the second
factor of the degreewise base change cocycle of `h ≫ g`. -/
theorem smallEtalePullbackMapHomotopy_map_representedAffineHomotopyPullbackIso_ascribed
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS h)).map
        ((representedAffineHomotopyPullbackIso B S hS g).hom.app M) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS h)).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).map
          ((@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
                (representedAffineAssociatedPullbackIso B S hS g)
                (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_representedAffineAssociated B S hS U))
                (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (pullbackModules_smallEtale_additive (representedSpaceMap B S hS g)))
                (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_extendScalars_comp_representedAffineAssociated B S hS g))
                (ComplexShape.up ℤ) ≪≫
              (@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _
                (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom)
                (representedAffineAssociated B S hS U') _ (Iso.refl _)
                (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (ModuleCat.extendRestrictScalarsAdj
                  (representedAffineCommRingCatHom B S hS g).hom).left_adjoint_additive)
                (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_representedAffineAssociated B S hS U'))
                (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (additive_extendScalars_comp_representedAffineAssociated B S hS g))
                (ComplexShape.up ℤ)).symm).hom.app M)) :=
  (smallEtalePullbackMapHomotopy_map_representedAffineHomotopyPullbackIso B S hS h g M).trans
    (StacksDraft.ComparisonSquare.functor_map_congr _
      (StacksDraft.ComparisonSquare.functor_map_congr _
        (StacksDraft.ComparisonSquare.hom_app_congr
          (representedAffineComplexPullbackIso_eq B S hS g) M)))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- **The associated module of the degreewise contraction of the two extensions of scalars, in the
ascribed spelling.**  `AlgebraicGeometry.Space.representedAffineHomotopyAssociated_map` read
through `AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso_eq`.  This is the
fourth factor of the degreewise base change cocycle of `h ≫ g`. -/
theorem representedAffineHomotopyAssociated_map_extendScalarsCompIso_ascribed
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineHomotopyAssociated B S hS U'').map
        ((representedAffineExtendScalarsComplexCompIso B S hS h g).hom.app M) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((representedAffineAssociated B S hS U'').mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
            (representedAffineExtendScalarsCompIso B S hS h g)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (ModuleCat.extendRestrictScalarsAdj
              (representedAffineCommRingCatHom B S hS g).hom).left_adjoint_additive)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (ModuleCat.extendRestrictScalarsAdj
              (representedAffineCommRingCatHom B S hS h).hom).left_adjoint_additive)
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (ModuleCat.extendRestrictScalarsAdj
              (representedAffineCommRingCatHom B S hS (h ≫ g)).hom).left_adjoint_additive)
            (ComplexShape.up ℤ)).hom.app M)) :=
  (representedAffineHomotopyAssociated_map B S hS U''
      ((representedAffineExtendScalarsComplexCompIso B S hS h g).hom.app M)).trans
    (StacksDraft.ComparisonSquare.functor_map_congr _
      (StacksDraft.ComparisonSquare.functor_map_congr _
        (StacksDraft.ComparisonSquare.hom_app_congr
          (representedAffineExtendScalarsComplexCompIso_eq B S hS h g) M)))

end AlgebraicGeometry.Space

end
