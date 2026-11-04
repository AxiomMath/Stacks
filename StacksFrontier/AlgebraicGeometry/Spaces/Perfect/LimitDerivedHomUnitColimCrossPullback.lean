module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCrossUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelPushforwardComparison

/-!
# The inverse image of the pullback-pseudofunctor datum, on the spaces-étale models

The point-tensor engine of Stacks 09RI computes derived pullbacks as
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback (spacesEtaleModelHom f)`,
the derived pullback along the morphism of models of the ringed spaces-étale sites: that is the
functor `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat` and
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfKFlat_hom_naturality` are stated for.  The
colimit statement of the tag, `CategoryTheory.PullbackData.LimitSystem.IsColim`, is stated for
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, whose inverse images are the derived
pullbacks along the morphisms of small étale ringed topoi of Stacks 03G8.

This file crosses between the two at the level of a **single** morphism.  The crossing isomorphism
exists already — `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackModelIso` builds it from
any identification of the two underived pullbacks, and
`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` is such an identification — so what
is done here is to instantiate it at the inverse image of the datum, unconditionally, and to read
off what it says about homomorphism groups: the inverse image along `f` of a morphism between
objects in the image of the derived equivalence is, up to conjugation by the crossing isomorphism,
the derived pullback along the morphism of models.  That conjugation is a bijection of
homomorphism groups, `AlgebraicGeometry.Space.modelDerivedPullbackHomEquiv`.

## What this does not do

It does **not** convert a statement about the model-side derived pullbacks into
`CategoryTheory.PullbackData.LimitSystem.IsColim`.  The transition maps and the maps to the vertex
of that statement are `CategoryTheory.PullbackData.factorHom`, conjugation by the comparison
`CategoryTheory.PullbackData.triangle` of a presented factorisation `f ≫ g = k`; crossing them
needs the crossing isomorphism to be **compatible with the composition comparisons** on the two
sides — that `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso` at `k` agrees with
the one at `g` followed by the one at `f`, modulo
`(AlgebraicGeometry.Space.smallEtaleDerivedPullbackData B S hS).compIso` on one side and the
model-side composition comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/SpacesEtaleModelHomCompCocycle.lean` on the other.  That
compatibility is proved nowhere: the crossing isomorphism is built by
`CategoryTheory.Functor.totalLeftDerivedConjugateIso`, for which no composition law is available,
and the two composition comparisons are constructed by different routes — the universal comparison
of a total left derived functor along a composite, against the cocycle of the models.  It is what
still stands between a model-side computation of the homomorphism groups and the conclusion of the
tag.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso`: **the inverse image of the
  pullback-pseudofunctor datum is the derived pullback on the spaces-étale models**, under the
  equivalences of Stacks 03G1 — unconditionally, the identification of the underived pullbacks
  being `AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso`.
* `AlgebraicGeometry.Space.modelDerivedPullbackHomEquiv`: the bijection of homomorphism groups it
  induces.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv_functor_eq`: the functor of the derived
  equivalence is `AlgebraicGeometry.Space.spacesEtaleModelModulesDerivedFunctor`, the two
  spellings of the derived equivalence of Stacks 03G1.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_hom_naturality`: **the crossing
  isomorphism intertwines the model-side derived pullback of a morphism with the inverse image of
  the datum of its image.**
* `AlgebraicGeometry.Space.modelDerivedPullbackHomEquiv_map`: the same solved for the inverse
  image, read on the bijection.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The two spellings of the derived equivalence of Stacks 03G1 agree.**
`AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv` is packaged as an equivalence and
`AlgebraicGeometry.Space.spacesEtaleModelModulesDerivedFunctor` as a bare functor; both are the
degreewise action of `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` on derived
categories. -/
theorem spacesEtaleModelDerivedEquiv_functor_eq (Z : AlgebraicSpaces B S hS) :
    (spacesEtaleModelDerivedEquiv B S hS Z).functor =
      spacesEtaleModelModulesDerivedFunctor B S hS Z :=
  rfl

/-- **The inverse image of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` is the derived
pullback along the morphism of models of the ringed spaces-étale sites**, under the equivalences
`AlgebraicGeometry.Space.spacesEtaleModelModulesDerivedFunctor` of Stacks 03G1.

This is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackModelIso` at the identification
`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackIso` of the two underived pullbacks, with
the existence premise of the derived pullback discharged by
`AlgebraicGeometry.Space.hasDerivedModulePullbacks`; nothing is assumed. -/
def smallEtaleDerivedPullbackDataModelIso :
    derivedPullback (X := spacesEtaleModelRingedTopos B S hS X)
          (Y := spacesEtaleModelRingedTopos B S hS Y) (spacesEtaleModelHom B S hS f) ⋙
        spacesEtaleModelModulesDerivedFunctor B S hS X ≅
      spacesEtaleModelModulesDerivedFunctor B S hS Y ⋙
        (smallEtaleDerivedPullbackData B S hS).pull f :=
  haveI := hasDerivedModulePullbacks B S hS f
  smallEtaleDerivedModulePullbackModelIso B S hS f (spacesEtaleModelModulesPullbackIso B S hS f)

/-- **The crossing isomorphism intertwines the model-side derived pullback with the inverse image
of the datum**: the naturality square of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso`, written out. -/
theorem smallEtaleDerivedPullbackDataModelIso_hom_naturality
    {Km Lm : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules} (ψ : Km ⟶ Lm) :
    (spacesEtaleModelModulesDerivedFunctor B S hS X).map
          ((derivedPullback (spacesEtaleModelHom B S hS f)).map ψ) ≫
        (smallEtaleDerivedPullbackDataModelIso B S hS f).hom.app Lm =
      (smallEtaleDerivedPullbackDataModelIso B S hS f).hom.app Km ≫
        ((smallEtaleDerivedPullbackData B S hS).pull f).map
          ((spacesEtaleModelModulesDerivedFunctor B S hS Y).map ψ) :=
  (smallEtaleDerivedPullbackDataModelIso B S hS f).hom.naturality ψ

/-- **The bijection of homomorphism groups attached to the crossing isomorphism**: morphisms
between the model-side derived pullbacks of `Km` and `Lm` are morphisms between the inverse images
under the datum of their images in `D(𝒪_Y)`. -/
def modelDerivedPullbackHomEquiv
    (Km Lm : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules) :
    ((derivedPullback (spacesEtaleModelHom B S hS f)).obj Km ⟶
        (derivedPullback (spacesEtaleModelHom B S hS f)).obj Lm) ≃
      (((smallEtaleDerivedPullbackData B S hS).pull f).obj
          ((spacesEtaleModelModulesDerivedFunctor B S hS Y).obj Km) ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull f).obj
          ((spacesEtaleModelModulesDerivedFunctor B S hS Y).obj Lm)) :=
  (spacesEtaleModelDerivedEquiv B S hS X).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((smallEtaleDerivedPullbackDataModelIso B S hS f).app Km)
      ((smallEtaleDerivedPullbackDataModelIso B S hS f).app Lm))

/-- The bijection `AlgebraicGeometry.Space.modelDerivedPullbackHomEquiv`, explicitly: apply the
functor of the derived equivalence and conjugate by the components of the crossing isomorphism. -/
theorem modelDerivedPullbackHomEquiv_apply
    (Km Lm : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules)
    (φ : (derivedPullback (spacesEtaleModelHom B S hS f)).obj Km ⟶
      (derivedPullback (spacesEtaleModelHom B S hS f)).obj Lm) :
    modelDerivedPullbackHomEquiv B S hS f Km Lm φ =
      (smallEtaleDerivedPullbackDataModelIso B S hS f).inv.app Km ≫
        (spacesEtaleModelModulesDerivedFunctor B S hS X).map φ ≫
        (smallEtaleDerivedPullbackDataModelIso B S hS f).hom.app Lm :=
  rfl

/-- **The bijection carries the model-side derived pullback of a morphism to the inverse image
under the datum of its image in `D(𝒪_Y)`.** -/
theorem modelDerivedPullbackHomEquiv_map
    {Km Lm : DerivedCategory (spacesEtaleModelRingedTopos B S hS Y).Modules} (ψ : Km ⟶ Lm) :
    modelDerivedPullbackHomEquiv B S hS f Km Lm
        ((derivedPullback (spacesEtaleModelHom B S hS f)).map ψ) =
      ((smallEtaleDerivedPullbackData B S hS).pull f).map
        ((spacesEtaleModelModulesDerivedFunctor B S hS Y).map ψ) :=
  ((smallEtaleDerivedPullbackDataModelIso B S hS f).app Km).inv_comp_eq.2
    (smallEtaleDerivedPullbackDataModelIso_hom_naturality B S hS f ψ)

end AlgebraicGeometry.Space

end
