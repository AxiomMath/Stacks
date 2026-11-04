module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMapSliceRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexHomologySliceRestriction

/-!
# The composition product on cohomology sheaves commutes with restriction to a slice site

Let `X` be a ringed site, `U` an object of its underlying category and `K`, `L`, `M` complexes of
`O`-modules. The composition product on the cohomology sheaves of the internal Hom complexes is
induced by the composition morphism of Stacks 0A91 — it is the map that morphism induces on
cohomology, precomposed with the product on the cohomology of a total tensor complex. This file
records the half of its restriction compatibility which concerns the composition morphism:

`Hⁿ(Tot(SheafHom(L, M) ⊗ SheafHom(K, L)))|_U ⟶ Hⁿ(SheafHom(K, M))|_U`

is, through the restriction comparisons of its source and its target, the corresponding map
formed over `U`.

Together with `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso` on the pieces, this says
that the restriction of the graded object with its composition product is the graded object with
its composition product of the restriction, up to the product on the cohomology of a total tensor
complex, which is not a composition datum at all.

## Main results

* `AlgebraicGeometry.RingedSite.compositionMap_over'`: the chain-level statement of
  `AlgebraicGeometry.RingedSite.compositionMap_over` with the restriction comparison of the total
  tensor complex transposed to the other side, so that it reads as a factorisation of the
  restricted composition morphism.
* `AlgebraicGeometry.RingedSite.homologyMap_compositionMap_over`: **the map induced on
  cohomology sheaves by the composition morphism commutes with restriction to a slice site.**

## Implementation notes

Both statements are transpositions of `AlgebraicGeometry.RingedSite.compositionMap_over`, which
carries all the mathematics: the first by `CategoryTheory.Iso.inv_comp_eq`, the second by the
naturality of the exactness comparison `Stacks.Homology.exactHomologyIso` of the restriction
functor together with functoriality of `HomologicalComplex.homologyMap`. Nothing is recomputed on
local sections.

The exactness and additivity of restriction are supplied as local instances, for the reason
recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexHomologySliceRestriction`.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  HomologicalComplex.homologyFunctor
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

attribute [local instance] Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor

-- Restriction to a slice site is additive by the global instance
-- `AlgebraicGeometry.RingedSite.overFunctor_additive`
-- (StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/RestrictionOfComplexes.lean:47); left and
-- right exactness are the named theorems of Stacks 04IX, made local instances here.
attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-- **The restricted composition morphism, factored through the restriction comparisons.** The
restriction of the composition morphism of Stacks 0A91, followed by the comparison identifying
its target with the internal Hom complex formed over `U`, is the comparison identifying its
source with the total tensor complex formed over `U`, followed by the composition morphism over
`U` of the restricted complexes.

This is `AlgebraicGeometry.RingedSite.compositionMap_over` with the comparison of the total
tensor complexes transposed; it is the form in which a map induced on cohomology is read off. -/
theorem compositionMap_over' :
    ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (compositionMap X K L M) ≫
        (sheafHomRestrictionComplexIso X U K M).hom =
      (tensorTotalOverIso X U (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj).hom ≫
        tensorTotalMap (X.over U) (sheafHomRestrictionComplexIso X U L M).hom
            (sheafHomRestrictionComplexIso X U K L).hom ≫
          compositionMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
            (restrictComplex X M U) :=
  (Iso.inv_comp_eq
    (tensorTotalOverIso X U (sheafHomComplex X L M).obj
      (sheafHomComplex X K L).obj)).1 (compositionMap_over X U K L M)

/-- **The map induced on cohomology sheaves by the composition morphism of internal Hom complexes
commutes with restriction to a slice site.** Restricting

`Hⁿ(Tot(SheafHom(L, M) ⊗ SheafHom(K, L))) ⟶ Hⁿ(SheafHom(K, M))`

to the site over `U` and identifying its source and its target with the ones formed over `U`
gives the corresponding map over `U`, for the restricted complexes.

The target comparison is `AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso`; the source one is
the exactness comparison of the restriction functor followed by the cohomology of the restriction
comparison of the total tensor complex, written out rather than named, the total tensor complex
having no composition datum of its own. -/
theorem homologyMap_compositionMap_over (n : ℤ) :
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          (HomologicalComplex.homologyMap (compositionMap X K L M) n) ≫
        (sheafHomHomologyOverIso X U K M n).hom =
      (Stacks.Homology.exactHomologyIso
            (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
            n).inv.app
          (tensorTotal X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj) ≫
        HomologicalComplex.homologyMap
          ((tensorTotalOverIso X U (sheafHomComplex X L M).obj
                (sheafHomComplex X K L).obj).hom ≫
            tensorTotalMap (X.over U) (sheafHomRestrictionComplexIso X U L M).hom
                (sheafHomRestrictionComplexIso X U K L).hom ≫
              compositionMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
                (restrictComplex X M U)) n := by
  have hnat : (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          (HomologicalComplex.homologyMap (compositionMap X K L M) n) ≫
        (Stacks.Homology.exactHomologyIso
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) n).inv.app
            (sheafHomComplex X K M).obj =
      (Stacks.Homology.exactHomologyIso
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) n).inv.app
            (tensorTotal X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj) ≫
        HomologicalComplex.homologyMap
          (((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (compositionMap X K L M)) n :=
    (Stacks.Homology.exactHomologyIso
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
      n).inv.naturality
        (compositionMap X K L M)
  refine (congrArg
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      (HomologicalComplex.homologyMap (compositionMap X K L M) n) ≫ ·)
    (sheafHomHomologyOverIso_hom X U K M n)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ HomologicalComplex.homologyMap
    (sheafHomRestrictionComplexIso X U K M).hom n) hnat).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyFunctor _ _ n).map (compositionMap_over' X U K L M)))

end AlgebraicGeometry.RingedSite

end
