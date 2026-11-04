module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# The total tensor-product complex and restriction to a localized ringed site

Let `X` be a ringed site, `U` an object of its underlying category and `A`, `B` complexes of
`O`-modules. This file records

`(Tot(A ⊗_O B))|_U ≅ Tot(A|_U ⊗_{O|_U} B|_U)`,

the compatibility of `AlgebraicGeometry.RingedSite.tensorTotal` with restriction to the
localized ringed site `AlgebraicGeometry.RingedSite.over` of Stacks 04IX.

Nothing of the mathematics is new. The same statement for the other construction of the total
tensor complex, `Stacks.SheafOfModules.Tensor.tensorComplex`, is
`AlgebraicGeometry.RingedSite.tensorComplexOverIso`; the two constructions are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`; and this is the conjugate of the
one by the other. It is stated because every consumer of the total tensor complex in this
development is phrased in terms of `tensorTotal`, and because the restriction compatibility of
the interchange morphism of Stacks 0BYR — which the reduction of Stacks 0ATN to a local
statement needs — cannot even be *stated* without it.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalOverIso`: the isomorphism above.

## Main results

* `AlgebraicGeometry.RingedSite.map_tensorTotalIsoTensorComplex_hom_tensorComplexOverIso` and
  `AlgebraicGeometry.RingedSite.map_tensorTotalIsoTensorComplex_inv_tensorTotalOverIso`: **the
  comparison of the two total tensor complexes commutes with restriction to a slice site.**
  These are transpositions of the definition of `tensorTotalOverIso`, stated because a morphism
  defined out of the *other* total tensor complex — the one the cohomology product of
  `CochainComplex.tensorHomology` uses — has no other way past restriction.

## What this file does not contain

**A description of the isomorphism on the local pure tensors.** Every identity in this
development between morphisms out of a total tensor complex is proved by testing on the
homogeneous local pure tensors, so a consumer needs to know that this isomorphism carries the
pure tensor of `a` and `b` to the pure tensor of their restrictions. That is true and is
reachable — `ι_totalMapf` describes the comparison of a functor with a total complex on a
summand, `HomologicalComplex₂.ιTotal_map` describes the map of total complexes induced by a map
of bicomplexes, and `AlgebraicGeometry.RingedSite.sheafTensorOverIso` is built by
`AlgebraicGeometry.RingedSite.isoOfUnits`, whose characterisation on a presheaf-level section is
`AlgebraicGeometry.RingedSite.comp_liftOfUnit` — but it is four such steps and it is not done
here. Until it is, this isomorphism can be composed with others but nothing can be computed
through it.

## Implementation notes

Sheaves of modules on the localized site are indexed by `(X.over U).ringSheaf` here and by
`X.ringSheaf.over U` in `AlgebraicGeometry.RingedSite.restrictComplex`; the two are the same
object but not reducibly so. The tensor comparisons therefore receive the existing slice
sheafification, additivity, and totalization dictionaries explicitly rather than introducing
another instance at the alternate coefficient spelling.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
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

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [sliceSheafify : HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [sliceLocallyBijective : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [sliceTensorAdditive : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [sliceTensorObjAdditive :
    ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)),
    ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [sliceTensorHasMap : ∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The total tensor-product complex commutes with restriction to a localized ringed site.**
The restriction of `Tot(A ⊗_O B)` to the site over `U` is the total tensor-product complex,
formed there, of the restrictions of `A` and `B`.

This is `AlgebraicGeometry.RingedSite.tensorComplexOverIso` — the same statement for the other
construction of the total tensor complex — conjugated on both sides by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`. -/
def tensorTotalOverIso :
    restrictComplex X (tensorTotal X A B) U ≅
      tensorTotal (X.over U) (restrictComplex X A U) (restrictComplex X B U) :=
  ((SheafOfModules.overFunctor.{u}
     (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (tensorTotalIsoTensorComplex X A B) ≪≫
    tensorComplexOverIso X U A B ≪≫
    (@tensorTotalIsoTensorComplex.{u} (X.over U) sliceSheafify sliceLocallyBijective
      sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap (restrictComplex X A U)
      (restrictComplex X B U)).symm

/-- **The comparison of the two total tensor complexes commutes with restriction to a slice
site.** Restricting `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` and then
identifying the sheafified total tensor complex with the one formed over `U` is the same as
identifying the two total complexes over `U` after the restriction comparison of
`AlgebraicGeometry.RingedSite.tensorTotal`.

This is a transposition of the definition of
`AlgebraicGeometry.RingedSite.tensorTotalOverIso`, which is exactly that composite; it is
stated because a consumer holding a morphism defined out of the *other* total tensor complex —
`AlgebraicGeometry.RingedSite.compositionTotalMap` is the one — has no other way to move the
comparison past restriction. -/
theorem map_tensorTotalIsoTensorComplex_hom_tensorComplexOverIso :
    ((SheafOfModules.overFunctor.{u}
       (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (tensorTotalIsoTensorComplex X A B).hom ≫
        (tensorComplexOverIso X U A B).hom =
      (tensorTotalOverIso X U A B).hom ≫
        (@tensorTotalIsoTensorComplex.{u} (X.over U) sliceSheafify sliceLocallyBijective
          sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap (restrictComplex X A U)
          (restrictComplex X B U)).hom :=
  ((Category.comp_id _).symm.trans
      (congrArg
        (fun z => ((SheafOfModules.overFunctor.{u}
                     (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (tensorTotalIsoTensorComplex X A B).hom ≫
            (tensorComplexOverIso X U A B).hom ≫ z)
        ((@tensorTotalIsoTensorComplex.{u} (X.over U) sliceSheafify sliceLocallyBijective
          sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap (restrictComplex X A U)
          (restrictComplex X B U)).inv_hom_id).symm)).trans
    (Category.assoc _ _ _).symm

/-- **The inverse comparison of the two total tensor complexes commutes with restriction to a
slice site.** This is the form in which a morphism defined out of
`AlgebraicGeometry.RingedSite.tensorTotal` is read on the total tensor complex that
`CochainComplex.tensorHomology` uses. -/
theorem map_tensorTotalIsoTensorComplex_inv_tensorTotalOverIso :
    ((SheafOfModules.overFunctor.{u}
       (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (tensorTotalIsoTensorComplex X A B).inv ≫
        (tensorTotalOverIso X U A B).hom =
      (tensorComplexOverIso X U A B).hom ≫
        (@tensorTotalIsoTensorComplex.{u} (X.over U) sliceSheafify sliceLocallyBijective
          sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap (restrictComplex X A U)
          (restrictComplex X B U)).inv := by
  apply (Iso.eq_comp_inv _).2
  have cancellation :=
    (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
        (tensorTotalIsoTensorComplex X A B)).inv_hom_id_assoc
          (tensorComplexOverIso X U A B).hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun morphism =>
      ((SheafOfModules.overFunctor.{u}
         (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (tensorTotalIsoTensorComplex X A B).inv ≫ morphism)
      (map_tensorTotalIsoTensorComplex_hom_tensorComplexOverIso X U A B).symm).trans cancellation)

end AlgebraicGeometry.RingedSite

end
