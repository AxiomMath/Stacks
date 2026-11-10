module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomRestrictionIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# The interchange morphism of Stacks 0BYR and restriction to a localized ringed site

Let `X` be a ringed site, `U` an object of its underlying category and `A`, `I`, `N` complexes of
`O`-modules. This file proves that the interchange morphism of Stacks 0BYR

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

is compatible with restriction to the localized ringed site of Stacks 04IX: its restriction to
the site over `U` is the interchange morphism formed there, out of the restrictions of `A`, `I`
and `N`, conjugated by the comparisons identifying the restriction of each of its two complexes
with the corresponding complex formed over `U`.

This is the one statement that the reduction of Stacks 0ATN to a local condition needs and that
the development did not have; the module constructing the diagonal of Stacks 0BYS at arbitrary
models records its absence.

## Main results

* `AlgebraicGeometry.RingedSite.tensorHomInterchange_restrict_square`: the square.

## Implementation notes

Each of the two complexes of the interchange morphism needs two comparisons, and they are the
ones already available: on the source,
`AlgebraicGeometry.RingedSite.tensorTotalOverIso` for the tensor product followed by the
functoriality of the total tensor complex in the internal Hom factor; on the target, the
restriction comparison of internal Hom complexes followed by the functoriality of the internal
Hom complex in its target.

The restriction comparison of internal Hom complexes used here is
`AlgebraicGeometry.RingedSite.DerivedHomRestriction.complexMap` rather than
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso`, because what it does on local
sections is public — that is `DerivedHomRestriction.complexMap_apply` of Stacks 08JB — and the
proof is a computation on local sections. Its invertibility, which a consumer of the square
needs and which is not part of the structure, is
`AlgebraicGeometry.RingedSite.isIso_of_isInternalHomRestrictionMap` applied to
`derivedHomRestriction_complexMap_isRestriction`; that holds at the complex `Tot(A ⊗_O I)`,
which is not known to be K-injective, and the `model` field of the structure would not reach it.

The proof is `AlgebraicGeometry.RingedSite.tensorTotalHomSection_ext`: a morphism out of a total
tensor complex into an internal Hom complex is determined by the evaluations of the images of the
homogeneous local pure tensors. Each side is then computed by the formula pinning the morphism it
is built from — the interchange morphism by
`tensorHomInterchange_applyHomSectionOver`, the two tensor comparisons by
`tensorTotalOverIso_inv_tensorTotalSectionAt` and its direct form, the two Hom comparisons by
`complexMap_apply`, and the functorialities by `tensorTotalMap_tensorTotalSection` and
`applyHomSectionOver_homMap` — and the two meet.

Two of those formulas are stated in the `sectionsIso` vocabulary and the goal is in the
`applyHomSectionOver` vocabulary; the two are the same by definition but not syntactically, so
those steps are taken by `Eq.trans` against an instantiated equation rather than by `rw`, which
cannot match across the gap.

## References

* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor Stacks.SheafOfModules.UliftTensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.tensorComplex
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

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor X.O).Additive] [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive] [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]


variable (A I N :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The interchange morphism of Stacks 0BYR commutes with restriction to a localized ringed
site.** Restricting

`Tot(A ⊗_O SheafHom(N, I)) ⟶ SheafHom(N, Tot(A ⊗_O I))`

to the site over `U` and following it with the comparisons identifying the restriction of its
target with `SheafHom(N|_U, Tot(A|_U ⊗ I|_U))` is the same as first identifying the restriction
of its source with `Tot(A|_U ⊗ SheafHom(N|_U, I|_U))` and then applying the interchange morphism
formed over `U`.

Both sides are morphisms out of a total tensor complex into an internal Hom complex, so they are
determined by the evaluations of the images of the homogeneous local pure tensors, and on such an
evaluation each side comes to the same thing: the pure tensor of the restricted first factor with
the value of the restricted Hom-section. -/
theorem tensorHomInterchange_restrict_square :
    ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (tensorHomInterchange X A I N) ≫
        (derivedHomRestriction X U).complexMap N (tensorTotal X A I) ≫
          homMap (X.over U) (𝟙 (restrictComplex X N U))
            (tensorTotalOverIso X U A I).hom =
      (tensorTotalOverIso X U A (sheafHomComplex X N I).obj).hom ≫
        tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
          ((derivedHomRestriction X U).complexMap N I) ≫
          tensorHomInterchange (X.over U) (restrictComplex X A U) (restrictComplex X I U)
            (restrictComplex X N U) := by
  apply (Iso.inv_comp_eq (tensorTotalOverIso X U A (sheafHomComplex X N I).obj)).mp
  refine tensorTotalHomSection_ext (X.over U)
    fun W₁ W₂ i t r b q hbq x φ z ↦ ?_
  have tensorImages := tensorTotalMap_tensorTotalSection (X.over U)
    (𝟙 (restrictComplex X A U)) ((derivedHomRestriction X U).complexMap N I) W₁ t r x φ
  have interchangeImages := congrArg
    (((tensorHomInterchange (X.over U) (restrictComplex X A U) (restrictComplex X I U)
      (restrictComplex X N U)).f (t + r)).val.app (op W₁)) tensorImages
  refine Eq.trans ?_ (congrArg (fun sectionValue => applyHomSectionOver (X.over U)
    (sheafHomComplex (X.over U) (restrictComplex X N U)
      (tensorTotal (X.over U) (restrictComplex X A U) (restrictComplex X I U)))
    W₁ W₂ i (t + r) b q hbq sectionValue z) interchangeImages).symm
  refine Eq.trans ?_ (tensorHomInterchange_applyHomSectionOver (X.over U) (restrictComplex X A U)
    (restrictComplex X I U) (restrictComplex X N U) W₁ W₂ i t r b (b + r) q rfl (by omega)
    x ((((derivedHomRestriction X U).complexMap N I).f r).val.app (op W₁) φ) z).symm
  refine Eq.trans (applyHomSectionOver_homMap (X.over U) (𝟙 (restrictComplex X N U))
    (tensorTotalOverIso X U A I).hom W₁ W₂ i (t + r) b q hbq _ z) ?_
  refine Eq.trans (congrArg (ModuleCat.Hom.hom _)
    (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U) N
      (tensorTotal X A I) (op W₁) (op (Over.mk i)) (t + r) b q hbq _ _)) ?_
  have restrictedTensorImage := tensorTotalOverIso_inv_tensorTotalSectionAt X U
    A (sheafHomComplex X N I).obj W₁ t r (t + r) rfl x φ
  have restrictedInterchangeImage := congrArg
    (((((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (tensorHomInterchange X A I N)).f (t + r)).val.app (op W₁))
    restrictedTensorImage
  refine Eq.trans (congrArg (fun sectionValue =>
    ((tensorTotalOverIso X U A I).hom.f q).val.app (op W₂)
      (applyHomSectionOver X (sheafHomComplex X N (tensorTotal X A I))
        (Over.left W₁) (Over.left W₂) (Over.Hom.left i) (t + r) b q hbq sectionValue z))
      restrictedInterchangeImage) ?_
  refine Eq.trans (congrArg (ModuleCat.Hom.hom _)
    (tensorHomInterchange_applyHomSectionOver X A I N (Over.left W₁) (Over.left W₂)
      (Over.Hom.left i) t r b (b + r) q rfl (by omega) x φ z)) ?_
  refine Eq.trans (tensorTotalOverIso_hom_tensorTotalSectionAt X U A I W₂
    t (b + r) q (by omega) _ _) ?_
  refine congrArg₂ (fun a' φ' => tensorTotalSectionAt (X.over U) (restrictComplex X A U)
      (restrictComplex X I U) W₂ t (b + r) q (by omega) a' φ') rfl ?_
  exact (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U) N I
    (op W₁) (op (Over.mk i)) r b (b + r) rfl φ z).symm

end AlgebraicGeometry.RingedSite

end
