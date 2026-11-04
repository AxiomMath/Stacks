module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomRestrictionIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# The evaluation morphism of Stacks 0A92 and restriction to a localized ringed site

Let `X` be a ringed site, `U` an object of its underlying category and `K`, `L`, `M` complexes of
`O`-modules. The evaluation morphism of Stacks 0A92

`Tot(SheafHom(L, M) ⊗_O K) ⟶ SheafHom(SheafHom(K, L), M)`

is compatible with restriction to the localized ringed site of Stacks 04IX: its restriction to
the site over `U` is the evaluation morphism formed there, out of the restrictions of `K`, `L`
and `M`, read through the comparisons identifying the restriction of each complex involved with
the corresponding complex formed over `U`.

## Main results

* `AlgebraicGeometry.RingedSite.evaluationMap_restrict_square`: the square.

## Implementation notes

The square is stated with the two Hom comparisons on the same side rather than inverted: on the
target the inner one is contravariant, so the composite of the evaluation morphism over `U` with
`homMap` of that comparison lands in the internal Hom complex out of the *restriction* of
`SheafHom(K, L)`, which is where the restriction of the ambient evaluation morphism lands as
well.

## References

* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Lemma 20.50.4 (Tag 0G40)](https://stacks.math.columbia.edu/tag/0G40)
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

variable
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The evaluation morphism of Stacks 0A92 commutes with restriction to a localized ringed
site.** Restricting

`Tot(SheafHom(L, M) ⊗_O K) ⟶ SheafHom(SheafHom(K, L), M)`

to the site over `U` and following it with the comparison identifying the restriction of its
target with an internal Hom complex over `U` is the same as first identifying the restriction of
its source with `Tot(SheafHom(L|_U, M|_U) ⊗ K|_U)`, then applying the evaluation morphism formed
over `U`, and finally restricting along the comparison of the inner internal Hom complex. -/
theorem evaluationMap_restrict_square :
    (tensorTotalOverIso X U (sheafHomComplex X L M).obj K).inv ≫
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (evaluationMap X K L M) ≫
          (derivedHomRestriction X U).complexMap (sheafHomComplex X K L).obj M =
      tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap L M)
          (𝟙 (restrictComplex X K U)) ≫
        evaluationMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
            (restrictComplex X M U) ≫
          homMap (X.over U) ((derivedHomRestriction X U).complexMap K L)
            (𝟙 (restrictComplex X M U)) := by
  refine tensorTotalHomSection_ext (X.over U) fun W₁ W₂ i t r a q haq x y z ↦ ?_
  simp only [HomologicalComplex.comp_f, comp_val_app_apply]
  refine Eq.trans ?_ (applyHomSectionOver_homMap (X.over U)
    ((derivedHomRestriction X U).complexMap K L) (𝟙 (restrictComplex X M U))
    W₁ W₂ i (t + r) a q haq _ z).symm
  have tensorImages := tensorTotalMap_tensorTotalSection (X.over U)
    ((derivedHomRestriction X U).complexMap L M) (𝟙 (restrictComplex X K U)) W₁ t r x y
  have evaluationImages := (congrArg
    (((evaluationMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
      (restrictComplex X M U)).f (t + r)).val.app (op W₁)) tensorImages).trans
        (evaluationMap_tensorTotalSection (X.over U) (restrictComplex X K U)
          (restrictComplex X L U) (restrictComplex X M U) W₁ t r
          ((((derivedHomRestriction X U).complexMap L M).f t).val.app (op W₁) x) y)
  refine Eq.trans ?_ (congrArg (fun sectionValue => applyHomSectionOver (X.over U)
    (sheafHomComplex (X.over U)
      (sheafHomComplex (X.over U) (restrictComplex X K U) (restrictComplex X L U)).obj
      (restrictComplex X M U)) W₁ W₂ i (t + r) a q haq sectionValue
      ((((derivedHomRestriction X U).complexMap K L).f a).val.app (op W₂) z))
    evaluationImages).symm
  refine Eq.trans ?_ (evaluationSectionAt_applyOver (X.over U) W₁ W₂ i
    t r (t + r) a (r + a) q rfl rfl (by omega)
    ((((derivedHomRestriction X U).complexMap L M).f t).val.app (op W₁) x) y
    ((((derivedHomRestriction X U).complexMap K L).f a).val.app (op W₂) z)).symm
  refine Eq.trans (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U)
    (sheafHomComplex X K L).obj M (op W₁) (op (Over.mk i)) (t + r) a q haq _ z) ?_
  have restrictedTensorImage := tensorTotalOverIso_inv_tensorTotalSectionAt X U
    (sheafHomComplex X L M).obj K W₁ t r (t + r) rfl x y
  have restrictedEvaluationImage := congrArg
    (((((SheafOfModules.overFunctor.{u} (ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (evaluationMap X K L M)).f (t + r)).val.app (op W₁)) restrictedTensorImage
  refine Eq.trans (congrArg (fun sectionValue => applyHomSectionOver X
    (sheafHomComplex X (sheafHomComplex X K L).obj M) (Over.left W₁) (Over.left W₂)
    (Over.Hom.left i) (t + r) a q haq sectionValue z) restrictedEvaluationImage) ?_
  refine Eq.trans (congrArg (fun w ↦ applyHomSectionOver X
    (sheafHomComplex X (sheafHomComplex X K L).obj M) (Over.left W₁) (Over.left W₂)
    (Over.Hom.left i) (t + r) a q haq w z)
    (evaluationMap_tensorTotalSection X K L M (Over.left W₁) t r x y)) ?_
  refine Eq.trans (evaluationSectionAt_applyOver X (Over.left W₁) (Over.left W₂)
    (Over.Hom.left i) t r (t + r) a (r + a) q rfl rfl (by omega) x y z) ?_
  refine congrArg (fun w ↦ (r + -(r + a) * r).negOnePow • w) ?_
  refine Eq.trans ?_ (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U)
    L M (op W₁) (op (Over.mk i)) t (r + a) q (by omega) x _).symm
  refine congrArg (fun w ↦ applyHomSectionOver X (sheafHomComplex X L M) (Over.left W₁)
    (Over.left W₂) (Over.Hom.left i) t (r + a) q (by omega) x w) ?_
  exact (DerivedHomRestriction.complexMap_apply X U (derivedHomRestriction X U) K L
    (op W₂) (op (Over.mk (𝟙 W₂))) a r (r + a) rfl z _).symm

end AlgebraicGeometry.RingedSite

end
