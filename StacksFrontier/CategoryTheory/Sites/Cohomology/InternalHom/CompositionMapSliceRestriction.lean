module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionSliceRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.RestrictionSections

/-!
# The composition morphism of internal Hom complexes commutes with restriction to a slice site

Let `X` be a ringed site, `U` an object of its underlying category and `K`, `L`, `M` complexes of
`O`-modules. Restriction to the slice site over `U` carries the three objects of the composition
morphism of Stacks 0A91 to the corresponding objects formed over `U`:

* the two internal Hom complexes, by `AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso`,
  which is the chain-level comparison of Stacks 08JB;
* the total tensor complex of its source, by
  `AlgebraicGeometry.RingedSite.tensorTotalOverIso`.

This file proves that the composition morphism is carried to the composition morphism:

`(β ∘ γ)|_U = β|_U ∘ γ|_U`

as an identity of morphisms of complexes of `O|_U`-modules, and not merely on local sections.
This is the input the gluing of a local-to-global statement about the composition product on
cohomology needs, the piecewise half of such a statement being the restriction comparison of the
Ext sheaves.

## Main results

* `AlgebraicGeometry.RingedSite.compositionMap_over`: **the composition morphism commutes with
  restriction to a slice site.**

## Implementation notes

A morphism out of a total tensor complex is determined by its values on the homogeneous local
pure tensors (`AlgebraicGeometry.RingedSite.tensorTotal_hom_ext`), so the identity is checked on
those, and on a pure tensor every morphism in sight is already computed:
`tensorTotalOverIso_inv_tensorTotalSectionAt` for the restriction comparison of the total tensor
complex, `tensorTotalMap_tensorTotalSection` for the map of total tensor complexes induced by the
two restriction comparisons, `compositionMap_tensorTotalSection` for the composition morphism on
both sites, and `compositionSection_sheafHomRestrictionComplexIso` for the restriction comparison
on a composite of sections. The identity then reads, on both sides, as the composite of the
restrictions of the two factors.

The equation is stated with the restriction comparison of the total tensor complex *inverted* on
the left, so that both sides are morphisms out of `Tot(SheafHom(L, M)|_U ⊗ SheafHom(K, L)|_U)`,
which is the object the extensionality principle is about. The two other forms follow by
cancelling that isomorphism.

Sheaves of modules on the slice site are indexed by `(X.over U).ringSheaf` here and by
`X.ringSheaf.over U` in `AlgebraicGeometry.RingedSite.restrictComplex`; the two are the same
object but not reducibly so, which is why the block of `implicit_reducible` attributes
prescribed by
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction` is in force, and
why the instance that the total complex of the slice site exists is transported by hand.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.RingedSite

universe u

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
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

attribute [local instance] Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor

/-- **The composition morphism of internal Hom complexes commutes with restriction to a slice
site.** Restricting the composition morphism of Stacks 0A91 to the slice site over `U`, and
identifying its source and its target with the ones formed over `U` — the source by
`AlgebraicGeometry.RingedSite.tensorTotalOverIso`, the target by
`AlgebraicGeometry.RingedSite.sheafHomRestrictionComplexIso` — gives the composition morphism
over `U` of the restricted complexes.

So the restriction of the composition product of internal Hom complexes *is* the composition
product of the restrictions, with no sign and no change of degree. -/
theorem compositionMap_over :
    (tensorTotalOverIso X U (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj).inv ≫
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (compositionMap X K L M) ≫
          (sheafHomRestrictionComplexIso X U K M).hom =
      tensorTotalMap (X.over U) (sheafHomRestrictionComplexIso X U L M).hom
          (sheafHomRestrictionComplexIso X U K L).hom ≫
        compositionMap (X.over U) (restrictComplex X K U) (restrictComplex X L U)
          (restrictComplex X M U) := by
  refine tensorTotal_hom_ext (X.over U) fun W t r β γ ↦ ?_
  simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change ((sheafHomRestrictionComplexIso X U K M).hom.f (t + r)).val.app (op W)
    (((((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (compositionMap X K L M)).f (t + r)).val.app (op W)
      (((tensorTotalOverIso X U (sheafHomComplex X L M).obj
        (sheafHomComplex X K L).obj).inv.f (t + r)).val.app (op W)
        ((X.over U).tensorTotalSection (restrictComplex X (sheafHomComplex X L M).obj U)
          (restrictComplex X (sheafHomComplex X K L).obj U) W t r β γ))) = _
  rw [tensorTotalMap_tensorTotalSection (X.over U)
      (sheafHomRestrictionComplexIso X U L M).hom
      (sheafHomRestrictionComplexIso X U K L).hom W t r β γ,
    compositionMap_tensorTotalSection (X.over U) (restrictComplex X K U)
      (restrictComplex X L U) (restrictComplex X M U) W t r _ _,
    ← tensorTotalSectionAt_self (X.over U) (restrictComplex X (sheafHomComplex X L M).obj U)
      (restrictComplex X (sheafHomComplex X K L).obj U) W t r β γ,
    tensorTotalOverIso_inv_tensorTotalSectionAt X U (sheafHomComplex X L M).obj
      (sheafHomComplex X K L).obj W t r (t + r) rfl β γ]
  exact (congrArg
      (fun z => ((sheafHomRestrictionComplexIso X U K M).hom.f (t + r)).val.app (op W) z)
      (compositionMap_tensorTotalSection X K L M W.left t r β γ)).trans
    (compositionSection_sheafHomRestrictionComplexIso X U K L M W t r (t + r) rfl β γ)

end AlgebraicGeometry.RingedSite

end
