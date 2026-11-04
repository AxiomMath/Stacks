module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CochainEvaluationLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections

/-! # The cochain-level evaluation morphism in the `tensorTotal` spelling

Two total tensor-product complexes of complexes of `O`-modules on a ringed site occur in this
development: `AlgebraicGeometry.RingedSite.tensorTotal`, the total complex of the double complex
of *presheaf* tensor products with sheafification applied afterwards, and
`Stacks.SheafOfModules.Tensor.tensorComplex`, the total complex of the double complex of sheaf
tensor products.  They are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, which matches the two homogeneous
local pure tensors (`AlgebraicGeometry.RingedSite.tensorTotalSectionAt` and
`AlgebraicGeometry.RingedSite.tensorComplexSection`).

The composition morphism of Stacks 0A8V and the evaluation morphism of Stacks 0A8P live over
`tensorTotal`, and the cochain-level evaluation morphism of Tag 0A90,
`AlgebraicGeometry.RingedSite.cochainEvaluation`, lives over `tensorComplex`.  This file carries
the local-section formula of
`AlgebraicGeometry.RingedSite.cochainEvaluation_val_app_tensorComplexSection` across that
identification, so that the two can be compared without re-deriving either.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_hom_tensorTotalSectionAt`: the
  forward direction of the comparison on local pure tensors, the companion of
  `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_inv_tensorComplexSection`.
* `AlgebraicGeometry.RingedSite.totalCochainEvaluation`: the cochain-level evaluation morphism
  `tensorTotal(SheafHom(B, D), B) ⟶ D` in the `tensorTotal` spelling.
* `AlgebraicGeometry.RingedSite.totalCochainEvaluation_val_app_tensorTotalSectionAt`: **it
  evaluates a homogeneous local pure tensor `ξ ⊗ l` to `ξ(l)`**, with no sign.

## Nothing here is tagged

Tag 0A90 is `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`, which carries the tag.  What
is below is a change of spelling of a step of the proof of Tag 0GM7, and carries no tag.

## Implementation notes

The forward direction of the comparison on local pure tensors is deduced from the inverse
direction by applying the forward map to both sides, rather than re-running the coproduct
argument: the identification is an isomorphism of complexes, so one `Iso.inv_hom_id_app`-style
step suffices, and the composition of morphisms of sheaves of modules acts on sections by
composition definitionally (`comp_val_app_apply_total` below, a `rfl`).

A note in `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluationSource`
says this comparison "is not available on this branch".  That is **false**:
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` is in
`StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison` with its
naturality, and its compatibility with the local pure tensors is in
`StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections`.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

/-- Composition of morphisms of sheaves of modules on sections.  Stated with every object a
variable, so that each use is one definitional-equality check. -/
private lemma comp_val_app_apply_total {X : RingedSite.{u, u, u}}
    {P Q R : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : P ⟶ Q)
    (ψ : Q ⟶ R) (W : X.Cᵒᵖ) (x : P.val.obj W) :
    ((φ ≫ ψ).val.app W) x = (ψ.val.app W) ((φ.val.app W) x) := rfl

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The comparison of the two total tensor-product complexes on local pure tensors, forward
direction.**  `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` carries the homogeneous
local pure tensor of `tensorTotal` to that of `tensorComplex`.

This is the companion of
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_inv_tensorComplexSection`, deduced
from it by applying the forward map. -/
theorem tensorTotalIsoTensorComplex_hom_tensorTotalSectionAt
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op W)) (b : (B.X r).val.obj (op W)) :
    ((tensorTotalIsoTensorComplex X A B).hom.f c).val.app (op W)
        (tensorTotalSectionAt X A B W t r c h a b) =
      tensorComplexSection X t r c h a b := by
  have hiv := congrArg (fun y => ((tensorTotalIsoTensorComplex X A B).hom.f c).val.app (op W) y)
    (tensorTotalIsoTensorComplex_inv_tensorComplexSection X A B W t r c h a b)
  refine hiv.symm.trans ?_
  rw [← comp_val_app_apply_total ((tensorTotalIsoTensorComplex X A B).inv.f c)
    ((tensorTotalIsoTensorComplex X A B).hom.f c) (op W) (tensorComplexSection X t r c h a b),
    ← HomologicalComplex.comp_f, (tensorTotalIsoTensorComplex X A B).inv_hom_id,
    HomologicalComplex.id_f]
  rfl

variable (B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The cochain-level evaluation morphism of Tag 0A90, in the `tensorTotal` spelling.**  The
morphism `tensorTotal(SheafHom(B, D), B) ⟶ D` obtained from
`AlgebraicGeometry.RingedSite.cochainEvaluation` by the comparison of the two total
tensor-product complexes. -/
def totalCochainEvaluation :
    tensorTotal X (sheafHomComplex X B D).obj B ⟶ D :=
  (tensorTotalIsoTensorComplex X (sheafHomComplex X B D).obj B).hom ≫ cochainEvaluation X B D

/-- **The cochain-level evaluation morphism on homogeneous local pure tensors, in the
`tensorTotal` spelling.**  It takes the local pure tensor of a degree-`t` section `ξ` of
`SheafHom(B, D)` and a degree-`r` section `l` of `B` over an object `W` of the site to the value
`ξ(l)`: no sign, no restriction, no intervening identification.

This is the formula that lets the evaluation morphism of Tag 0A90 be compared with the
composition morphism of Stacks 0A8V, which lives over `tensorTotal` and whose own formula on
local pure tensors is `AlgebraicGeometry.RingedSite.compositionSection_apply`. -/
theorem totalCochainEvaluation_val_app_tensorTotalSectionAt
    (c t r : ℤ) (htr : t + r = c) (hrt : r + t = c) (W : X.C)
    (ξ : ((sheafHomComplex X B D).obj.X t).val.obj (op W))
    (l : (B.X r).val.obj (op W)) :
    ((totalCochainEvaluation X B D).f c).val.app (op W)
        (tensorTotalSectionAt X (sheafHomComplex X B D).obj B W t r c htr ξ l) =
      applyHomSection X (sheafHomComplex X B D) W t r c hrt ξ l := by
  rw [totalCochainEvaluation, HomologicalComplex.comp_f, comp_val_app_apply_total,
    tensorTotalIsoTensorComplex_hom_tensorTotalSectionAt X (sheafHomComplex X B D).obj B W t r c
      htr ξ l,
    cochainEvaluation_val_app_tensorComplexSection X B D c t r htr hrt W ξ l]

end AlgebraicGeometry.RingedSite

end
