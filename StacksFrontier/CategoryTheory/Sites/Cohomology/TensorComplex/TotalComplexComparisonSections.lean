module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexShift

/-!
# The two total tensor-product complexes agree on the local pure tensors

Let `X` be a ringed site and `A`, `B` complexes of `O`-modules. This development has two
constructions of their total tensor-product complex, identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`: one totalises the bicomplex of
pointwise tensor products of the underlying presheaves and then sheafifies degreewise
(`AlgebraicGeometry.RingedSite.tensorTotal`), the other sheafifies degreewise and then
totalises (`Stacks.SheafOfModules.Tensor.tensorComplex`). Each comes with its own notion of a
homogeneous local pure tensor — `AlgebraicGeometry.RingedSite.tensorTotalSectionAt` and
`AlgebraicGeometry.RingedSite.tensorComplexSection` — and the two differ in the order in which
the summand inclusion and the sheafification unit are applied.

This file proves that the identification matches them up. That is needed because every identity
in this development between morphisms out of a total tensor complex is proved by testing on the
pure tensors, so a computation that has to pass through `tensorTotalIsoTensorComplex` — for
instance one passing through
`AlgebraicGeometry.RingedSite.tensorTotalOverIso`, which is built by conjugating a statement
about `tensorComplex` — cannot proceed without it.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex_inv_tensorComplexSection`: the
  identification carries the pure tensor of one construction to the pure tensor of the other.

## Implementation notes

The statement is proved in the direction of the *inverse* of
`tensorTotalIsoTensorComplex`, because that is the direction in which the comparison of a
functor with a total complex is *defined*: the source is a coproduct, so
`HomologicalComplex₂.TotalMap.ι_totalMapf` describes it on each summand, while the inverse has
no such description. The direction stated here is therefore the one that needs no transposition;
a consumer wanting the other direction applies the isomorphism to both sides.

The whole proof is the summand description of that comparison, followed by the naturality of the
unit of `Stacks.SheafOfModules.Tensor.sheafification`, the sheafification inside
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is
`Stacks.SheafOfModules.Tensor.unit_naturality_apply`. What is left is the passage from that
sealed sheafification to Mathlib's `PresheafOfModules.sheafification`, the one `tensorTotal` uses:
the comparison of the two that the defining equation
`Stacks.SheafOfModules.Tensor.sheafification_def` provides carries the sealed unit to Mathlib's.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section SheafificationComparison

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison of `Stacks.SheafOfModules.Tensor.sheafification` with Mathlib's
`PresheafOfModules.sheafification` given by the defining equation
`Stacks.SheafOfModules.Tensor.sheafification_def` carries the sealed sheafification unit to
Mathlib's. -/
private lemma unit_comp_map_eqToIso_sheafification_def_hom_app
    (M : PresheafOfModules.{u} (ringSheaf X.O).obj) :
    (sheafificationAdjunction X.O).unit.app M ≫
        (SheafOfModules.forget (ringSheaf X.O) ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
          ((eqToIso (sheafification_def X.O)).hom.app M) =
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf X.O).obj)).unit.app M := by
  rw [Stacks.SheafOfModules.Tensor.sheafificationAdjunction, Adjunction.ofNatIsoLeft,
    NatTrans.comp_app, Category.assoc, Functor.whiskerRight_app, ← Functor.map_comp,
    ← NatTrans.comp_app, eqToIso.hom, eqToIso.hom, eqToHom_trans, eqToHom_refl, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- `unit_comp_map_eqToIso_sheafification_def_hom_app` on sections. -/
private lemma eqToIso_sheafification_def_hom_app_unit_apply
    (M : PresheafOfModules.{u} (ringSheaf X.O).obj) (U : X.Cᵒᵖ) (x : M.obj U) :
    ((eqToIso (sheafification_def X.O)).hom.app M).val.app U
        (((sheafificationAdjunction X.O).unit.app M).app U x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf X.O).obj)).unit.app M).app U x :=
  PresheafOfModules.hom_congr_apply' (unit_comp_map_eqToIso_sheafification_def_hom_app X M) U x

end SheafificationComparison

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive] [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The two total tensor-product complexes agree on the local pure tensors.** The inverse of
the identification `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` carries the
homogeneous local pure tensor of `Stacks.SheafOfModules.Tensor.tensorComplex` — the
sheafification unit of the pointwise tensor product followed by the inclusion of the `(t, r)`
summand — to that of `AlgebraicGeometry.RingedSite.tensorTotal` — the inclusion of the `(t, r)`
summand at the level of presheaves followed by the sheafification unit.

The two are the same section for the same reason the two complexes are the same complex: the
comparison is induced out of a coproduct by the sheafifications of the summand inclusions, and
the unit is natural. -/
lemma tensorTotalIsoTensorComplex_inv_tensorComplexSection
    (W : X.C) (t r c : ℤ) (h : t + r = c)
    (a : (A.X t).val.obj (op W)) (b : (B.X r).val.obj (op W)) :
    ((tensorTotalIsoTensorComplex X A B).inv.f c).val.app (op W)
        (tensorComplexSection X t r c h a b) =
      tensorTotalSectionAt X A B W t r c h a b := by
  have e := HomologicalComplex₂.TotalMap.ι_totalMapf
    (Stacks.SheafOfModules.Tensor.sheafification X.O) (presheafTensorBicomplex X A B) c t r
    (show ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c
      by simpa using h)
  exact (congrArg (fun z ↦ ((eqToIso (sheafification_def X.O)).hom.app _).val.app (op W)
      (z.val.app (op W) (((sheafificationAdjunction X.O).unit.app _).app (op W)
        (a ⊗ₜ[(ringSheaf X.O).obj.obj (op W)] b)))) e).trans <|
    (congrArg _ (unit_naturality_apply _ (op W) _)).trans
      (eqToIso_sheafification_def_hom_app_unit_apply X _ (op W) _)

end AlgebraicGeometry.RingedSite

end
