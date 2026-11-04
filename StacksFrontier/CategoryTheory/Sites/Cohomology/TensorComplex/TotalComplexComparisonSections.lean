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
sheafification unit, which is `AlgebraicGeometry.RingedSite.sheafification_map_unit_apply`. The
two bicomplexes involved are definitionally equal, by
`AlgebraicGeometry.RingedSite.mapBicomplex_presheafTensorBicomplex`, so nothing has to be
transported.

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
    (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
    (presheafTensorBicomplex X A B) c t r
    (show ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c
      by simpa using h)
  have key := congrArg
    (fun z => z.val.app (op W)
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        _).app (op W) (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] b))) e
  refine Eq.trans key ?_
  exact sheafification_map_unit_apply X _ (op W) _

end AlgebraicGeometry.RingedSite

end
