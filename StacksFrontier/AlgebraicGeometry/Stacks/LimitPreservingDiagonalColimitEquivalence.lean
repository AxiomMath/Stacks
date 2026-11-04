module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeEvaluation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimit
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStagewiseEquivalence
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductEquivalence

/-!
# The comparison of the lower left corners of the two squares of Stacks 0CMW is an equivalence

`AlgebraicGeometry.Stack.colimitSplitFiberTwoFibreProductComparison` compares
`colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}` with `colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒵_{Uᵢ}`. It is the colimit of
the stagewise comparison `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison` followed
by the comparison `CategoryTheory.Cat.colimitTwoFibreProductComparison` out of the colimit of a
stagewise 2-fibre product, and this file proves that it is an equivalence when the index
category is cofiltered. Both factors are:

* the stagewise comparison is an equivalence at every stage by
  `AlgebraicGeometry.Stack.isEquivalence_splitFiberTwoFibreProductComparisonApp`, hence so is
  its colimit (`CategoryTheory.Cat.isEquivalence_colimMap`);
* the second is "filtered colimits of categories commute with 2-fibre products",
  `CategoryTheory.Cat.isEquivalence_colimitTwoFibreProductComparison`, which the source of
  Stacks 0CMW uses with the details omitted.

## Main results

* `AlgebraicGeometry.Stack.hasColimitsOfSize_sSet_fiberDiagram`: simplicial sets have the
  colimits the nerves of the diagrams of split fibres need.
* `AlgebraicGeometry.Stack.isEquivalence_colimitSplitFiberTwoFibreProductComparison`: the
  comparison is an equivalence.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **Simplicial sets have the colimits the nerves of the diagrams of split fibres need, at the
universes of Stacks 0CMW.** This is the companion of
`AlgebraicGeometry.Stack.hasColimitsOfSize_cat_fiberDiagram` for the nerve: the criteria of
`StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages` are stated for diagrams whose
nerves have colimits. -/
lemma hasColimitsOfSize_sSet_fiberDiagram :
    HasColimitsOfSize.{w, v} SSet.{max (u + 1) v w} :=
  hasColimitsOfSizeShrink.{w, v, max (u + 1) v w, max (u + 1) v w} _

/-- **The comparison of the lower left corners is an equivalence.** The split fibres of the base
change, taken stagewise into the stagewise 2-fibre product of the split fibres and then through
the colimit, land in the 2-fibre product of the colimits by an equivalence: the stagewise
comparison is one at every stage, and filtered colimits of categories commute with 2-fibre
products.

This is the input `[K.IsEquivalence]` of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer` for
the two squares of Stacks 0CMW. -/
lemma isEquivalence_colimitSplitFiberTwoFibreProductComparison (E : I ⥤ BigFppfOver B S hS)
    [IsFiltered Iᵒᵖ] :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E).IsEquivalence := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
  have : Functor.IsEquivalence
      (colimMap (splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)).toFunctor :=
    Cat.isEquivalence_colimMap.{max (u + 1) v w, v, w} _ fun j =>
      isEquivalence_splitFiberTwoFibreProductComparison_app B S hS 𝒳 𝒴 𝒵 p q E j
        (isEquivalence_splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q _)
  have : (Cat.colimitTwoFibreProductComparison
      (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
      (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).IsEquivalence :=
    Cat.isEquivalence_colimitTwoFibreProductComparison.{max (u + 1) v w, v, w} _ _
  exact inferInstanceAs (((colimMap
    (splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)).toFunctor ⋙
      Cat.colimitTwoFibreProductComparison
        (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
        (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).IsEquivalence)

end AlgebraicGeometry.Stack

end
