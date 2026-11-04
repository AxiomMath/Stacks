module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonProjections

/-!
# The two legs of the colimit comparison of a base change

The comparison `K` of Stacks 0CMW,

`colim (𝒳 ×_𝒴 𝒵)_{Uᵢ} ⥤ colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒵_{Uᵢ}`,

is `AlgebraicGeometry.Stack.colimitSplitFiberTwoFibreProductComparison`. This file computes its
two projections: they are the colimits of the diagrams of split fibres of the two projections of
the base change,

`K ⋙ π₁ = colim (π₁)_{Uᵢ}` and `K ⋙ π₂ = colim (p')_{Uᵢ}`.

The second of these says that `K` carries the left leg of the square of Stacks 0CMR for the base
change `p' = AlgebraicGeometry.BigFppfOver.twoFibreProductSnd` to the second projection of the
2-fibre product of the colimits; together with the first it exhibits `K` as the comparison functor
of the 2-commutative square of the colimits, which is what the pasting lemma of
`StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonPaste` consumes.

The computation is stagewise and needs no filteredness. At one stage it is
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_comp_π₁`, carried across the
universe lift of the cospan -- which acts on each component by the lift, so the projections are
unchanged. The passage from the stages to the colimit is
`CategoryTheory.Cat.colimitTwoFibreProductComparison_comp_π₁` followed by the functoriality of
`CategoryTheory.Limits.colimMap`.

## Main results

* `AlgebraicGeometry.BigFppfOver.fiberDiagramMap_twoFibreProductFst_comp_comparison` and `…Snd…`:
  the diagram-level identities.
* `AlgebraicGeometry.BigFppfOver.colimMap_twoFibreProductFst_comp_comparison` and `…Snd…`: the
  two projections of `K`.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **A stage of the diagram-level comparison, followed by the first projection.** The
stage is the componentwise comparison followed by the universe lift of the cospan, and a change of
cospan acts on each projection by its own component
(`CategoryTheory.Limits.CategoricalPullback.map_comp_π₁`), so the lift passes through. -/
lemma splitFiberTwoFibreProductComparisonStage_comp_π₁ (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j ⋙
        CategoricalPullback.π₁
          ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E).app j).toFunctor
          ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E).app j).toFunctor =
      (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q (E.obj j.unop) ⋙
        CategoricalPullback.π₁ (splitFiberMap B S hS p (E.obj j.unop))
          (splitFiberMap B S hS q (E.obj j.unop))) ⋙ AsSmall.up := rfl

/-- **A stage of the diagram-level comparison, followed by the second projection.** The
stage is the componentwise comparison followed by the universe lift of the cospan, and a change of
cospan acts on each projection by its own component
(`CategoryTheory.Limits.CategoricalPullback.map_comp_π₂`), so the lift passes through. -/
lemma splitFiberTwoFibreProductComparisonStage_comp_π₂ (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j ⋙
        CategoricalPullback.π₂
          ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E).app j).toFunctor
          ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E).app j).toFunctor =
      (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q (E.obj j.unop) ⋙
        CategoricalPullback.π₂ (splitFiberMap B S hS p (E.obj j.unop))
          (splitFiberMap B S hS q (E.obj j.unop))) ⋙ AsSmall.up := rfl

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The diagram of split fibres of the first projection, read at a stage.** The stagewise
comparison followed by the first projection of the lifted cospan is the universe lift of the
stagewise comparison followed by the first projection of the unlifted one, which is
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_comp_π₁`. -/
lemma fiberDiagramMap_twoFibreProductFst_comp_comparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E ≫
        Cat.twoFibreProductDiagramFst
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) =
      Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  refine NatTrans.ext (funext fun j => Cat.Hom.ext ?_)
  rw [NatTrans.comp_app, Cat.Hom.comp_toFunctor,
    show ((Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E).app j).toFunctor ⋙
        ((Cat.twoFibreProductDiagramFst
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).app
            j).toFunctor =
      AsSmall.down ⋙
        (Stack.splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j ⋙
          CategoricalPullback.π₁
            ((Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS p E).app j).toFunctor
            ((Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS q E).app j).toFunctor) from rfl,
    Stack.splitFiberTwoFibreProductComparisonStage_comp_π₁,
    Stack.splitFiberTwoFibreProductComparisonApp_comp_π₁]
  rfl

/-- **The diagram of split fibres of the second projection, read at a stage.** -/
lemma fiberDiagramMap_twoFibreProductSnd_comp_comparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E ≫
        Cat.twoFibreProductDiagramSnd
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) =
      Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  refine NatTrans.ext (funext fun j => Cat.Hom.ext ?_)
  rw [NatTrans.comp_app, Cat.Hom.comp_toFunctor,
    show ((Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E).app j).toFunctor ⋙
        ((Cat.twoFibreProductDiagramSnd
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).app
            j).toFunctor =
      AsSmall.down ⋙
        (Stack.splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j ⋙
          CategoricalPullback.π₂
            ((Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS p E).app j).toFunctor
            ((Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS q E).app j).toFunctor) from rfl,
    Stack.splitFiberTwoFibreProductComparisonStage_comp_π₂,
    Stack.splitFiberTwoFibreProductComparisonApp_comp_π₂]
  rfl

/-- **The first projection of the comparison `K` is the colimit of the diagram of split fibres of
the first projection.** -/
lemma colimMap_twoFibreProductFst_comp_comparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    Stack.colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E ⋙
        CategoricalPullback.π₁
          (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
            B S hS p E)).toFunctor
          (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
            B S hS q E)).toFunctor =
      (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have hcomp : colimMap (Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E) ≫
      colimMap (Cat.twoFibreProductDiagramFst
        (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
        (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)) =
      colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E) := by
    rw [← fiberDiagramMap_twoFibreProductFst_comp_comparison.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q E]
    refine colimit.hom_ext fun j => ?_
    rw [← Category.assoc, ι_colimMap, Category.assoc, ι_colimMap, ι_colimMap]
    exact (Category.assoc _ _ _).symm
  have h := congrArg Cat.Hom.toFunctor hcomp
  rw [Cat.Hom.comp_toFunctor] at h
  refine Eq.trans ?_ h
  rw [show Stack.colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E =
      (colimMap (Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)).toFunctor ⋙
        Cat.colimitTwoFibreProductComparison
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) from rfl,
    Functor.assoc, Cat.colimitTwoFibreProductComparison_comp_π₁]

/-- **The second projection of the comparison `K` is the colimit of the diagram of split fibres of
the base change `p'`.** This is the left leg of the square of Stacks 0CMR for `p'`, read in the
2-fibre product of the colimits, and it is an equality of functors rather than merely an
isomorphism. -/
lemma colimMap_twoFibreProductSnd_comp_comparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    Stack.colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E ⋙
        CategoricalPullback.π₂
          (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
            B S hS p E)).toFunctor
          (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
            B S hS q E)).toFunctor =
      (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have hcomp : colimMap (Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E) ≫
      colimMap (Cat.twoFibreProductDiagramSnd
        (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
        (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)) =
      colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E) := by
    rw [← fiberDiagramMap_twoFibreProductSnd_comp_comparison.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q E]
    refine colimit.hom_ext fun j => ?_
    rw [← Category.assoc, ι_colimMap, Category.assoc, ι_colimMap, ι_colimMap]
    exact (Category.assoc _ _ _).symm
  have h := congrArg Cat.Hom.toFunctor hcomp
  rw [Cat.Hom.comp_toFunctor] at h
  refine Eq.trans ?_ h
  rw [show Stack.colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E =
      (colimMap (Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)).toFunctor ⋙
        Cat.colimitTwoFibreProductComparison
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) from rfl,
    Functor.assoc, Cat.colimitTwoFibreProductComparison_comp_π₂]

/-- **The square of the colimits is 2-cartesian.** Its apex is `colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}`, its legs
are the colimits of the diagrams of split fibres of the two projections, and its cospan is the
colimits of those of `p` and `q`. Its comparison functor is the comparison `K` of Stacks 0CMW
itself, by `AlgebraicGeometry.BigFppfOver.colimMap_twoFibreProductFst_comp_comparison` and
`AlgebraicGeometry.BigFppfOver.colimMap_twoFibreProductSnd_comp_comparison`, and `K` is an
equivalence -- filtered colimits of categories commute with 2-fibre products.

This is the left-hand square of the first pasting of Stacks 0CMT. -/
lemma isEquivalence_squareComparison_colimitTwoFibreProduct (E : I ⥤ BigFppfOver B S hS)
    [IsFiltered Iᵒᵖ] :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (CategoricalPullback.squareComparison
      (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
      (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
      (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
        B S hS p E)).toFunctor
      (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
        B S hS q E)).toFunctor
      (CategoricalPullback.projFillerOfEq _ _ _ _
        (Stack.colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)
        (colimMap_twoFibreProductFst_comp_comparison.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q E)
        (colimMap_twoFibreProductSnd_comp_comparison.{u, v, w}
          B S hS 𝒳 𝒴 𝒵 p q E))).IsEquivalence := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have := Stack.isEquivalence_colimitSplitFiberTwoFibreProductComparison.{u, v, w}
    B S hS 𝒳 𝒴 𝒵 p q E
  exact CategoricalPullback.isEquivalence_squareComparison_projOfEq _ _ _ _ _ _ _

end AlgebraicGeometry.BigFppfOver

end
