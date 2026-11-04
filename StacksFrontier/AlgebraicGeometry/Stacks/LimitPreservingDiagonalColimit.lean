module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalMorphism
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductDiagonal

/-!
# The left leg of the diagonal's square is the diagonal of the left legs

The square of Stacks 0CMR for the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` has
`colim (𝒳 ×_𝒴 𝒳)_{Uᵢ}` for its lower left corner, while the square of relative diagonals of the
square of `f` has `colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒳_{Uᵢ}`. The comparison `K` between the
two is the colimit of the stagewise comparison
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison` followed by the comparison
`CategoryTheory.Cat.colimitTwoFibreProductComparison` out of the colimit of a stagewise 2-fibre
product. This file builds `K` and proves that it carries the left leg of the diagonal's square to
the diagonal of the left leg of `f`'s square:

`colim Δ'_{Uᵢ} ⋙ K = Δ_{colim f'_{Uᵢ}}`.

The proof is stagewise and needs no filteredness. At one stage the identity is
`AlgebraicGeometry.BigFppfOver.splitFiberMap_twoFibreProductDiagonal_comp_comparison` -- the
split fibre of the diagonal *is* the diagonal of the split fibres -- carried across the universe
lift by `CategoryTheory.Limits.CategoricalPullback.diagonal_comp_asSmallMap`; that makes the
comparison of *diagrams* carry the stagewise diagonal to the stagewise diagonal, and
`CategoryTheory.Cat.colimMap_twoFibreProductDiagonalDiagram_comp_comparison` then identifies the
colimit of the stagewise diagonal, read in the 2-fibre product of the colimits, with the
diagonal of `colimMap`.

## Main definitions

* `AlgebraicGeometry.Stack.colimitSplitFiberTwoFibreProductComparison`: the comparison `K`.

## Main results

* `AlgebraicGeometry.BigFppfOver.fiberDiagramMap_twoFibreProductDiagonal_comp_comparison`: the
  diagram of split fibres of the diagonal, compared stagewise, is the stagewise diagonal
  `CategoryTheory.Cat.twoFibreProductDiagonalDiagram`.
* `AlgebraicGeometry.BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison`: the identity
  displayed above, which is the input `iu` of
  `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`.

## Implementation notes

`CategoryTheory.Limits.colimMap` is functorial, which Mathlib records only through `colim.map`
and so only under `HasColimitsOfShape`; the composite here is therefore split by
`CategoryTheory.Limits.colimit.hom_ext` instead.

`Deformation.Artin.fiberDiagram` carries its own `CategoryTheory.Limits.HasColimit` instance, but
the stagewise 2-fibre product of two such diagrams does not: `CategoryTheory.Cat` has all
colimits only at a single universe, and the shrink to the index category's universes has to be
performed. `AlgebraicGeometry.Stack.hasColimitsOfSize_cat_fiberDiagram` performs it once, at the
universe shape of the diagrams of split fibres, and is installed with `letI` wherever a colimit
of a stagewise 2-fibre product is named.

## References

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

/-- **`Cat` has the colimits the diagrams of split fibres need, at the universes of Stacks
0CMW.** `CategoryTheory.Cat` has all colimits at one universe; `Deformation.Artin.fiberDiagram`
and its stagewise 2-fibre products take values at `max (u + 1) v w`, which absorbs both the type
and the hom universe of the index category, so the shrink applies. -/
lemma hasColimitsOfSize_cat_fiberDiagram :
    HasColimitsOfSize.{w, v} Cat.{max (u + 1) v w, max (u + 1) v w} :=
  hasColimitsOfSizeShrink.{w, v, max (u + 1) v w, max (u + 1) v w} _

/-- **The comparison `K` of the lower left corners.** The split fibres of the base change
`𝒳 ×_𝒴 𝒵`, taken stagewise into the stagewise 2-fibre product of the split fibres and then
through the colimit, land in the 2-fibre product of the colimits:

`colim (𝒳 ×_𝒴 𝒵)_{Uᵢ} ⥤ colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒵_{Uᵢ}`.

It is `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison` pushed through the colimit,
followed by `CategoryTheory.Cat.colimitTwoFibreProductComparison`. -/
noncomputable def colimitSplitFiberTwoFibreProductComparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimit (Deformation.Artin.fiberDiagram
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E) : Cat) ⥤
      CategoricalPullback
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)).toFunctor
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).toFunctor :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  (colimMap (splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)).toFunctor ⋙
    Cat.colimitTwoFibreProductComparison
      (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
      (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The diagram of split fibres of the diagonal, read componentwise, is the stagewise
diagonal.** At each stage this is
`AlgebraicGeometry.BigFppfOver.splitFiberMap_twoFibreProductDiagonal_comp_comparison` carried
across the universe lift of the cospan, which is a change of cospan along a strictly commuting
square and therefore carries diagonals to diagonals
(`CategoryTheory.Limits.CategoricalPullback.diagonal_comp_asSmallMap`). -/
lemma fiberDiagramMap_twoFibreProductDiagonal_comp_comparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E ≫
        Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E =
      Cat.twoFibreProductDiagonalDiagram
        (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E) :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  NatTrans.ext (funext fun j => Cat.Hom.ext
    (congrArg (fun F => AsSmall.down ⋙ F)
      ((congrArg
          (fun F => F ⋙ CategoricalPullback.map
            (Stack.splitFiberMap B S hS f (E.obj j.unop))
            (Stack.splitFiberMap B S hS f (E.obj j.unop))
            AsSmall.up AsSmall.up AsSmall.up
            (AsSmall.down ⋙ Stack.splitFiberMap B S hS f (E.obj j.unop) ⋙ AsSmall.up)
            (AsSmall.down ⋙ Stack.splitFiberMap B S hS f (E.obj j.unop) ⋙ AsSmall.up)
            (eqToIso rfl) (eqToIso rfl))
          (splitFiberMap_twoFibreProductDiagonal_comp_comparison.{u, v, w} B S hS 𝒳 𝒴 f
            (E.obj j.unop))).trans
        (CategoricalPullback.diagonal_comp_asSmallMap
          (Stack.splitFiberMap B S hS f (E.obj j.unop))))))

/-- **The left leg of the diagonal's square, read in the 2-fibre product of the colimits, is the
diagonal of the left leg.** This is the input `iu` of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer` for
the two squares of Stacks 0CMW, and it is an equality of functors rather than merely an
isomorphism. -/
lemma colimMap_twoFibreProductDiagonal_comp_comparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor ⋙
        Stack.colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E =
      CategoricalPullback.diagonal
        (colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
          B S hS f E)).toFunctor := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := Stack.hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have hcomp : colimMap (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E) ≫
        colimMap (Stack.splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E) =
      colimMap (Cat.twoFibreProductDiagonalDiagram
        (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)) := by
    rw [← fiberDiagramMap_twoFibreProductDiagonal_comp_comparison.{u, v, w} B S hS 𝒳 𝒴 f E]
    refine colimit.hom_ext fun j => ?_
    rw [← Category.assoc, ι_colimMap, Category.assoc, ι_colimMap, ι_colimMap]
    exact (Category.assoc _ _ _).symm
  have h := congrArg (fun H => H ⋙ Cat.colimitTwoFibreProductComparison
      (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)
      (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E))
    (congrArg Cat.Hom.toFunctor hcomp)
  rw [Cat.Hom.comp_toFunctor] at h
  exact h.trans (Cat.colimMap_twoFibreProductDiagonalDiagram_comp_comparison
    (Stack.fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E))

end AlgebraicGeometry.BigFppfOver

end
