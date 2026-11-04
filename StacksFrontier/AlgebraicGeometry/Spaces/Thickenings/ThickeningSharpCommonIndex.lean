module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp

/-!
# The comorphism read through a thickening, on a chart of the thickening

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`, and
let `c : X ⟶ W` be a morphism.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartProjection.lean` reads the
comorphism `𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of `c` through the thickening on étale scheme charts,
but only after transporting it across the comparison
`AlgebraicGeometry.Space.pushforwardRingSheafCompInv` of iterated direct images: the reading is
indexed by an étale chart of `X` above `X ×_W V`, and **that index category depends on `c`**.

For two morphisms `c, c'` agreeing on the thickening the target sheaf is literally the same —
it depends on `c` only through `i ≫ c` — so their comorphisms through the thickening can be
compared as morphisms, which is what
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RestrictedSharpAmbient.lean` does.  Their chart
readings, however, live over two different index categories and cannot be compared term by term.

This file reads the comorphism through the thickening at the index category which depends only on
`i ≫ c`, namely the étale charts of `Z` above `Z ×_W V`.  By
`AlgebraicGeometry.Space.directImageChartProjection_pushforwardRingSheafCompInv` the one-step
reading at the index attached to a chart `j` of `X` above `X ×_W V` and a chart `k` of `Z` above
`Z ×_X j` is the two-step reading, so the computation of the latter carries over: **it is the
chart projection along `i` of the unit `η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` at the pullback of the regular
function along the chartwise morphism of `c`.**

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_comp`:
  **the one-step chart projection of the comorphism read through the thickening, at the index
  attached to a chart of `X` over `X ×_W V` and a chart of `Z` over `Z ×_X j`, is the chart
  projection along `i` of the unit at the chartwise pullback of the regular function.**

## Implementation notes

The statement is made at `AlgebraicGeometry.Space.structureSharpThroughThickening`, whose index
is the composite `i ≫ c` on the nose, rather than at
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt`, which carries an `eqToHom` along a
chosen equality `i ≫ c = e`.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` record that putting
such an `eqToHom` next to one of these composites is a deterministic `whnf` timeout; the two
differ by `CategoryTheory.Category.comp_id` once the equality is substituted, so nothing is lost
by keeping the composite spelling.

**No `@[stacks]` attribute is placed.**  This is a chart-level reading of
[Stacks Project, Tag 03G8] internal to this development.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated
  direct images.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this reading is
  an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The comorphism read through the thickening, projected to a chart of the thickening.**

For a chart `j` of `X` above `X ×_W V` and a chart `k` of `Z` above `Z ×_X j`, the projection of
the comorphism `𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` of `c` read through the thickening, at the index of
the limit of chart sections attached to `j` and `k` by
`AlgebraicGeometry.Space.chartBaseChangeComp`, is the projection along `i` of the unit
`η : 𝒪_X ⟶ i_*i^{-1}𝒪_X` at the pullback of the regular function along the chartwise morphism
of `c`.

The index on the left depends on `c` only through the composite `i ≫ c`, so this is the reading
at which the comorphisms of two morphisms agreeing on the thickening become comparable; the
right hand side is the reading of
`AlgebraicGeometry.Space.directImageChartProjection_structureSharpThroughThickening_chartPullback`,
whose index does depend on `c`. -/
theorem directImageChartProjection_structureSharpThroughThickening_comp (c : X ⟶ W)
    (V : SmallEtale B S hS W.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op)
    (k : StructuredArrow
      (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) j.right.unop))
      (comparisonFunctor B S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op V))) :
    (directImageChartProjection B S hS (subspaceInclusion B S hS X Z ≫ c) V
          (StructuredArrow.mk
            ((chartBaseChangeComp B S hS (subspaceInclusion B S hS X Z) c V j).op ≫
              k.hom))).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((structureSharpThroughThickening B S hS Z c).hom.app (op V) b) =
      (directImageChartProjection B S hS (subspaceInclusion B S hS X Z) j.right.unop k).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((thickeningRingUnit B S hS Z).hom.app j.right
          (chartPullback B S hS c V j b)) :=
  (directImageChartProjection_pushforwardRingSheafCompInv B S hS
        (subspaceInclusion B S hS X Z) c V j k
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
        ((structureSharpThroughThickening B S hS Z c).hom.app (op V) b)).symm.trans
    (congrArg ((directImageChartProjection B S hS (subspaceInclusion B S hS X Z)
        j.right.unop k).app
      ((sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
      (directImageChartProjection_structureSharpThroughThickening_chartPullback
        B S hS Z c V j b))

end AlgebraicGeometry.Space

end
