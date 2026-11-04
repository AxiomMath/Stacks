module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.RingTheory.Branches.Defs

/-!
# Geometrically unibranch algebraic spaces

An algebraic space `F` over a scheme `S` is *geometrically unibranch at* a point `x` of `|F|`
when, for every étale chart `U → F` and every point `u` of `U` above `x`, the local ring
`𝒪_{U, u}` is geometrically unibranch; it is *geometrically unibranch* when this holds at every
point of `|F|`.

Lemma 06DK of the Stacks Project lists five equivalent conditions on a point of an algebraic
space — one minimal prime, one irreducible component, unibranch charts, geometrically unibranch
charts, and one minimal prime in the étale local ring at a geometric point — and the definition
of Tag 06DL is that they hold.  The condition taken here as the definition is the geometrically
unibranch one on charts, which is the one phrased purely in terms of the local rings of schemes
and so needs nothing beyond the points of a presheaf on the big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.IsGeometricallyUnibranchAt`: geometric unibranchness at a point of
  `|F|`, tested on the local rings of the étale charts at the points above it.
* `AlgebraicGeometry.Space.IsGeometricallyUnibranch`: geometric unibranchness at every point
  of `|F|`.

## Implementation notes

The chosen big fppf site presents the points of a chart by the field-valued points of its
represented presheaf, so the two quantifiers of the definition — over étale charts of `F`, and
over the field-valued points of a chart lying over `x` — express the source's quantifiers over
schemes étale over the algebraic space and over their points above `x`.

Neither predicate assumes that `F` is an algebraic space: both read off the local rings of the
charts, which makes sense for any presheaf on the big fppf site over `S`, and the equivalence
with the other four conditions of Tag 06DK is what needs algebraicity.

Geometric unibranchness of a local ring is `IsGeometricallyUnibranch` of Tag 0BPZ.

## References

* [Stacks Project, Tag 06DL](https://stacks.math.columbia.edu/tag/06DL)
* [Stacks Project, Tag 06DK](https://stacks.math.columbia.edu/tag/06DK)
* [Stacks Project, Tag 0BPZ](https://stacks.math.columbia.edu/tag/0BPZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 06DL, at a point.** The presheaf `F` is geometrically unibranch at a point `x` of
`|F|` when the local ring of every étale chart of `F` at every point above `x` is geometrically
unibranch.  This is condition (4) of Tag 06DK, which for an algebraic space is equivalent to the
four other branch criteria there. -/
@[stacks 06DL "at a point"]
noncomputable def IsGeometricallyUnibranchAt (x : points B S hS F) : Prop :=
  ∀ (U : SmallEtale B S hS F)
      (p : FieldValuedPoint B S hS (yoneda.obj U.1.left)),
    pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
        (p.class B S hS (yoneda.obj U.1.left)) = x →
      _root_.IsGeometricallyUnibranch
        (((BigFppfOver.toScheme B S hS).obj U.1.left).presheaf.stalk
          (schemePoint B S hS U.1.left p))

/-- **Stacks 06DL, at every point.** The presheaf `F` is geometrically unibranch when it is
geometrically unibranch at every point of `|F|`. -/
@[stacks 06DL "at every point"]
noncomputable abbrev IsGeometricallyUnibranch : Prop :=
  ∀ x : points B S hS F, IsGeometricallyUnibranchAt B S hS F x

end AlgebraicGeometry.Space

end
