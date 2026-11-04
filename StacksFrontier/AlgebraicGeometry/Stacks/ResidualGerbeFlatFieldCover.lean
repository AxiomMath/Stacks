module

public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack

/-!
# A flat field cover of a one-point substack forces the substack to have one point

Condition (3) of **Stacks 06MT** asks, of a point `x` of an algebraic stack `𝒳`, for a
monomorphism `f : 𝒵 ⟶ 𝒳` together with a surjective flat 1-morphism to `𝒵` from the algebraic
stack of the spectrum of a field, some point of which maps to `x`. Condition (1) asks instead
that the space of points of `𝒵` be a singleton mapping to `x`.

This file proves that condition (3) implies condition (1). The mechanism is that the spectrum of
a field has one point, so a 1-morphism out of its algebraic stack which is surjective on points
leaves its target with at most one point; the flatness hypothesis is not needed for this
direction.

The identification of the points of a represented algebraic stack with the points of its scheme
is `AlgebraicGeometry.Stack.pointsHomeomorphScheme`, and the witness of fibredness in groupoids
it is stated at agrees with the one `AlgebraicGeometry.Stack.points` is read at in the conditions
of Stacks 06MT, because `CategoryTheory.Functor.IsFiberedInGroupoids` is a proposition.

## Main definitions

None.

## Main results

* `AlgebraicGeometry.Stack.subsingleton_points_schemeStack`: a represented algebraic stack whose
  scheme has at most one point has at most one point.
* `AlgebraicGeometry.Stack.subsingleton_points_fieldSpectrumStack`: the algebraic stack of the
  spectrum of a field has at most one point.
* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_flatFieldCover`: condition (3) of
  **Stacks 06MT** implies its condition (1).

## Implementation notes

`AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**) is surjectivity of the map on points,
so the passage from a surjection out of a one-point stack to a one-point target is a statement
about `Function.Surjective` and needs nothing about the topology of the point spaces.

The two equivalences of Stacks 06MT are not proved here: the implication (2) ⟹ (1) is
`AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_reduced`, and the implications
(1) ⟹ (2) and (2) ⟹ (3) rest respectively on the reduced induced substack of **Stacks 0509**
and on **Stacks 06MN**, neither of which this library has. Accordingly no `06MT` key is placed
on anything below; a key here would make a tag query answer that the tag is formalized while all
three of its statements are open.

## References

* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A represented algebraic stack has the points of its scheme.** If the scheme underlying an
object `U` of the big fppf site of `S` has at most one point, then so does the algebraic stack it
represents.

This transports `AlgebraicGeometry.Stack.pointsHomeomorphScheme`, the identification of the point
space of **Stacks 04XL** of a represented stack with the topological space of its scheme. -/
theorem subsingleton_points_schemeStack (U : BigFppfOver B S hS)
    (hU : Subsingleton ((BigFppfOver.toScheme B S hS).obj U)) :
    Subsingleton (points B S hS (schemeStack.{u, w} B S hS U).val.val
      (Classical.choose (schemeStack.{u, w} B S hS U).property)) := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  exact (pointsHomeomorphScheme B S hS U).injective.subsingleton

/-- **The algebraic stack of the spectrum of a field has one point.** The spectrum of a field has
a unique prime ideal, so the scheme underlying a `AlgebraicGeometry.Stack.FieldSpectrum` has at
most one point and `AlgebraicGeometry.Stack.subsingleton_points_schemeStack` applies. -/
theorem subsingleton_points_fieldSpectrumStack (F : FieldSpectrum B S hS) :
    Subsingleton (points B S hS (schemeStack.{u, w} B S hS F.base).val.val
      (Classical.choose (schemeStack.{u, w} B S hS F.base).property)) :=
  subsingleton_points_schemeStack.{u, w} B S hS F.base
    (Scheme.homeoOfIso F.isSpec).injective.subsingleton

/-- **Condition (3) of Stacks 06MT implies its condition (1).** A monomorphism `f : 𝒵 ⟶ 𝒳`
admitting a surjective 1-morphism to `𝒵` from the algebraic stack of the spectrum of a field, one
of whose points maps to `x`, exhibits `𝒵` as a one-point substack of `𝒳` over `x`: the spectrum
of a field has one point and `AlgebraicGeometry.Stack.IsSurjective` is surjectivity on points, so
every point of `𝒵` is the image of that one point.

Flatness of the cover, which condition (3) also carries, is not used. -/
theorem hasSingletonPointMonomorphism_of_flatFieldCover
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (h : HasFlatFieldCoverMonomorphism B S hS 𝒳 x) :
    HasSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨𝒵, f, F, z, hmono, hsurj, -, q, hq⟩ := h
  have hsub := subsingleton_points_fieldSpectrumStack.{u, w} B S hS F
  refine ⟨𝒵, f, hmono, _, fun z' => ?_, hq⟩
  obtain ⟨q', rfl⟩ := hsurj z'
  exact congrArg _ (Subsingleton.elim q' q)

end AlgebraicGeometry.Stack

end
