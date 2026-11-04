module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.SquaringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.SquaringMapProperties

/-!
# Universally injective morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *universally injective* when every base
change of it along a morphism from an algebraic space induces an injective map on points.
For a representable morphism this is tested by field-valued points: it holds exactly when
each of the morphism's components at an object of the site whose underlying scheme is the
spectrum of a field is injective.

## Main definitions

* `AlgebraicGeometry.Space.UniversallyInjective` is universal injectivity of a morphism of
  algebraic spaces.
* `AlgebraicGeometry.AffineLineInvolution.affineLineSquare` squares the standard coordinate
  of the affine line, and
  `AlgebraicGeometry.AffineLineInvolution.squaringMap` is the morphism it descends to on the
  involution quotient of Stacks 02Z1.
* `AlgebraicGeometry.AffineLineInvolution.affineLineZero` is the origin of the affine line
  over an object of the site, and `AlgebraicGeometry.AffineLineInvolution.originPoint` is the
  point of Stacks 03BU it defines.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_iff_injective_on_field_points`: a
  representable morphism has Mathlib's universal injectivity of scheme morphisms on all of
  its represented base changes precisely when it is injective on field-valued points of the
  site.
* `AlgebraicGeometry.Space.universallyInjective_pullback`: **Stacks 03MW**, a base change of a
  universally injective morphism is universally injective; and
  `AlgebraicGeometry.Space.universallyInjective_of_isPullback`, the same conclusion for an
  arbitrary cartesian square.
* `AlgebraicGeometry.Space.universallyInjective_comp`: **Stacks 03MY**, a composition of
  universally injective morphisms is universally injective.
* `AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`: a morphism is universally
  injective as soon as two sections over a field spectrum with the same image agree after one
  restriction to a field spectrum. This is the implication (1) implies (2) of Stacks 040X.
* `AlgebraicGeometry.AffineLineInvolution.isIso_squaringMap_pullback_puncturedAffineLine`:
  the squaring map on the involution quotient is an isomorphism away from the origin.
* `AlgebraicGeometry.AffineLineInvolution.existsUnique_pointsMap_squaringMap_eq_originPoint`:
  exactly one point of the involution quotient lies over the origin.
* `AlgebraicGeometry.AffineLineInvolution.universallyInjective_squaringMap`: the squaring map
  on the involution quotient is universally injective.

  The last four are parts (1) to (4) of the remark of Stacks 05VS; part (5), that the squaring
  map is not separated, is
  `AlgebraicGeometry.AffineLineInvolution.not_isSeparated_squaringMap` in
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap`.

## Implementation notes

Stacks 05VS is a *remark*, and its content is a conjunction of five assertions about the
involution quotient `X = 𝐀¹_k/\{x ∼ -x ∣ x ≠ 0\}` of Stacks 02Z1: it carries a morphism to
`𝐀¹_k` sending the point with coordinate `x` to the point with coordinate `x ^ 2`; that
morphism is an isomorphism away from `0`; there is a unique point of `X` over `0`; the morphism
is universally injective; and the morphism is not separated — the point of the remark, since a
universally injective morphism of *schemes* is separated by Stacks 05VE. (That `X` itself is
not separated, which the remark uses to get the last assertion, is cited there from
Stacks 02Z1 and is not an assertion of 05VS.) The first four are stated here, as
`AlgebraicGeometry.AffineLineInvolution.squaringMap`,
`AlgebraicGeometry.AffineLineInvolution.isIso_squaringMap_pullback_puncturedAffineLine`,
`AlgebraicGeometry.AffineLineInvolution.existsUnique_pointsMap_squaringMap_eq_originPoint` and
`AlgebraicGeometry.AffineLineInvolution.universallyInjective_squaringMap`, and each carries its
own clause of the tag. The fifth lives downstream, in
`StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap`, because the geometric
input it needs — that the relation `R = Δ ⨿ Γ°` of Stacks 02Z1 is not a closed immersion — is
proved in `StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionNotSeparated`, which is not
among the imports of this module.

The fifth assertion needs no algebraicity hypothesis on `X`, and in particular no effective
descent: the relation is the kernel pair of the chart `𝐀¹_k ⟶ X` with no hypothesis on the
quotient, so it is a represented base change of the relative diagonal of the squaring map, and
being separated asks for every represented base change of that diagonal to be a closed
immersion. Neither the two effective-descent hypotheses of Stacks 0265 carried by
`AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient` nor the
algebraic-space property itself enters.

The first two statements are made for natural transformations of presheaves on the big fppf site
over `S`, so that a morphism of algebraic spaces may be fed to them without carrying its
algebraicity proofs. The points and their induced maps are
`AlgebraicGeometry.Space.points` and `AlgebraicGeometry.Space.pointsMap`, and the fibre
product is the categorical pullback in the presheaf category.

The two notions are deliberately kept apart. `AlgebraicGeometry.Space.UniversallyInjective`
is the definition of the source: a condition on the maps of point *sets* of all base
changes. The characterization is about the *scheme* property
`AlgebraicGeometry.UniversallyInjective` transferred to the site by inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` and then by
`CategoryTheory.MorphismProperty.presheaf`; it is available only for a representable
morphism, where every represented base change is a morphism of schemes.

The field occurring in the test is restricted to those represented in the chosen
size-bounded site, by asking for an object of the site together with an isomorphism of its
underlying scheme with the spectrum of the field. The reverse implication produces such an
object from the residue field of a point of the fibre product of the represented base
change with itself; that the residue field's spectrum stays inside the cutoff is
`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact` together with
`AlgebraicGeometry.Scheme.size_pullback_le`.

The two permanence properties are the exact analogues of
`AlgebraicGeometry.Space.universalHomeomorphism_pullback` and
`AlgebraicGeometry.Space.universalHomeomorphism_comp`, with `IsHomeomorph` replaced by
`Function.Injective`: everything turns on injectivity of the map on points of an
isomorphism, which is `AlgebraicGeometry.Space.pointsMap_injective_of_mono` of Tag 06RV, and
on `AlgebraicGeometry.Space.pointsMap_comp`. Base change is then the instance of the
transport lemma at the pasting isomorphism `W ×_Z (Z ×_Y X) ≅ W ×_Y X` and composition its
instance at `W ×_Z X ≅ (W ×_Z Y) ×_Y X`. Stability under base change is stated both for the
canonical fibre product, which is the form Stacks 03MW takes, and for an arbitrary cartesian
square over the same cospan, which is what a client with its own fibre product needs.

The assertions of Stacks 05VS live in this module, in the namespace of the remark's quotient,
because they are the content of a tag of the universally injective section; the geometry of
the quotient itself is `StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution` and
`StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient`.

The descent of the squaring map is `Stacks.Groupoids.quotientSheafDesc` applied to the
invariance of the squared coordinate under negation; the restriction over the punctured line is
an isomorphism by a local criterion, local surjectivity of the quotient projection being
`Stacks.Groupoids.toQuotientSheaf_isLocallySurjective` and local surjectivity of squaring
coming from adjoining a square root of a section, which is faithfully flat and finitely
presented because `X ^ 2 - C a` is monic.

The two assertions about the origin go through the same local surjectivity, now read on points:
a locally surjective morphism is surjective on the points of Stacks 03BU, and more precisely a
field-valued point of its target lifts to a section of its source over a single further field
spectrum. For the point over `0` this is enough on its own — a field-valued point of `𝐀¹_k`
whose square is the origin *is* the origin, the spectrum of a field being reduced — and no
assumption on the characteristic is needed. For universal injectivity two successive lifts
bring both sections of `X` to classes of points of `𝐀¹_k` with the same square over one field
spectrum; there the coordinate is zero or a unit, and the two cases are closed by reducedness
and by
`AlgebraicGeometry.AffineLineInvolution.quotient_eq_of_square_eq` respectively. The
characteristic assumption enters only through the second case, which uses that the squaring
map is an isomorphism over the punctured line.

## Files

* `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.Basic`: the definition,
  the characterization by field-valued points, and the permanence properties.
* `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.SquaringMap`: the
  squaring map on the involution quotient and the local lemmas it needs.
* `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.SquaringMapProperties`:
  parts (2) to (4) of Stacks 05VS.

## References

* [Stacks Project, Tag 03MU](https://stacks.math.columbia.edu/tag/03MU)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 03MW](https://stacks.math.columbia.edu/tag/03MW)
* [Stacks Project, Tag 03MY](https://stacks.math.columbia.edu/tag/03MY)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 05VS](https://stacks.math.columbia.edu/tag/05VS)
-/
