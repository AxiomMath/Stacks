module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization

/-!
# Flat morphisms locally of finite type and the conditions of Tag 0BB1

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over `S` which is locally of finite
type, and suppose the target satisfies the equivalent conditions of Stacks 0BB1 — the finiteness
of the irreducible components of every quasi-compact open of every étale scheme chart, which is
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`. Then the source satisfies those
conditions as well, and `f` carries points of codimension zero to points of codimension zero.
Both assertions together are Stacks 0GMD.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `hasLocallyFiniteIrreducibleComponents_and_codimensionZero_of_isFlat_of_isLocallyOfFiniteType`
  is **Stacks 0GMD**, both of its conclusions in one statement.

## Implementation notes

The two conclusions are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization`, which this file imports, and
this statement only puts them together under the hypotheses of the source. The finiteness
conclusion is
`AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType`.
The codimension-zero conclusion is `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isFlat`,
which is Stacks 0GMC and asks neither that the morphism be locally of finite type nor that the
target satisfy the conditions of Stacks 0BB1; the source derives the second conclusion of
Tag 0GMD from Tag 0GMC in exactly that way.

Codimension zero at a point of an algebraic space is vanishing of
`AlgebraicGeometry.Space.localRingDimension`, the dimension of the local ring of Tag 04NA, as in
the statement of Stacks 0BB1 and in the comparisons of Tag 0BAQ.

## References

* [Stacks Project, Tag 0GMD](https://stacks.math.columbia.edu/tag/0GMD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0GMD.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat and
locally of finite type, and assume `Y` satisfies the equivalent conditions of Stacks 0BB1. Then
`X` satisfies those conditions too, and for every point `x` of `X` of codimension zero the image
`f x` has codimension zero in `Y`. -/
@[stacks 0GMD]
theorem hasLocallyFiniteIrreducibleComponents_and_codimensionZero_of_isFlat_of_isLocallyOfFiniteType
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hYfinite : HasLocallyFiniteIrreducibleComponents B S hS Y) :
    HasLocallyFiniteIrreducibleComponents B S hS X ∧
      ∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        localRingDimension B S hS (pointsMap B S hS X f x) = 0 :=
  ⟨hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType B S hS hX hY f hf hft
      hYfinite,
    fun x hx ↦ localRingDimension_eq_zero_of_isFlat B S hS hX hY f hf x hx⟩

end AlgebraicGeometry.Space

end
