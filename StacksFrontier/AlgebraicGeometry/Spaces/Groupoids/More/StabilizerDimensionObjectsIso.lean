module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidObjectsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.StabilizerDimensionOverField

/-!
# Stacks 06FF at an object space isomorphic to the spectrum of a field

**Stacks 06FF** says that for a groupoid in algebraic spaces over `S` whose space of objects is
the spectrum of a field and whose source and target are locally of finite type, the arrow space
and the stabilizer have the same dimension. This file states it with the object space only
*isomorphic* to the spectrum of the field.

## Main results

* `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer_of_objects_iso`:
  **Stacks 06FF**, with the object space isomorphic to the field spectrum.

## Implementation notes

The tag asks the object space to be that spectrum, and an algebraic space isomorphic to it is that
spectrum. `AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer` states it at an
equality of algebraic spaces. The isomorphism form reduces to it by replacing the groupoid with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.transportObjects`: that groupoid has the field
spectrum as its object space on the nose, has the *same* arrow space, and has a stabilizer of the
same dimension
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.dimension_stabilizerOverBase_transportObjects`), so
both sides of the conclusion are unchanged. The isomorphism form is what a consumer has when
the field spectrum reaches it as an object of the site presented with an isomorphism of its
underlying scheme, which is the shape of `AlgebraicGeometry.Stack.FieldSpectrum`.

## References

* [Stacks Project, Tag 06FF](https://stacks.math.columbia.edu/tag/06FF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06FF.** Let `G` be a groupoid in algebraic spaces over `S` whose space of objects
is the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and whose source
and target are locally of finite type. Then the space of arrows of `G` and the stabilizer of `G`
have the same dimension.

The hypothesis is an *isomorphism* of the object space with the spectrum of the field, not an
equality of algebraic spaces; the equality case is
`AlgebraicGeometry.Space.dimension_arrows_eq_dimension_stabilizer`. -/
@[stacks 06FF "with the space of objects isomorphic to the spectrum of the field"]
theorem dimension_arrows_eq_dimension_stabilizer_of_objects_iso {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (objects_iso : G.objects ≅ _root_.AlgebraicGeometry.schemeSpace
      (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom) :
    dimension B S hS G.arrows.obj G.arrows.property =
      dimension B S hS (GroupoidInAlgebraicSpaces.stabilizerOverBase G).obj
        (GroupoidInAlgebraicSpaces.stabilizerOverBase G).property := by
  have hs' := GroupoidInAlgebraicSpaces.isLocallyOfFiniteType_transportObjects_source
    G objects_iso hs
  have ht' := GroupoidInAlgebraicSpaces.isLocallyOfFiniteType_transportObjects_target
    G objects_iso ht
  exact (dimension_arrows_eq_dimension_stabilizer B S hS hk structureMap
    (GroupoidInAlgebraicSpaces.transportObjects G objects_iso) rfl hs' ht').trans
    (GroupoidInAlgebraicSpaces.dimension_stabilizerOverBase_transportObjects G objects_iso)

end AlgebraicGeometry.Space

end
