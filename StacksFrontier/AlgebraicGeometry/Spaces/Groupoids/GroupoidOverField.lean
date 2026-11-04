module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Groupoids in algebraic spaces whose objects are the spectrum of a field (Stacks 06DY)

Stacks 06DY fixes the data a scheme `S`, an algebraic space `B` over `S`, and a groupoid in
algebraic spaces `(U, R, s, t, c)` over `B` subject to the single extra condition that the space
of objects is the spectrum of a field, `U = Spec k`. This file bundles exactly that data: a
groupoid in algebraic spaces over `B` in the sense of Stacks 043W, a field `k` whose spectrum is
an object of the ambient big fppf site together with its structure morphism to `S`, and the
identification of the space of objects with the algebraic space represented by `Spec k`.

## Main definitions

* `AlgebraicGeometry.GroupoidOverField`: **Stacks 06DY**, the situation itself.
* `AlgebraicGeometry.GroupoidOverField.siteObject`: the object `Spec k` of the big fppf site
  over `S` determined by the field and its structure morphism.

## Implementation notes

The field is carried as a type with an instance-implicit `Field` structure, as for
`AlgebraicGeometry.Space.FieldValuedPoint`, so that a term of this structure is literally a
choice of field rather than of a type with a side condition.

The identification of the space of objects is an equality of algebraic spaces,
`AlgebraicGeometry.schemeSpace` applied to `Spec k` regarded as an object of the site over `S`,
rather than an isomorphism. This is the shape in which the results of the section phrase the
hypothesis — for instance the constant dimension of the arrow space, Stacks 06FD — so those
results apply to the fields of this structure directly.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06DY](https://stacks.math.columbia.edu/tag/06DY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks 06DY.** A groupoid in algebraic spaces over an algebraic space `B` over a scheme
`S`, whose space of objects is the spectrum of a field `k` regarded as an algebraic space over
`S` through Yoneda. -/
@[stacks_fixed 06DY "groupoid in algebraic spaces over a field"]
structure GroupoidOverField (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS) where
  /-- The field whose spectrum is the space of objects. -/
  carrier : Type u
  /-- Its field structure. -/
  [field : Field carrier]
  /-- The spectrum of the field lies in the chosen big fppf site. -/
  containsSpec : C.Contains (Spec (.of carrier))
  /-- The structure morphism of the spectrum of the field over the base scheme. -/
  structureMap : Spec (.of carrier) ⟶ S
  /-- The underlying groupoid in algebraic spaces over `B`. -/
  groupoid : GroupoidInAlgebraicSpaces C S hS B
  /-- Its space of objects is the spectrum of the field. -/
  objects_eq : groupoid.objects =
    schemeSpace (Over.mk (⟨structureMap⟩ : C.obj containsSpec ⟶ C.obj hS))

attribute [instance] GroupoidOverField.field

namespace GroupoidOverField

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidOverField C S hS B)

/-- The spectrum of the field, as an object of the big fppf site over `S`. -/
noncomputable abbrev siteObject : BigFppfOver C S hS :=
  Over.mk (⟨G.structureMap⟩ : C.obj G.containsSpec ⟶ C.obj hS)

/-- The space of objects, the spectrum of the field. -/
abbrev objects : AlgebraicSpaces C S hS := G.groupoid.objects

/-- The space of arrows. -/
abbrev arrows : AlgebraicSpaces C S hS := G.groupoid.arrows

/-- The source morphism. -/
abbrev source : G.arrows ⟶ G.objects := G.groupoid.source

/-- The target morphism. -/
abbrev target : G.arrows ⟶ G.objects := G.groupoid.target

/-- The underlying presheaf of the space of objects is represented by the spectrum of the
field. -/
theorem objects_obj_eq : G.objects.obj = yoneda.obj G.siteObject :=
  congrArg (fun X : AlgebraicSpaces C S hS => X.obj) G.objects_eq

end GroupoidOverField

end AlgebraicGeometry

end
