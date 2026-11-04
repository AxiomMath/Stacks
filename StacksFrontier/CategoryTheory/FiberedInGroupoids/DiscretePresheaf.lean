module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Types as discrete groupoids

A type becomes a groupoid by taking its discrete category, and a map of types becomes a
functor between the discrete categories. This is Mathlib's `CategoryTheory.typeToCat`
corestricted to groupoids, which is what turns a set-valued presheaf into a presheaf of
groupoids and so into a category fibred in groupoids whose fibres are discrete.

## Main definitions

* `CategoryTheory.typeToGrpd`: the functor sending a type to its discrete groupoid.

## Implementation notes

The functoriality proofs are obtained from those of `CategoryTheory.typeToCat` by applying
`CategoryTheory.Cat.Hom.toFunctor`, so the two functors agree after composing with the
forgetful functor from groupoids to categories, by construction rather than by a lemma.
-/

@[expose] public section

namespace CategoryTheory

universe u

/-- A type, regarded as a groupoid: its discrete category. -/
def typeToGrpd : Type u ⥤ Grpd.{u, u} where
  obj X := Grpd.of (Discrete X)
  map f := (typeToCat.map f).toFunctor
  map_id X := congrArg Cat.Hom.toFunctor (typeToCat.map_id X)
  map_comp f g := congrArg Cat.Hom.toFunctor (typeToCat.map_comp f g)

end CategoryTheory

end
