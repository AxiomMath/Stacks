module

public import StacksFrontier.CategoryTheory.Sites.Presheaf.AlgebraicStructure.Sheaves
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# Ringed topoi

A ringed topos is a site together with an ordinary sheaf of commutative rings on it, that
is, an object of `Sheaf J CommRingCat`. Its underlying topos of sheaves of sets is
`Sheaf J (Type w)`, and forgetting the ring operations of the structure sheaf is
composition with the forgetful functor.

## Main definitions

* `AlgebraicGeometry.RingedTopos`: a site together with its structure sheaf of commutative
  rings.
* `AlgebraicGeometry.RingedTopos.Topos`: the underlying topos of sheaves of sets.
* `AlgebraicGeometry.RingedTopos.forgetRing`: the functor forgetting the ring operations of
  a sheaf of commutative rings on the site.

## Implementation notes

The site and the universe of the values of the structure sheaf are independent, so a
`RingedTopos` carries three universe parameters: the morphisms and the objects of the site,
and the sections of the structure sheaf.

## References

* [Stacks, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace AlgebraicGeometry

/-- A site with a sheaf of commutative rings. -/
@[stacks 01D3 "part (1): ringed topoi",
  sga "4 Vbis 1.3.1" "absolute case (D = pt)",
  sga "4 IV 11.1.1" "ringed topos"]
structure RingedTopos.{v₁, u₁, w₁} where
  /-- The category of the site. -/
  C : Type u₁
  /-- Morphisms in the site. -/
  [category : Category.{v₁} C]
  /-- The topology of the site. -/
  J : GrothendieckTopology C
  /-- The structure sheaf and its commutative ring operations. -/
  O : Sheaf J CommRingCat.{w₁}

attribute [instance] RingedTopos.category

namespace RingedTopos

/-- The underlying topos of sheaves of sets. -/
abbrev Topos (X : RingedTopos.{v, u, w}) := Sheaf X.J (Type w)

/-- Forget the operations of a sheaf of commutative rings. -/
noncomputable abbrev forgetRing (X : RingedTopos.{v, u, w}) :=
  sheafCompose X.J (forget CommRingCat.{w})

end RingedTopos

end AlgebraicGeometry
