module

public import StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal

/-!
# A two-sided tensor inverse is unique up to a canonical isomorphism

`Stacks.TensorPowers.TensorInverse L` is *data*: an object `N` together with isomorphisms
`L ⊗ N ≅ 𝟙_` and `N ⊗ L ≅ 𝟙_`. The module documentation of
`StacksFrontier.AlgebraicGeometry.TensorPowers.Monoidal` records that it is data and not a
`Prop`, so that "no two-sided tensor inverse is canonical here", and it proves nothing relating
two of them. This file supplies that relation, in a monoidal category and with no hypothesis
beyond `MonoidalCategory`:

* any two two-sided tensor inverses of one object are isomorphic;
* a two-sided tensor inverse transports along an isomorphism of the object it inverts;
* hence inverses of isomorphic objects are isomorphic.

## Main definitions

* `Stacks.CartierConormal.TensorInverse.ofIso`: the transport of a two-sided tensor inverse of
  `L` along an isomorphism `L ≅ L'`, with the *same* underlying object.

## Main results

* `Stacks.CartierConormal.TensorInverse.invIso`: `a.inv ≅ b.inv` for any two
  `a b : TensorInverse L`.
* `Stacks.CartierConormal.TensorInverse.invIsoOfIso`: `a.inv ≅ b.inv` for
  `a : TensorInverse L`, `b : TensorInverse L'` and an isomorphism `L ≅ L'`.

## Route

`invIso` is the usual five-step chain, written as a composite of five isomorphisms with no
tactic:

`a.inv ≅ 𝟙_ ⊗ a.inv ≅ (b.inv ⊗ L) ⊗ a.inv ≅ b.inv ⊗ (L ⊗ a.inv) ≅ b.inv ⊗ 𝟙_ ≅ b.inv`,

by the left unitor, `b.mulIso'` whiskered on the right, the associator, `a.mulIso` whiskered on
the left, and the right unitor. `ofIso` keeps the inverse object and conjugates the two
structure isomorphisms by the given one. `invIsoOfIso` is the composite of the two.

No coherence is claimed: nothing here says that `invIso` is compatible with composition of
inverses, that `invIso a a` is the identity, or that `invIso` commutes with the tensor and power
operations of `Stacks.TensorPowers.TensorInverse`. Those would need the normalisation of
`addIso` that the sibling file explicitly does not develop.

## Universe situation

Fully polymorphic, inherited from the sibling file: `C : Type u` with `[Category.{v} C]`, `u`
and `v` independent, no constraint between them and no constraint on the objects.

## Why this is here

It is a named input of [Stacks, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)'s
`"normal sheaf"` clause, which asserts that the dual of a pullback is the pullback of the dual
for an invertible module. The route to that clause identifies both sides as two-sided tensor
inverses of one object and concludes by uniqueness; this is the uniqueness step, and it was the
only step of that route with no statement anywhere in the repository. See the module
documentation of `StacksFrontier.AlgebraicGeometry.CartierConormal.Basic` for the remainder of
that route and the step that is still missing.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace Stacks.CartierConormal

namespace TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **A two-sided tensor inverse is unique up to isomorphism.** For two two-sided tensor
inverses `a` and `b` of the same object `L`, the chain

`a.inv ≅ 𝟙_ ⊗ a.inv ≅ (b.inv ⊗ L) ⊗ a.inv ≅ b.inv ⊗ (L ⊗ a.inv) ≅ b.inv ⊗ 𝟙_ ≅ b.inv`

uses `b` on the left of `L` and `a` on the right of it, so both two-sidedness isomorphisms are
spent and neither braiding nor symmetry is needed. -/
noncomputable def invIso {L : C} (a b : Stacks.TensorPowers.TensorInverse L) : a.inv ≅ b.inv :=
  (λ_ a.inv).symm ≪≫ whiskerRightIso b.mulIso'.symm a.inv ≪≫ α_ b.inv L a.inv ≪≫
    whiskerLeftIso b.inv a.mulIso ≪≫ ρ_ b.inv

/-- **A two-sided tensor inverse transports along an isomorphism of the object it inverts**, with
the same underlying inverse object: conjugate each structure isomorphism by the given one. -/
noncomputable def ofIso {L L' : C} (a : Stacks.TensorPowers.TensorInverse L) (e : L ≅ L') :
    Stacks.TensorPowers.TensorInverse L' where
  inv := a.inv
  mulIso := whiskerRightIso e.symm a.inv ≪≫ a.mulIso
  mulIso' := whiskerLeftIso a.inv e.symm ≪≫ a.mulIso'

/-- The inverse object of `ofIso a e` is the inverse object of `a`. -/
@[simp]
theorem ofIso_inv {L L' : C} (a : Stacks.TensorPowers.TensorInverse L) (e : L ≅ L') :
    (ofIso a e).inv = a.inv := rfl

/-- **Two-sided tensor inverses of isomorphic objects are isomorphic.** Transport `a` along `e`
by `Stacks.CartierConormal.TensorInverse.ofIso` and compare with `b` by
`Stacks.CartierConormal.TensorInverse.invIso`. -/
noncomputable def invIsoOfIso {L L' : C} (a : Stacks.TensorPowers.TensorInverse L)
    (b : Stacks.TensorPowers.TensorInverse L') (e : L ≅ L') : a.inv ≅ b.inv :=
  invIso (ofIso a e) b

end TensorInverse

end Stacks.CartierConormal

end
