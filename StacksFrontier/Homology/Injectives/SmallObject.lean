module

public import Mathlib.CategoryTheory.Presentable.Basic
public import StacksFrontier.Order.Stacks0030
import StacksCore.Tactic.StacksAttribute

/-!
# Objects small with respect to a class of morphisms

Let `𝒞` be a category, let `I` be a class of morphisms of `𝒞` and let `α` be an ordinal. An
object `A` of `𝒞` is `α`-small with respect to `I` when, for every system `B` indexed by `α`
all of whose transition morphisms lie in `I`, the canonical map
`colim_i Hom(A, B i) ⟶ Hom(A, colim_i B i)` is bijective. This is the smallness notion that
drives the small object argument, and it is the content of Tag 05NS.

## Main definitions

* `Stacks.Injectives.IsSmallWithRespectTo`: an object is `α`-small with respect to a class of
  morphisms.

## Main results

There are no results beyond the definition.

## Implementation notes

An ordinal `α` is represented by its canonical well-ordered type `α.ToType`, and a system
indexed by it is a `CategoryTheory.System`. Rather than naming the comparison map and
asserting that it is bijective, the condition is expressed as `PreservesColimit` for the
covariant representable functor `coyoneda.obj (.op A)`: preservation of the colimit is
precisely bijectivity of that canonical map, and this formulation makes the standard
colimit-preservation API available directly.

Mathlib's presentability notions (`CategoryTheory.IsCardinalPresentable` and friends) are a
different condition: they quantify over all cardinal-filtered colimits rather than over
ordinal-indexed systems with transition morphisms in a prescribed class, so they cannot be
used here.

## References

* [Stacks Project, Tag 05NS](https://stacks.math.columbia.edu/tag/05NS)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.Injectives

/-- An object `A` is `α`-small with respect to `I` if `Hom(A, -)` preserves the colimit of
every `α`-indexed system all of whose transition morphisms belong to `I`. -/
@[stacks 05NS]
abbrev IsSmallWithRespectTo {C : Type u} [Category.{v} C] (A : C)
    (I : MorphismProperty C) (α : Ordinal.{w}) : Prop :=
  ∀ B : System α.ToType C, (∀ {i j : α.ToType} (f : i ⟶ j), I (B.map f)) →
    Limits.PreservesColimit B (coyoneda.obj (.op A))

end Stacks.Injectives
