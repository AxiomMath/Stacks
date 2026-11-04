module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# Categories fibred in setoids (Stacks 04SA)

Stacks Tag `04SA` (Definition 4.39.1): a functor `p : 𝒳 ⥤ 𝒮` is *fibred in setoids* when it
is fibred in groupoids and each of its fibre categories is a setoid.

A *setoid* is a groupoid in which every object has exactly one automorphism, i.e. a thin
groupoid (Stacks `02XZ`): `CategoryTheory.IsGroupoid` together with `Quiver.IsThin`. The
fibres of a category fibred in groupoids are automatically groupoids — this is
`CategoryTheory.Functor.IsFiberedInGroupoids.fiber_isGroupoid`, half of Stacks `003V` — so
the only extra content of "fibred in setoids" beyond "fibred in groupoids" is thinness of
the fibres, and that is the shape used here.

## Main definitions

* `CategoryTheory.Functor.IsFiberedInSetoids`: the functor is fibred in setoids.

## Implementation notes

The "fibred in groupoids" hypothesis is the predicate
`CategoryTheory.Functor.IsFiberedInGroupoids` (Stacks `003S`), recorded as a field rather
than as `extends`, since that predicate is a `structure … : Prop` and not a class. Its
equivalence with "fibred category all of whose fibres are groupoids" is available as
`Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid`, with constructor
`IsFiberedInGroupoids.mk'` and projections `.isFibered` and `.fiber_isGroupoid`.

## References

* [Stacks Project, Definition 4.39.1 (Tag 04SA)](https://stacks.math.columbia.edu/tag/04SA)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- **Stacks 04SA.** A functor `p : 𝒳 ⥤ 𝒮` is a *category fibred in setoids* if it is
fibred in groupoids and each fibre category `p.Fiber S` is a setoid, i.e. thin (its fibres
are groupoids automatically, by Stacks `003V`). -/
@[stacks_fixed 04SA]
class IsFiberedInSetoids (p : 𝒳 ⥤ 𝒮) : Prop where
  /-- `p` is fibred in groupoids (Stacks `003S`). -/
  isFiberedInGroupoids : p.IsFiberedInGroupoids
  /-- Every fibre category of `p` is thin: between two objects of a fibre there is at most
  one morphism lying over the identity. -/
  fiber_isThin : ∀ S : 𝒮, Quiver.IsThin (p.Fiber S)

/-- The fibres of a category fibred in setoids are groupoids, hence setoids. -/
theorem IsFiberedInSetoids.fiber_isGroupoid (p : 𝒳 ⥤ 𝒮) [hp : p.IsFiberedInSetoids]
    (S : 𝒮) : IsGroupoid (p.Fiber S) :=
  hp.isFiberedInGroupoids.fiber_isGroupoid S

end CategoryTheory.Functor
