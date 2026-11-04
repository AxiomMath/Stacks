module

public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic

/-!
# Tag 0B8M on a ringed space, in the other invertibility spelling

[Stacks, Tag 0B8M] says that on a ringed space a locally free module of rank one is invertible,
and that the converse holds when every stalk of the structure sheaf is a local ring.

Both implications are proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyTrivialInvertible/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/InvertibleTrivialization/Sheaf.lean`, which carry the tag.
They are stated for `Stacks.SheafOfModules.IsInvertible`, the copy of Tag 01CS's invertibility
predicate whose API the trivialization consumes. The decomposition's own statement of Tag 0B8M
is written in the *other* copy, `AlgebraicGeometry.SheafOfModules.IsInvertible` — the two have
byte-identical definitions and are distinct constants, and
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` is the passage between them.

This file crosses once, so that each implication is available in the spelling a consumer written
against `AlgebraicGeometry.SheafOfModules.IsInvertible` can apply directly. The finite-local-
freeness side needs no crossing: both statements already use
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, the class carrying
`@[stacks 01C6 "(3)"]`.

## Main definitions

None.

## Main results

* `Stacks.InvertibleBridge.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one`: a sheaf
  of modules on a ringed space that is finite locally free of rank one is invertible.
* `Stacks.InvertibleBridge.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: on a
  ringed space whose structure sheaf has local stalks, a sheaf of modules is invertible exactly
  when it is finite locally free of rank one.

## Implementation notes

The universe is written `RingedSpace.{u}`, leaving the ring-value universe of
`RingedSpace.{u, v}` to be inferred. It is not free: `SheafOfModules.{u}` over
`structureSheaf X.sheaf` forces the ring sections to lie in universe `u`, so the elaborated
statements are at `RingedSpace.{u, u}` and agree with the tagged forms, which fix `{u, u}`
outright.

No instance is declared, following the discipline of
`StacksFrontier/AlgebraicGeometry/InvertibleBridge/Basic.lean`: an instance here would make
every `AlgebraicGeometry.SheafOfModules.IsInvertible` goal on a ringed space spawn a search for
finite local freeness of rank one, so that instance search for one of the two predicates would
search for the other.

The two theorems below restate `Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one`
and `Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one` across the bridge. The
tag's third clause — that the converse fails for a general ringed space, witnessed by a one-point
space whose ring has nontrivial Picard group — is
`Stacks.RingedSpace.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one` of
`StacksFrontier/AlgebraicGeometry/InvertibleCounterexample/Clause3.lean`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.InvertibleBridge.RingedSpace

/-- **Clause 1 of Stacks Tag 0B8M, in the `AlgebraicGeometry` spelling of Tag 01CS.** A sheaf of
modules on a ringed space that is finite locally free of rank one is invertible.

This is `Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one`, which carries the
tag, composed with `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. No hypothesis on
the stalks is needed. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1
    (Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X L)

/-- **Clause 2 of Stacks Tag 0B8M, in the `AlgebraicGeometry` spelling of Tag 01CS.** On a ringed
space all of whose structure-sheaf stalks are local rings, a sheaf of modules is invertible if and
only if it is finite locally free of rank one.

This is `Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one`, which carries the
tag, composed with `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one
    (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
        (structureSheaf X.sheaf).property L ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
        (J := Opens.grothendieckTopology X) L 1 :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).symm.trans
    (Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L)

end Stacks.InvertibleBridge.RingedSpace

end
