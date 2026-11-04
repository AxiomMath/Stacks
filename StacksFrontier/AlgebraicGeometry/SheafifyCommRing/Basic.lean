module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Left exact sheafification of sheaves of commutative rings in a larger universe

Let `(C, J)` be a site with `C : Type u` and `Category.{v} C`. Sheafification of
`CommRingCat`-valued presheaves on `(C, J)` exists, and is left exact, even when the universe
of the rings is strictly larger than the universes of the site.

Mathlib's left exact sheafification for a concrete category is stated at the coefficient
universe of the site, so it answers for `CommRingCat.{max u v}` and not for
`CommRingCat.{max u v w}`. The construction is insensitive to the enlargement: the colimits
that the plus construction takes are indexed by the covering sieves of `(C, J)`, and the limits
it compares them against are finite, so both are small relative to the enlarged coefficient
universe and are obtained by shrinking.

## Main results

* `Stacks.SheafifyCommRing.hasSheafifyCommRingCat`: sheafification of `CommRingCat.{max u v w}`
  valued presheaves on a site `C : Type u` with `Category.{v} C` exists and preserves finite
  limits.

## Implementation notes

This strengthens `CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat`, which gives the adjunction
at this same signature but not its left exactness, by the two shrinking steps on the limit side
that the left exact statement additionally needs. `CategoryTheory.HasSheafify` is the conjunction
of the two (`CategoryTheory.HasSheafify.isRightAdjoint` and
`CategoryTheory.HasSheafify.isLeftExact`), so the weak instance is recovered from this one and
the two do not compete: `HasSheafify` is a `Prop`.

The four `let`s are the whole content. `CategoryTheory.hasSheafify` asks, for a concrete
category, for colimits indexed by the covering sieves and for finite limits, together with the
preservation of each by the forgetful functor; `CommRingCat.{max u v w}` has all four at its own
size, and `CategoryTheory.Limits.hasColimitsOfSizeShrink`,
`CategoryTheory.Limits.hasLimitsOfSizeShrink`,
`CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink` and
`CategoryTheory.Limits.preservesLimitsOfSize_shrink` move each down to the size of the site.
None of the four is a global instance in Mathlib — `preservesColimitsOfSize_shrink` is
documented there as looping when it is one — so they have to be put into the local context by
hand, which is why this is a tactic proof of a `Prop` rather than an instance chain.

The enlargement is what makes the statement non-vacuous, and the measurement is worth
recording, because the weaker class is the one that was available. At this pin, with
`Mathlib.CategoryTheory.Sites.LeftExact` and the three `Mathlib.Algebra.Category.Ring` limit
files imported, instance search finds `HasSheafify J CommRingCat.{max u v}` and
`HasSheafify (Opens.grothendieckTopology X) CommRingCat.{u}` unaided; it does not find
`HasSheafify J CommRingCat.{max u v w}`, while it does find
`HasWeakSheafify J CommRingCat.{max u v w}`. Importing `Sites.LeftExact` alone is not enough for
any of them: the `CommRingCat` limit and colimit instances are needed as well, and that import
gap, rather than any absence, is what a failure to synthesize the class at the equal-universe
signature records.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.SheafifyCommRing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification of presheaves of commutative rings exists and is left exact, with the rings
in a universe at least as large as the universes of the site. -/
instance hasSheafifyCommRingCat : HasSheafify J CommRingCat.{max u v w} := by
  let : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget CommRingCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_shrink (forget CommRingCat.{max u v w})
  let : HasColimitsOfSize.{max u v, max u v} CommRingCat.{max u v w} :=
    hasColimitsOfSizeShrink CommRingCat.{max u v w}
  let : HasLimitsOfSize.{max u v, max u v} CommRingCat.{max u v w} :=
    hasLimitsOfSizeShrink CommRingCat.{max u v w}
  let : PreservesLimitsOfSize.{max u v, max u v} (forget CommRingCat.{max u v w}) :=
    preservesLimitsOfSize_shrink (forget CommRingCat.{max u v w})
  infer_instance

end Stacks.SheafifyCommRing

end
