module

public import StacksFrontier.AlgebraicGeometry.InvertibleCounterexample.OnePoint
public import StacksFrontier.RingTheory.Picard.InvertibleNotFree

/-!
# Invertible does not imply finite locally free of rank one

This file states the counterexample of Stacks Tag 0B8M: there is a ringed space carrying an
invertible sheaf of modules that is not finite locally free of rank one. It is obtained by
feeding the one-point ringed space construction of
`StacksFrontier/AlgebraicGeometry/InvertibleCounterexample/OnePoint.lean` with the invertible
non-free module of `StacksFrontier/RingTheory/Picard/InvertibleNotFree.lean`, the class of the
ideal `(2, 1 + √-5)` of `ℤ[√-5]` in the Picard group of that ring.

Together with `Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one` and
`Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one` this completes Tag 0B8M:
finite local freeness of rank one always implies invertibility; the converse holds when every
stalk of the structure sheaf is a local ring; and this file shows the converse fails without
that hypothesis, so it cannot be dropped.

## Main results

* `Stacks.RingedSpace.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one`: clause 3 of
  Tag 0B8M.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.RingedSpace

/-- **Clause 3 of Stacks Tag 0B8M.** On a general ringed space an invertible sheaf of modules
need not be finite locally free of rank one: there is a ringed space `X` and a sheaf of
`𝒪_X`-modules `L` with `L` invertible and `L` not finite locally free of rank one.

The witness is the one-point ringed space whose ring of global sections is `ℤ[√-5]`, carrying
the sheaf of modules attached to the non-principal invertible ideal `(2, 1 + √-5)`. Its single
stalk is `ℤ[√-5]`, which is not a local ring; this is exactly what the local-stalk hypothesis of
`Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one` rules out. -/
@[stacks 0B8M "the converse fails for general ringed spaces"]
theorem exists_isInvertible_not_isFiniteLocallyFreeOfRank_one :
    ∃ (X : AlgebraicGeometry.RingedSpace.{u})
      (L : SheafOfModules.{u} (structureSheaf X.sheaf)),
      Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L ∧
        ¬AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
          (C := Opens X) (J := Opens.grothendieckTopology X) L 1 :=
  exists_isInvertible_not_isFiniteLocallyFreeOfRank_one_of
    Stacks.InvertibleNotFree.Base.{u} Stacks.InvertibleNotFree.Witness.{u}
    Stacks.InvertibleNotFree.not_free.{u}

end Stacks.RingedSpace

end
