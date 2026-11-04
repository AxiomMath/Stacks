module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Unconditional

/-!
# Invertible modules are exactly the locally free modules of rank one, for local stalks

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X, x}` are local rings. This file puts
the two halves of [Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) together: a sheaf
of `𝒪_X`-modules is invertible if and only if it is finite locally free of rank one.

The forward implication is
`Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isInvertible`, which is where
the local-ring hypothesis is used, and the converse is
`Stacks.SheafOfModules.Invertible.isInvertible_of_isFiniteLocallyFreeOfRank_one`, which needs
no hypothesis on the stalks at all.

## Main results

* `Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: the equivalence, for the
  `Stacks` spelling of invertibility.
* `Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry`: the
  same equivalence for the `AlgebraicGeometry` spelling, transported along
  `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/


@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))
  [∀ y : X.carrier, IsLocalRing (ringStalk X y)]

/-- On a ringed space all of whose stalks `𝒪_{X, x}` are local rings, a sheaf of `𝒪_X`-modules is
invertible exactly when it is finite locally free of rank one. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one :
    IsInvertible X.presheaf (structureSheafRing X).property L ↔
      Invertible.IsFiniteLocallyFreeOfRank (R := structureSheafRing X) L 1 :=
  ⟨fun h => have := h; Invertible.isFiniteLocallyFreeOfRank_one_of_isInvertible L, fun h => by
    have h' : Invertible.IsFiniteLocallyFreeOfRank
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
          (structureSheafRing X).property) L 1 := h
    exact Invertible.isInvertible_of_isFiniteLocallyFreeOfRank_one L⟩

/-- On a ringed space all of whose stalks are local rings, a sheaf of `𝒪_X`-modules is invertible
in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible` exactly when it is finite locally
free of rank one. -/
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one_algebraicGeometry :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (structureSheafRing X).property L ↔
      Invertible.IsFiniteLocallyFreeOfRank (R := structureSheafRing X) L 1 :=
  (isInvertible_iff_algebraicGeometry X.presheaf (structureSheafRing X).property L).symm.trans
    (isInvertible_iff_isFiniteLocallyFreeOfRank_one L)

end Stacks.SheafOfModules

end
