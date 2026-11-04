module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSection

/-!
# An invertible module on a scheme is quasi-coherent

Let `X` be a scheme and let `L` be an invertible `𝒪_X`-module. This file proves that `L` is
quasi-coherent.

The route is the converse clause of [Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M),
`Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isInvertible`: on a ringed
space whose structure-sheaf stalks are local rings — a scheme — an invertible module is finite
locally free of rank one. The local generators it supplies are locally free data, and locally
free data with no relations is quasi-coherent data.

This is the one missing link between the order-of-vanishing calculus of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`, which models a meromorphic section by its
value in the generic stalk, and the sheaf `𝒦_X(L)` of meromorphic sections of Stacks 01X4: the
comparison of the two
(`Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk`) is stated for a quasi-coherent module,
while the statements of chapter 42 hypothesize only invertibility.

## Main results

* `Stacks.Divisors.isQuasicoherent_of_isInvertible` — an invertible `𝒪_X`-module is
  quasi-coherent. Registered as an instance.
* `Stacks.Divisors.isInvertible_presheaf` — the change of spelling of the invertibility
  hypothesis between the chapter-42 statements and the rest of this library.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- The invertibility hypothesis of the chapter-42 statements, restated in the spelling that
`Stacks.Divisors.isTrivializedNear_of_isInvertible` and
`Stacks.Chow.meromorphicDivisorCycleOfInvertible` take. The two differ only in how the structure
sheaf and its sheaf condition are spelled. -/
theorem isInvertible_presheaf {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
  ‹AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›

/-- **An invertible module on a scheme is quasi-coherent.** By the converse clause of Stacks 0B8M
an invertible module on a space with local stalks is finite locally free of rank one, so it has
local generators which are locally free data; adjoining no relations turns those into
quasi-coherent data.

No Stacks attribute is attached: this is a consequence of one clause of Tag 0B8M together with
Tag 01C6, not a tagged statement in its own right. -/
instance (priority := 100) isQuasicoherent_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    L.IsQuasicoherent := by
  have _ := Stacks.ChernCap42.isInvertible_stacks_of_algebraicGeometry L
  have h := Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (X := X.toRingedSpace) L
  obtain ⟨q, hfree, -⟩ := h.exists_isFiniteLocallyFreeOfRankData
  have _ : q.IsLocallyFreeData := hfree
  exact q.quasiCoherentData.isQuasicoherent

end Stacks.Divisors

end
