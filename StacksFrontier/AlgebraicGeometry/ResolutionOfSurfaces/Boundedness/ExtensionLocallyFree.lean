module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank

/-!
# An extension of the structure sheaf by itself is finite locally free of rank two

For a scheme `X` and a short exact sequence of `𝒪_X`-modules

  `0 ⟶ 𝒪_X ⟶ ℰ ⟶ 𝒪_X ⟶ 0`,

the middle term `ℰ` is finite locally free of rank two, hence finite locally free, hence
quasi-coherent.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_two_of_shortExact_unit`
* `AlgebraicGeometry.isFiniteLocallyFree_of_shortExact_unit`
* `AlgebraicGeometry.isQuasicoherent_of_shortExact_unit`

## Implementation notes

The extension statement is `Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_shortExact` and its
rank-indexed refinement `isFiniteLocallyFreeOfRank_of_shortExact`, which give rank `a + c` from
ranks `a` and `c`. Their outer hypotheses are explicit arguments in the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`.

The instance `AlgebraicGeometry.isFiniteLocallyFree_unit` does not supply them: it is stated in
the different class `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` (the two are related by
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`). Instead
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit` gives the structure sheaf rank
one in the right class, and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree` forgets the
rank. The outer terms of `ShortComplex.mk f g w` are projections of a structure literal, which
reduce to `𝒪_X` only by iota, so instance search does not find these hypotheses and they are
passed as terms.

Quasi-coherence is `Stacks.Chow.isQuasicoherent_of_isFiniteLocallyFree`, stated in the same
class.

The sequence `0 ⟶ 𝒪_X ⟶ ℰ ⟶ 𝒪_X ⟶ 0` is the extension attached to a class in `H¹(X, 𝒪_X)` by
[Stacks, Tag 0B3A] (`Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology`), as in the
proof of [Stacks, Tag 0AXB].

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C7](https://stacks.math.columbia.edu/tag/01C7)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {E : X.Modules}
  (f : SheafOfModules.unit X.ringCatSheaf ⟶ E) (g : E ⟶ SheafOfModules.unit X.ringCatSheaf)
  (w : f ≫ g = 0)

/-- **An extension of `𝒪_X` by `𝒪_X` is finite locally free of rank two.** -/
theorem isFiniteLocallyFreeOfRank_two_of_shortExact_unit
    (hS : (ShortComplex.mk f g w).ShortExact) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 2 :=
  Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hS 1 1
    (SheafOfModules.isFiniteLocallyFreeOfRank_unit X)
    (SheafOfModules.isFiniteLocallyFreeOfRank_unit X)

/-- **An extension of `𝒪_X` by `𝒪_X` is finite locally free.** -/
theorem isFiniteLocallyFree_of_shortExact_unit (hS : (ShortComplex.mk f g w).ShortExact) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
  have := isFiniteLocallyFreeOfRank_two_of_shortExact_unit f g w hS
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 2

/-- **An extension of `𝒪_X` by `𝒪_X` is quasi-coherent.** -/
theorem isQuasicoherent_of_shortExact_unit (hS : (ShortComplex.mk f g w).ShortExact) :
    E.IsQuasicoherent :=
  have := isFiniteLocallyFree_of_shortExact_unit f g w hS
  Stacks.Chow.isQuasicoherent_of_isFiniteLocallyFree E

end AlgebraicGeometry

end
