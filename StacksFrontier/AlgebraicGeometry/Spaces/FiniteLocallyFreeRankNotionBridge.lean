module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree

/-!
# The two notions of a finite locally free module on an algebraic space

Let `X` be an algebraic space and `ℰ` an `𝒪_X`-module on the small étale site of `X`. Two
readings of "`ℰ` is finite locally free (of rank `r`)" are in use in the library:

* the site readings, imposed over a covering family of *every* object of the small étale
  ringed site: `SheafOfModules.IsFiniteLocallyFreeOnSite` (Stacks 03DL (2)) and
  `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` (the rank clause of Stacks 0409);
* the local-generators readings, imposed over a covering of the *terminal* object of the same
  site with the same structure sheaf `structureRingSheaf`:
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` (Stacks 01C6 (2)) and
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` (Stacks 01C6 (3)).

This file records that on the small étale site of an algebraic space the two readings agree,
in both the unranked and the ranked form.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_sheafOfModules` and
  `AlgebraicGeometry.Space.isFiniteLocallyFree_sheafOfModules_of_isFiniteLocallyFreeOfRank`: a
  module of rank `r` in the sense of Stacks 0409 is finite locally free, and of rank `r`, in the
  sense of Stacks 01C6.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_sheafOfModules`: the same for the unranked
  notions.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_sheafOfModules` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_of_sheafOfModules`: the converses, and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_sheafOfModules`,
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_iff_sheafOfModules` the equivalences.

## Implementation notes

The ring sheaf `Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O`
over which `AlgebraicGeometry.Space.Modules` is indexed is `structureRingSheaf B S hS X` by
definition, so no transport of the module is needed; the module is restated through `show`
exactly as the consumers of the local-generators readings state it.  Both comparisons are
general facts about a site whose slice topologies admit sheafification:
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_iff_sheafOfModules` for the ranked
notions, and `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`
with `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree` for the unranked
ones.  The slice instances for the small étale site are
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}

/-- **A module of rank `r` on the small étale site of an algebraic space (Stacks 0409) has rank
`r` in the local-generators sense of Stacks 01C6 (3)**, over the structure ring sheaf. -/
theorem isFiniteLocallyFreeOfRank_sheafOfModules
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) r :=
  RingedSite.isFiniteLocallyFreeOfRank_sheafOfModules _ E hr

/-- **A module of rank `r` on the small étale site of an algebraic space (Stacks 0409) is finite
locally free in the local-generators sense of Stacks 01C6 (2)**, over the structure ring
sheaf. -/
theorem isFiniteLocallyFree_sheafOfModules_of_isFiniteLocallyFreeOfRank
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) :=
  have := isFiniteLocallyFreeOfRank_sheafOfModules E hr
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r

/-- **A finite locally free module on the small étale site of an algebraic space (Stacks 03DL
(2)) is finite locally free in the local-generators sense of Stacks 01C6 (2)**, over the
structure ring sheaf. -/
theorem isFiniteLocallyFree_sheafOfModules (h : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) :=
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite E h

/-- **A module of rank `r` in the local-generators sense of Stacks 01C6 (3) on the small étale
site of an algebraic space has rank `r` in the sense of Stacks 0409.** -/
theorem isFiniteLocallyFreeOfRank_of_sheafOfModules
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) r] :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r :=
  RingedSite.isFiniteLocallyFreeOfRank_of_sheafOfModules _ E r h

/-- **A module finite locally free in the local-generators sense of Stacks 01C6 (2) on the small
étale site of an algebraic space is finite locally free in the sense of Stacks 03DL (2).** -/
theorem isFiniteLocallyFreeOnSite_of_sheafOfModules
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] :
    SheafOfModules.IsFiniteLocallyFreeOnSite E :=
  Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree E h

/-- **The two rank conditions agree on the small étale site of an algebraic space**: the rank
clause of Stacks 0409 and the rank condition of Stacks 01C6 (3) over the structure ring
sheaf. -/
theorem isFiniteLocallyFreeOfRank_iff_sheafOfModules :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
        (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) r :=
  ⟨isFiniteLocallyFreeOfRank_sheafOfModules E,
    fun _ => isFiniteLocallyFreeOfRank_of_sheafOfModules E⟩

/-- **The two finite-local-freeness conditions agree on the small étale site of an algebraic
space**: Stacks 03DL (2) and Stacks 01C6 (2) over the structure ring sheaf. -/
theorem isFiniteLocallyFreeOnSite_iff_sheafOfModules :
    SheafOfModules.IsFiniteLocallyFreeOnSite E ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
        (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) :=
  ⟨isFiniteLocallyFree_sheafOfModules E, fun _ => isFiniteLocallyFreeOnSite_of_sheafOfModules E⟩

end AlgebraicGeometry.Space

end
