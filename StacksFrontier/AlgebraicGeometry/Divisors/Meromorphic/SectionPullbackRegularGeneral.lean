module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullbackRegularLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic

/-!
# Stacks 02OY part (2) for a morphism of locally ringed spaces

Let `f : X ⟶ Y` be a morphism of locally ringed spaces for which pullbacks of meromorphic
functions are defined ([Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)) and let `L` be an
invertible `𝒪_Y`-module. Then the pullback of a regular meromorphic section of `L` is a regular
meromorphic section of `f^* L`.

## Main results

* `AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection_of_isInvertible`:
  **part (2) of Tag 02OY**, for an arbitrary morphism of locally ringed spaces.

## Implementation notes

The work is done in
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/SectionPullbackRegularLocal.lean`, which
proves the statement for a module generated near every point by a single section. An invertible
module on a locally ringed space is such a module: that is the converse half of Tag 0B8M,
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible`, whose hypothesis is the
invertibility predicate of `StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`, equivalent to
the one of Tag 01CS by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## References

* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Stacks.ModuleStalk

universe u

namespace AlgebraicGeometry

/-- **Stacks 02OY part (2).** Let `f : X ⟶ Y` be a morphism of locally ringed spaces for which
pullbacks of meromorphic functions are defined and let `L` be an invertible `𝒪_Y`-module. The
pullback of a regular meromorphic section of `L` is a regular meromorphic section of `f^* L`. -/
@[stacks 02OY "part (2)"]
theorem isRegularMeromorphicSection_pullbackMeromorphicSection_of_isInvertible
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (hf : PullbacksMeromorphicSections f)
    (L : SheafOfModules.{u} Y.ringCatSheaf)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property L)
    (s : MeromorphicSection Y.sheaf L) (hs : IsRegularMeromorphicSection Y.sheaf L s) :
    IsRegularMeromorphicSection X.sheaf
      ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj L)
      (pullbackMeromorphicSection f hf L s) := by
  refine isRegularMeromorphicSection_pullbackMeromorphicSection_of_exists_generator f hf L
    (fun y => ?_) s hs
  have hinv : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  obtain ⟨W, hyW, g, hbij⟩ := Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible
    (X := Y.toRingedSpace) L y
  exact ⟨W, hyW, g, fun V hVW => hbij V hVW⟩

end AlgebraicGeometry

end
