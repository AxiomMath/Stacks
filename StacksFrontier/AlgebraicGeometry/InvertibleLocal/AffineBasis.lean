module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TrivializingAffineCover
public import StacksFrontier.AlgebraicGeometry.InvertibleLocal.Basic

/-!
# The affine opens trivializing an invertible module form a basis

Let `L` be an invertible module on a scheme `X`. Being locally trivial, `L` is isomorphic to the
structure sheaf over each member of some open cover; the members of that cover are arbitrary
opens, and a trivialization restricts along an inclusion of opens, so the opens over which `L`
is trivial are closed under shrinking. Since the affine opens form a basis of the topology, the
*affine* opens over which `L` is trivial therefore form a basis of the topology as well.

This is the local triviality that a construction working chart by chart on an affine cover
needs: not merely that `X` is covered by trivializing affine opens, but that a trivializing
affine open can be found inside any given open around any given point.

## Main results

* `Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible`: every point of an open
  `W` of `X` has an affine open neighbourhood inside `W` on which `L` restricts to the structure
  sheaf.
* `Stacks.Modules.exists_affineOpen_pullback_iso_unit_of_isInvertible`: the same with the
  restriction spelled as the pullback along the open immersion, which is the form the module
  pullback calculus consumes.

## Implementation notes

Shrinking a trivialization is done in the localized-site spelling `L.over U ≅ 𝒪|_U`, where
`Stacks.SheafOfModules.isoUnitOverOfHom` restricts it along an arbitrary morphism of the site;
the two translations to the open-subscheme spelling `Scheme.Modules.restrict L U.ι ≅ 𝒪_U` are
`Stacks.Modules.overIsoUnitOfRestrictIsoUnit` and
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`. Nothing is computed
sectionwise.

The hypothesis is `AlgebraicGeometry.SheafOfModules.IsInvertible`, the class the Bertini
situation carries; it is converted to the class both halves of [Stacks, Tag 0B8M] are stated in
by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Modules

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **An invertible module is trivial on an affine open neighbourhood of every point of every
open.** The trivializing opens cover `X` and a trivialization restricts along an inclusion of
opens, so a trivializing open can be shrunk to an affine one inside any prescribed open. -/
theorem exists_affineOpen_restrict_iso_unit_of_isInvertible {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W ∧
      Nonempty (Scheme.Modules.restrict L V.ι ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›
  obtain ⟨U, hU, hiso⟩ := exists_restrict_iso_unit_of_isInvertible L
  obtain ⟨y, hy⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ y, U y by rw [hU]; exact Opens.mem_top _)
  obtain ⟨V, hV, hxV, hVle⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ W ⊓ U y from ⟨hx, hy⟩)
  refine ⟨V, hV, hxV, hVle.trans inf_le_left, ⟨?_⟩⟩
  exact Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit V L
    (Stacks.SheafOfModules.isoUnitOverOfHom L (homOfLE (hVle.trans inf_le_right))
      (overIsoUnitOfRestrictIsoUnit L (U y) (hiso y).some))

/-- **An invertible module has trivial pullback on an affine open neighbourhood of every point of
every open.** This is `exists_affineOpen_restrict_iso_unit_of_isInvertible` with the restriction
read as the pullback along the open immersion, through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
theorem exists_affineOpen_pullback_iso_unit_of_isInvertible {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  obtain ⟨V, hV, hxV, hVW, ⟨e⟩⟩ := exists_affineOpen_restrict_iso_unit_of_isInvertible L hx
  exact ⟨V, hV, hxV, hVW, ⟨((Scheme.Modules.restrictFunctorIsoPullback V.ι).app L).symm ≪≫ e⟩⟩

end Stacks.Modules

end
