module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.Topology.Sober.Local
public import StacksFrontier.Topology.Sober.NoetherianSurjection

/-!
# Generic points on a locally Noetherian algebraic space

Every irreducible closed subset of the point space of a locally Noetherian algebraic space has
a generic point: `|X|` is quasi-sober.

The reason is purely topological. An étale scheme atlas presents `|X|` as the image of a
continuous open surjection from the topological space of a scheme, which is quasi-sober and —
local Noetherianity being an étale-local property — locally Noetherian. A continuous
surjection from a *Noetherian* quasi-sober space has quasi-sober target, because the preimage
of an irreducible closed set is a closed set and therefore a *finite* union of irreducible
closed sets, whose generic points have finitely many closed images covering the target set;
irreducibility then selects one of them. Patching that over a cover by Noetherian opens gives
the locally Noetherian statement.

## Main results

* `AlgebraicGeometry.Space.quasiSober_points_of_isLocallyNoetherian`: the point space of a
  locally Noetherian algebraic space over `S` is quasi-sober.  The purely topological inputs
  are `quasiSober_of_noetherianSpace_surjective` and
  `quasiSober_of_isLocallyNoetherianSpace_isOpenMap_surjective` of
  `StacksFrontier/Topology/Sober/NoetherianSurjection.lean`.

## Implementation notes

Openness of the map is needed only to patch: it is what makes the image of a Noetherian open
subset an open subset of the target, so that
`quasiSober_iff_of_open_cover` applies. The Noetherian core needs continuity and surjectivity
only.

Nothing here assumes the algebraic space decent or Zariski locally quasi-separated. The source
derives quasi-soberness of `|X|` for a Zariski locally quasi-separated algebraic space
(Tag 06NJ) from the density of the schematic locus (Tag 06NH, which rests on Tag 086U); that
route is unavailable in this development, and the Noetherian hypothesis replaces it. The two
statements are independent: neither of "locally Noetherian" and "Zariski locally
quasi-separated" implies the other.

Local Noetherianity of an algebraic space is
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of Tag 03E6 attached to
`AlgebraicGeometry.IsLocallyNoetherian`, and the passage from it to local Noetherianity of the
point space is `AlgebraicGeometry.Space.isLocallyNoetherianSpace_of_isLocallyNoetherian` of
Tag 04ZF.

## References

* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 06N9](https://stacks.math.columbia.edu/tag/06N9)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The point space of a locally Noetherian algebraic space over `S` is quasi-sober: every
irreducible closed set of points has a generic point.

An étale scheme atlas is a continuous open surjection onto the points, its own point space is
homeomorphic to the topological space of a scheme by clause (1) of Tag 03BX — hence
quasi-sober — and local Noetherianity of the algebraic space makes that scheme locally
Noetherian, so Tag 04ZF makes the atlas's point space locally Noetherian as well. -/
theorem quasiSober_points_of_isLocallyNoetherian (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    QuasiSober (points B S hS X) := by
  obtain ⟨U, φ, hsurj, hetale, hUnoeth⟩ := hN
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hUnoeth
  have : QuasiSober (points B S hS (yoneda.obj U)) :=
    (schemePointsHomeomorph B S hS U).isOpenEmbedding.quasiSober
  exact quasiSober_of_isLocallyNoetherianSpace_isOpenMap_surjective
    ((_root_.AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj U)).of_homeomorph
      (schemePointsHomeomorph B S hS U).symm)
    (f := pointsMap B S hS (yoneda.obj U) φ) (continuous_pointsMap B S hS φ)
    (isOpenMap_pointsMap_of_etale B S hS hX U φ hetale)
    ((surjective_iff_surjective_pointsMap B S hS X hX U φ).mp hsurj)

end AlgebraicGeometry.Space

end
