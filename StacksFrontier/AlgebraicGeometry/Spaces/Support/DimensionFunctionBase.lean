module

public import StacksFrontier.AlgebraicGeometry.Spaces.Catenary
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.Topology.Dimension.DimensionFunction

/-!
# A base algebraic space with a dimension function

The theory of cycles on an algebraic space is developed over a base which is quasi-separated,
locally Noetherian and universally catenary, and which is equipped with a dimension function on
its topological space of points. This file bundles that standing datum.

## Main definitions

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation` is the base algebraic space together
  with its separation, Noetherian and catenary hypotheses and the chosen dimension function.

## Implementation notes

The algebraic space is a presheaf on a chosen big fppf site over a base scheme. The site is
required to contain both that scheme and the terminal scheme; the latter is what makes the
*absolute* quasi-separatedness predicate `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`
available, since it is formed after relocalizing over `Spec ℤ`. Local Noetherianity is the
étale-local scheme property `AlgebraicGeometry.IsLocallyNoetherian` in the sense of
`AlgebraicGeometry.Space.HasEtaleLocalProperty`. The dimension function is
`TopologicalSpace.DimensionFunction` for the canonical topology
`AlgebraicGeometry.Space.pointTopology` on the points of the space, installed as a local
instance in the type of the field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-- A quasi-separated, locally Noetherian, universally catenary algebraic space over a base
scheme, together with a dimension function on its points: the standing base datum for the
theory of cycles on algebraic spaces. -/
structure BaseSpaceDimensionSituation where
  /-- The ambient big fppf site. -/
  site : BigFppfSite.{u}
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The base belongs to the chosen site. -/
  base_mem : site.Contains base
  /-- The terminal scheme belongs to the chosen site. -/
  terminal_mem : site.Contains (⊤_ Scheme.{u})
  /-- The algebraic space over the base. -/
  space : (BigFppfOver site base base_mem)ᵒᵖ ⥤ Type u
  /-- The presheaf is an algebraic space. -/
  isAlgebraicSpace : IsAlgebraicSpace site base base_mem space
  /-- The algebraic space is quasi-separated. -/
  quasiSeparated : IsAbsolutelyQuasiSeparated site base base_mem terminal_mem space
  /-- The algebraic space is locally Noetherian. -/
  locallyNoetherian : HasEtaleLocalProperty site base base_mem space
    (fun T : Scheme.{u} => IsLocallyNoetherian T)
  /-- The algebraic space is universally catenary. -/
  universallyCatenary : IsUniversallyCatenary site base base_mem space
  /-- The chosen dimension function on the points of the algebraic space. -/
  delta :
    letI : TopologicalSpace (points site base base_mem space) :=
      pointTopology site base base_mem space
    DimensionFunction (points site base base_mem space)

end AlgebraicGeometry.Space

end
