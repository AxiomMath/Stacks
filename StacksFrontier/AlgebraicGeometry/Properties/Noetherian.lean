module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Topology.Noetherian.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian schemes have Noetherian topological spaces

The underlying topological space of a Noetherian scheme is Noetherian, and the underlying
topological space of a locally Noetherian scheme is locally Noetherian. The global assertion is
already Mathlib's `AlgebraicGeometry.IsNoetherian.noetherianSpace`, which carries Tag 01OZ
upstream; the local assertion is proved here. A quasi-compact open subscheme of a locally
Noetherian scheme is Noetherian, and therefore has finitely many irreducible components.

## Main results

* `AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian`: the space underlying a
  locally Noetherian scheme is locally Noetherian.
* `AlgebraicGeometry.finite_irreducibleComponents_of_isCompact`: a quasi-compact open of a
  locally Noetherian scheme has finitely many irreducible components.

## Implementation notes

The local assertion uses `TopologicalSpace.IsLocallyNoetherianSpace`: every point has an open
neighbourhood whose induced topology is Noetherian.

Tag 01OZ is the conjunction of the two halves its parenthesis abbreviates, so its covering set has
two members. The global half is `AlgebraicGeometry.IsNoetherian.noetherianSpace`, which already
carries `@[stacks 01OZ]` in Mathlib itself at this pin, so no registration for it is needed here.
The attribute below carries the remaining, local half, which Mathlib does not state. The
attribute below carries the remaining, local half, which Mathlib does not state.

A quasi-compact open subscheme is Noetherian because `AlgebraicGeometry.IsNoetherian` is exactly
`IsLocallyNoetherian` together with `CompactSpace`, both of which it inherits; its finitely many
irreducible components are then those of a Noetherian space.

## References

* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
-/

public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The underlying topological space of a locally Noetherian scheme is locally Noetherian. -/
@[stacks 01OZ "the (locally) half: a locally Noetherian scheme has a locally Noetherian space"]
theorem isLocallyNoetherianSpace_of_isLocallyNoetherian
    (X : Scheme) [IsLocallyNoetherian X] :
    IsLocallyNoetherianSpace X := by
  intro x
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let f := X.affineCover.f i
  let _ := IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange f⟩
  refine ⟨_, f.opensRange.2, ⟨y, rfl⟩, ?_⟩
  convert! noetherianSpace_of_isAffineOpen f.opensRange (isAffineOpen_opensRange f)

/-- A quasi-compact open of a locally Noetherian scheme has finitely many irreducible
components: as a scheme it is locally Noetherian and compact, hence a Noetherian space. -/
@[ega "0 2.2.5" "special case", ega "I 7.3.3" "special case", ega "IV 2.3.6" "special case"]
theorem finite_irreducibleComponents_of_isCompact (X : Scheme.{u}) [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : (irreducibleComponents U).Finite := by
  have : CompactSpace (U : Type u) := isCompact_iff_compactSpace.mp hU
  have : IsNoetherian (U : Scheme.{u}) := ⟨⟩
  exact finite_irreducibleComponents_of_isNoetherian (X := (U : Scheme.{u}))

end AlgebraicGeometry

end
