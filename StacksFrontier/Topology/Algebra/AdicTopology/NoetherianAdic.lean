module

public import Mathlib.RingTheory.Noetherian.Defs
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings

/-!
# Noetherian adic topological rings

The class `WAdm^{Noeth}` of Situation 0ANI: topological rings whose topology is adic and whose
underlying ring is Noetherian. This is the class on which the conditions of Stacks 0GCD are
tested, and the class for which flatness is a local property by Stacks 0GC9.

## Main definitions

* `TopologicalRing.IsNoetherianAdic`: the topology is adic and the ring is Noetherian.
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- A topological ring is *Noetherian adic* when its topology is adic and its underlying ring is
Noetherian. This is the class `WAdm^{Noeth}` of Situation 0ANI. -/
abbrev IsNoetherianAdic (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : Prop :=
  IsAdic R ∧ IsNoetherianRing R

end TopologicalRing

end
