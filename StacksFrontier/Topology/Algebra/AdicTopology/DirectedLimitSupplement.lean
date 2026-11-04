module

public import StacksFrontier.Topology.Algebra.AdicTopology.DirectedLimit
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Projections from a directed limit of rings

For an inverse system of commutative rings `R i` with transition maps `t`, the projections from
the limit are compatible with the transition maps.
These results are stated next to `StacksFrontier.Topology.Algebra.AdicTopology.DirectedLimit` but
kept in a module of their own, so that that module stays as it is on the base.

## Main results

* `TopologicalRing.DirectedLimit.proj_comp`: for `i ≤ j`, the projection to `R i` is the
  projection to `R j` followed by the transition map `t`.
-/

@[expose] public section

namespace TopologicalRing

open Filter

universe u

variable {I : Type u} [Preorder I] {R : I → Type u} [∀ i, CommRing (R i)]
  (t : ∀ ⦃i j : I⦄, i ≤ j → R j →+* R i)

namespace DirectedLimit

/-- The projection at the smaller index is the projection at the larger one followed by the
transition map. -/
theorem proj_comp {i j : I} (h : i ≤ j) : (t h).comp (proj t j) = proj t i :=
  RingHom.ext fun a ↦ t_proj t h a

variable [Nonempty I] [IsDirected I (· ≤ ·)]

end DirectedLimit

end TopologicalRing

end
