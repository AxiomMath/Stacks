module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of an algebraic cycle

The support of a cycle `∑ n_Z [Z]` is the union of the integral closed subschemes `Z` occurring
with a nonzero coefficient. A cycle is a locally finitely supported function on the points of
the scheme, the point `x` standing for the integral closed subscheme `closure {x}`, so this
union is the closure of the set of points carrying a nonzero coefficient, that is the
topological support `tsupport`.

## Main results

* `Stacks.Chow.tsupport_eq_biUnion_closure_singleton` identifies `tsupport` with the union of
  the integral closed subschemes occurring in the cycle.

## Implementation notes

The identification needs local finiteness: the closure of a union is the union of the closures
for a locally finite family, and the family of closures of the points of the support of a cycle
is locally finite by `Stacks.Chow.locallyFinite_closure_support`. Everything else about the
support of a cycle is Mathlib's existing `tsupport` API, in particular `isClosed_tsupport`; the
support depends neither on the base situation, nor on the dimension function, nor on the
dimension of the cycle, so no separate definition is introduced.

## References

* [Stacks Project, Tag 0H46](https://stacks.math.columbia.edu/tag/0H46)
-/

@[expose] public section

open Set Topology

namespace Stacks.Chow

universe u

variable {X : Type u} [TopologicalSpace X]

add_to_stacks 0H46 tsupport

/-- The support of a cycle is the union of the integral closed subschemes occurring in it with a
nonzero coefficient. The point `x` stands for the integral closed subscheme `closure {x}`, and
the family of these closures is locally finite, so their union is already closed and equals the
closure of the set of points with a nonzero coefficient. -/
@[ega "IV 21.6.1" "more general"]
theorem tsupport_eq_biUnion_closure_singleton {R : Type*} [Zero R] {c : X → R}
    (hc : LocallyFiniteSupport c) :
    tsupport c = ⋃ x ∈ Function.support c, closure {x} := by
  have hlf : LocallyFinite fun x : Function.support c ↦ ({(x : X)} : Set X) :=
    (locallyFinite_closure_support hc).subset fun _ ↦ subset_closure
  have hunion : Function.support c = ⋃ x : Function.support c, ({(x : X)} : Set X) := by
    ext y
    simp
  rw [show tsupport c = closure (Function.support c) from rfl]
  conv_lhs => rw [hunion]
  rw [hlf.closure_iUnion, Set.biUnion_eq_iUnion]

end Stacks.Chow
