module

public import Mathlib.Topology.Constructible
public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.Topology.Constructible.InConstructible
public import StacksFrontier.Topology.Constructible.IrreducibleMeet
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible sets in a Noetherian space

In a Noetherian topological space every subset is retrocompact, so the retrocompactness conditions
in the definition of a constructible set are vacuous and being constructible reduces to being a
finite union of locally closed subsets.

## Main results

* `constructible_iff_finite_union_locally_closed` (Stacks 005L): in a Noetherian space
  `IsConstructibleSet` and `IsFiniteUnionLocallyClosed` agree.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- **Stacks 005L.** In a Noetherian topological space `X`, a subset `E ⊆ X` is constructible if
and only if it is a finite union of locally closed subsets of `X`. -/
@[stacks 005L,
  ega "0 9.1.7",
  ega "0 9.2.1" "first assertion",
  ega "IV 1.8.1" "special case",
  ega "IV 10.1.1" "global comparison"]
theorem constructible_iff_finite_union_locally_closed
    [TopologicalSpace.NoetherianSpace X] (E : Set X) :
    IsConstructibleSet E ↔ IsFiniteUnionLocallyClosed E := by
  refine ⟨fun ⟨n, U, V, hU, _, hV, _, hE⟩ => ⟨n, fun i => U i ∩ (V i)ᶜ,
      fun i => (hU i).isLocallyClosed.inter (hV i).isClosed_compl.isLocallyClosed, hE⟩,
    fun ⟨n, L, hL, hE⟩ => ?_⟩
  choose U Z hU hZ hLi using hL
  exact ⟨n, U, fun i => (Z i)ᶜ, hU, fun _ => noetherianSpace_isRetrocompact X _,
    fun i => (hZ i).isOpen_compl, fun _ => noetherianSpace_isRetrocompact X _,
    hE.trans <| Set.iUnion_congr fun i => by rw [hLi, compl_compl]⟩
