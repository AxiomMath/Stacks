module

public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Locally connected spaces in the sense of the Stacks Project (Stacks 04ME)

The Stacks Project (Tag 04MD) calls a topological space `X` locally connected if every point
has a fundamental system of connected neighbourhoods, which need not be open. Mathlib's class
`LocallyConnectedSpace` asks instead for a basis of *open* connected neighbourhoods.

This file states Stacks 04ME under the Stacks definition: if every point of `X` has a
fundamental system of connected neighbourhoods, then
1. every open subset of `X` again has this property,
2. the connected components of `X` are open,
3. the connected components of open subsets of `X` are open, and
4. every point has a fundamental system of open connected neighbourhoods.

The last clause is the substantial one: it is what identifies the Stacks notion with Mathlib's
`LocallyConnectedSpace`, recorded as `locallyConnectedSpace_iff_hasBasis_isConnected`.

## Main statements

* `locallyConnectedSpace_iff_hasBasis_isConnected`: the Stacks definition of local
  connectedness agrees with `LocallyConnectedSpace`.
* `hasBasis_isConnected_nhds_open_and_isOpen_connectedComponent`: Stacks 04ME.

## References

* [Stacks Project, Tag 04MD](https://stacks.math.columbia.edu/tag/04MD)
* [Stacks Project, Tag 04ME](https://stacks.math.columbia.edu/tag/04ME)
-/

@[expose] public section

open Topology Filter

variable {X : Type*} [TopologicalSpace X]

/-- A space is a `LocallyConnectedSpace` exactly when every point has a fundamental system of
connected (not necessarily open) neighbourhoods, which is the Stacks definition (Tag 04MD). -/
theorem locallyConnectedSpace_iff_hasBasis_isConnected :
    LocallyConnectedSpace X ↔
      ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsConnected s) id := by
  rw [locallyConnectedSpace_iff_connected_basis]
  refine forall_congr' fun x => ?_
  have key : ∀ s : Set X, (s ∈ 𝓝 x ∧ IsConnected s) ↔ (s ∈ 𝓝 x ∧ IsPreconnected s) :=
    fun s => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ⟨x, mem_of_mem_nhds h.1⟩, h.2⟩⟩
  simp_rw [key]

/-- **Stacks 04ME.** Let `X` be a topological space in which every point has a fundamental
system of connected neighbourhoods (locally connected in the sense of Stacks 04MD). Then
(1) every open subset `U` of `X` has the same property, (2) the connected components of `X` are
open, (3) the connected components of an open subset `U` are open (as subsets of `X`), and
(4) every point has a fundamental system of open connected neighbourhoods. -/
@[stacks 04ME "The complete lemma under the Stacks definition 04MD of local connectedness
(a fundamental system of connected, not necessarily open, neighbourhoods): open subsets are
locally connected, connected components of the space and of its open subsets are open, and
every point has a fundamental system of open connected neighbourhoods."]
theorem hasBasis_isConnected_nhds_open_and_isOpen_connectedComponent
    (h : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsConnected s) id) :
    (∀ U : Set X, IsOpen U →
        ∀ x : U, (𝓝 x).HasBasis (fun s : Set U => s ∈ 𝓝 x ∧ IsConnected s) id) ∧
      (∀ x : X, IsOpen (connectedComponent x)) ∧
      (∀ U : Set X, IsOpen U → ∀ x : U, IsOpen (Subtype.val '' connectedComponent x)) ∧
      ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => IsOpen s ∧ x ∈ s ∧ IsConnected s) id := by
  have : LocallyConnectedSpace X := locallyConnectedSpace_iff_hasBasis_isConnected.2 h
  refine ⟨fun U hU => ?_, fun _ => isOpen_connectedComponent, fun U hU x => ?_,
    LocallyConnectedSpace.open_connected_basis⟩
  · have := hU.locallyConnectedSpace
    exact locallyConnectedSpace_iff_hasBasis_isConnected.1 this
  · have := hU.locallyConnectedSpace
    exact hU.isOpenMap_subtype_val _ isOpen_connectedComponent
