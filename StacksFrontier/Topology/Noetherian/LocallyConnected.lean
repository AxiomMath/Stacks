module

public import StacksFrontier.Topology.Noetherian.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A locally Noetherian space is locally connected (Stacks 04MF)

Let `X` be a locally Noetherian topological space, meaning every point admits an open
neighbourhood that is Noetherian as a subspace (the predicate
`TopologicalSpace.IsLocallyNoetherianSpace`). Then `X` is locally connected.

The proof goes through two helper lemmas. A Noetherian space has only finitely many
connected components: each irreducible component is contained in a connected component, and
a Noetherian space has finitely many irreducible components. In a space with finitely many
connected components each connected component is clopen, since the complement of a component
is a finite union of components, hence closed. (Mathlib proves the clopenness of components
only for a locally connected space, which would be circular here.)

Combining these with `TopologicalSpace.NoetherianSpace.inter_of_left`: for any open
neighbourhood `U` of `x` and any open Noetherian neighbourhood `W` of `x`, the connected
component of `x` in `W ∩ U` is open, connected, contains `x`, and is contained in `U`. So the
connected open neighbourhoods of `x` form a basis of `𝓝 x`.
-/

@[expose] public section

open TopologicalSpace Topology

namespace TopologicalSpace

section helper_lemmas

variable {α : Type*} [TopologicalSpace α]

/-- A Noetherian topological space has finitely many connected components. -/
lemma NoetherianSpace.finite_connectedComponents
    (α : Type*) [TopologicalSpace α] [NoetherianSpace α] :
    Finite (ConnectedComponents α) := by
  have : Finite ↑(irreducibleComponents α) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  -- Map each irreducible component to the connected component of one of its points.
  refine Finite.of_surjective
      (fun I : ↑(irreducibleComponents α) => ConnectedComponents.mk I.property.1.nonempty.some)
      fun c => ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨I, hI, hxI⟩ : x ∈ ⋃₀ irreducibleComponents α := by
    rw [sUnion_irreducibleComponents]
    trivial
  refine ⟨⟨I, hI⟩, ?_⟩
  rw [ConnectedComponents.coe_eq_coe']
  exact hI.1.isConnected.subset_connectedComponent hxI hI.1.nonempty.some_mem

/-- The fibre of `ConnectedComponents.mk` over the class of `y` is `connectedComponent y`. -/
private theorem preimage_mk_singleton_eq_connectedComponent (y : α) :
    ConnectedComponents.mk ⁻¹' {(ConnectedComponents.mk y)} = connectedComponent y :=
  Set.ext fun _ => ConnectedComponents.coe_eq_coe'

/-- In a space with finitely many connected components, every component is clopen. -/
lemma isClopen_connectedComponent_of_finite_connectedComponents
    [Finite (ConnectedComponents α)] (x : α) : IsClopen (connectedComponent x) := by
  -- Each fibre of the quotient map equals a connected component, hence is closed.
  have hpre : ∀ c : ConnectedComponents α,
      IsClosed (ConnectedComponents.mk ⁻¹' ({c} : Set _)) := by
    intro c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [preimage_mk_singleton_eq_connectedComponent]
    exact isClosed_connectedComponent
  refine ⟨isClosed_connectedComponent, ?_⟩
  rw [← preimage_mk_singleton_eq_connectedComponent,
    ← isClosed_compl_iff, ← Set.preimage_compl,
    show ConnectedComponents.mk ⁻¹' ({ConnectedComponents.mk x}ᶜ : Set _) =
        ⋃ c ∈ ({ConnectedComponents.mk x}ᶜ : Set _),
          ConnectedComponents.mk ⁻¹' ({c} : Set _) from by
      ext _
      simp]
  exact (Set.toFinite _).isClosed_biUnion (fun c _ => hpre c)

/-- Given an open Noetherian subspace `W` containing `x` and any open neighbourhood `U` of
`x`, there is a connected open neighbourhood `V` of `x` with `V ⊆ U`. -/
@[ega "I 6.1.9" "partial"]
lemma exists_isConnected_isOpen_subset_of_noetherian
    (x : α) (U : Set α) (hU : IsOpen U) (hxU : x ∈ U)
    (W : Set α) (hW : IsOpen W) (hxW : x ∈ W) [NoetherianSpace W] :
    ∃ V : Set α, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V := by
  set WU : Set α := W ∩ U
  have hxWU : x ∈ WU := ⟨hxW, hxU⟩
  have : NoetherianSpace WU := NoetherianSpace.inter_of_left W U
  have : Finite (ConnectedComponents WU) := NoetherianSpace.finite_connectedComponents WU
  set x' : WU := ⟨x, hxWU⟩
  have hClopen : IsClopen (connectedComponent x') :=
    isClopen_connectedComponent_of_finite_connectedComponents x'
  refine ⟨Subtype.val '' connectedComponent x', ?_, hClopen.2.trans (hW.inter hU),
    ⟨x', mem_connectedComponent, rfl⟩,
    ⟨⟨x, x', mem_connectedComponent, rfl⟩,
      (isConnected_connectedComponent (x := x')).2.image _
        continuous_subtype_val.continuousOn⟩⟩
  rintro y ⟨⟨z, _, hzU⟩, _, rfl⟩
  exact hzU

end helper_lemmas

/-- **Stacks 04MF.** A locally Noetherian topological space is locally connected. -/
@[stacks 04MF, ega "I 6.1.9", sga "3 X 7.0" "local connectedness", sga "4 VI 2.18" "special case"]
theorem IsLocallyNoetherianSpace.locallyConnectedSpace
    (α : Type*) [TopologicalSpace α] (hα : IsLocallyNoetherianSpace α) :
    LocallyConnectedSpace α := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_iff]
  intro t
  refine ⟨fun ht => ?_, fun ⟨V, ⟨hV, hxV, _⟩, hVt⟩ =>
    Filter.mem_of_superset (hV.mem_nhds hxV) hVt⟩
  rw [mem_nhds_iff] at ht
  obtain ⟨U, hUt, hU, hxU⟩ := ht
  obtain ⟨W, hW, hxW, _⟩ := hα x
  obtain ⟨V, hVU, hVopen, hxV, hVconn⟩ :=
    exists_isConnected_isOpen_subset_of_noetherian x U hU hxU W hW hxW
  exact ⟨V, ⟨hVopen, hxV, hVconn⟩, hVU.trans hUt⟩

end TopologicalSpace
