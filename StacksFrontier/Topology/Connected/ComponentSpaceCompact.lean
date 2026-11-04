module

public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The space of connected components of a quasi-compact space is profinite

If every connected component of a quasi-compact space `X` is the intersection of the clopen subsets
containing it, then `ConnectedComponents X` is Hausdorff: given two distinct components,
compactness of one of them cuts the intersection of clopens defining the other down to a single
clopen `U` disjoint from it, and `U`, being a union of connected components, descends to a clopen
of `ConnectedComponents X`.

## Main results

* `IsProfiniteSpacePropForm`: compact, Hausdorff and totally disconnected.
* `connectedComponent_eq_iInter_isClopen_of_hyp`: under the hypothesis of the tag, a connected
  component is the intersection of the clopens *containing its base point*.
* `isProfiniteSpacePropForm_connectedComponents` (Stacks 0900): `ConnectedComponents X` is
  profinite.
-/

@[expose] public section

open Set Topology

/-- A topological space is profinite if it is compact (quasi-compact in the Stacks/Bourbaki sense,
without a separation axiom), Hausdorff and totally disconnected. -/
def IsProfiniteSpacePropForm (Y : Type*) [TopologicalSpace Y] : Prop :=
  CompactSpace Y ∧ T2Space Y ∧ TotallyDisconnectedSpace Y

/-- Under the hypothesis of Stacks 0900, the connected component of a point `x` is the intersection
of the clopen subsets of `X` *containing `x`*, not merely of those containing the whole component.
For clopen `U` the two formulations agree: if `x ∈ U` then `connectedComponent x ⊆ U`. -/
lemma connectedComponent_eq_iInter_isClopen_of_hyp
    {X : Type*} [TopologicalSpace X]
    (h_clopen_inter : ∀ x : X,
      connectedComponent x = ⋂₀ {U : Set X | IsClopen U ∧ connectedComponent x ⊆ U})
    (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X) := by
  apply Set.Subset.antisymm
  · -- A clopen set is a union of connected components, so one containing `x` contains the whole
    -- component of `x`.
    refine subset_iInter ?_
    rintro ⟨U, hU, hxU⟩
    exact hU.connectedComponent_subset hxU
  · -- Conversely, fix `y` in the intersection: every clopen `U` containing `connectedComponent x`
    -- also contains `x`, hence contains `y`.
    intro y hy
    rw [h_clopen_inter x]
    refine mem_sInter.mpr ?_
    rintro U ⟨hUclopen, hUsub⟩
    exact mem_iInter.mp hy ⟨U, hUclopen, hUsub mem_connectedComponent⟩

/-- **Stacks 0900.** Let `X` be a quasi-compact topological space such that every connected
component of `X` equals the intersection of the clopen subsets of `X` containing it. Then
`ConnectedComponents X`, with the quotient topology, is a profinite space: compact, Hausdorff and
totally disconnected. -/
@[stacks 0900]
theorem isProfiniteSpacePropForm_connectedComponents
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (h_clopen_inter : ∀ x : X,
      connectedComponent x = ⋂₀ {U : Set X | IsClopen U ∧ connectedComponent x ⊆ U}) :
    IsProfiniteSpacePropForm (ConnectedComponents X) := by
  refine ⟨inferInstance, ?_, inferInstance⟩
  -- It remains to show `T2Space (ConnectedComponents X)`.
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h_disj : Disjoint (connectedComponent a) (connectedComponent b) :=
    connectedComponent_disjoint ne
  -- Rewrite `connectedComponent b` as the intersection of the clopens containing `b`.
  have hb_eq :
      connectedComponent b = ⋂ s : { s : Set X // IsClopen s ∧ b ∈ s }, (s : Set X) :=
    connectedComponent_eq_iInter_isClopen_of_hyp h_clopen_inter b
  rw [hb_eq] at h_disj
  -- Compactness of the closed set `connectedComponent a` gives a finite subfamily of those clopens
  -- whose intersection is already disjoint from it; that intersection is a single clopen `U`.
  obtain ⟨U, V, hU, ha, hb, rfl⟩ :
      ∃ (U : Set X) (V : Set (ConnectedComponents X)),
        IsClopen U ∧ Disjoint (connectedComponent a) U
          ∧ connectedComponent b ⊆ U ∧ ((↑) : X → ConnectedComponents X) ⁻¹' V = U := by
    obtain ⟨fin_a, ha_eq⟩ :=
      (isClosed_connectedComponent (α := X)).isCompact.elim_finite_subfamily_closed
        (fun s : { s : Set X // IsClopen s ∧ b ∈ s } => (s : Set X))
        (fun ⟨_, hs, _⟩ => hs.isClosed) h_disj
    set U : Set X := ⋂ (i : { s // IsClopen s ∧ b ∈ s }) (_ : i ∈ fin_a), (i : Set X)
    have hU_clopen : IsClopen U := isClopen_biInter_finset fun ⟨_, hi, _⟩ _ => hi
    refine ⟨U, ((↑) : X → ConnectedComponents X) '' U, hU_clopen, ha_eq, ?_, ?_⟩
    · -- Each set in the finite intersection contains `b`, hence contains `connectedComponent b`.
      exact subset_iInter₂ fun ⟨_, hs, hbs⟩ _ => hs.connectedComponent_subset hbs
    · -- `U` is clopen, hence a union of connected components, so it is saturated.
      exact (connectedComponents_preimage_image U).symm ▸
        hU_clopen.biUnion_connectedComponent_eq
  -- `U = (↑) ⁻¹' V` is clopen, so `V` is clopen in `ConnectedComponents X`.
  rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
  refine ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hb mem_connectedComponent,
    disjoint_compl_left⟩
  -- `[a] ∉ V`: otherwise `a ∈ (↑) ⁻¹' V = U`, contradicting disjointness from
  -- `connectedComponent a`.
  intro hmemV
  exact Set.disjoint_left.mp ha mem_connectedComponent hmemV
