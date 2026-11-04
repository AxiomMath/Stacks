module

public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.MaximalPointDrop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The irreducible components of top dimension of a subset

Let `T` be a subset of a topological space `X` and let `C` be an irreducible component of the
subspace `T`, read in `X` as `Subtype.val '' C`. This file proves point-set facts about such
components, in particular about the components of `T` of the largest dimension `d = dim T`.

## Main results

* `eq_image_of_image_subset_of_mem_irreducibleComponents`: an irreducible subset of `T`
  containing a component of `T` is that component.
* `eq_image_of_isGenericPoint_mem_of_mem_irreducibleComponents`: a closed irreducible subset of
  `T` containing the generic point of a component of `T` is that component.
* `preimage_mem_irreducibleComponents_of_isGenericPoint_mem`: if a closed subset `S ⊆ T`
  contains the generic point of a component of `T`, that component is a component of `S`.
* `notMem_of_topologicalKrullDim_lt`: a closed set of dimension smaller than that of a component
  of `T` does not contain its generic point.
* `topologicalKrullDim_lt_of_forall_ne`: if `dim T = n` is finite, an irreducible closed subset
  of `T` which is none of the components of `T` of dimension `n` has dimension `< n`.
* `topologicalKrullDim_lt_of_isGenericPoint_notMem`: a closed subset of a component of `T` of
  finite dimension `n` which misses the generic point of the component has dimension `< n`.
-/

@[expose] public section

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X] {T : Set X}

/-- The image in `X` of an irreducible subset of `T` is irreducible. -/
private theorem isIrreducible_image_val {Y : Set T} (hY : IsIrreducible Y) :
    IsIrreducible (Subtype.val '' Y) :=
  hY.image _ continuous_subtype_val.continuousOn

/-- A closed set containing the generic point of a set contains that set. -/
private theorem subset_of_isGenericPoint_mem {A S : Set X} {ξ : X} (hξ : IsGenericPoint ξ A)
    (hScl : IsClosed S) (hξS : ξ ∈ S) : A ⊆ S :=
  hξ ▸ hScl.closure_subset_iff.2 (singleton_subset_iff.2 hξS)

/-- A nonempty closed proper subset of an irreducible set of finite dimension `n` has
dimension `< n`. -/
private theorem topologicalKrullDim_lt_of_ssubset {C S : Set X} (hC : IsIrreducible C)
    (hScl : IsClosed S) (hSC : S ⊆ C) (hne : S.Nonempty) (hnot : ¬ C ⊆ S) {n : ℕ}
    (hn : topologicalKrullDim C = n) : topologicalKrullDim S < n := by
  have hinter : C ∩ S = S := inter_eq_self_of_subset_right hSC
  obtain ⟨h1, hle⟩ := topologicalKrullDim_inter_le_pred_of_not_subset hC hScl hnot
    (by rwa [hinter]) hn.le
  rw [hinter] at hle
  exact hle.trans_lt (WithBot.coe_lt_coe.2 (ENat.coe_lt_coe.2 (by lia)))

/-- An irreducible subset of `T` containing a component of `T` is that component. -/
theorem eq_image_of_image_subset_of_mem_irreducibleComponents {C : Set T}
    (hC : C ∈ irreducibleComponents T) {W : Set X} (hW : IsIrreducible W) (hWT : W ⊆ T)
    (hCW : Subtype.val '' C ⊆ W) : W = Subtype.val '' C := by
  have hle : Subtype.val ⁻¹' W ⊆ C :=
    hC.2 (isIrreducible_preimage_subtypeVal hW hWT) (image_subset_iff.1 hCW)
  exact Subset.antisymm (fun w hw => ⟨⟨w, hWT hw⟩, hle hw, rfl⟩) hCW

/-- A closed irreducible subset of `T` containing the generic point of a component of `T` is that
component. -/
@[ega "0 2.1.6" "more general"]
theorem eq_image_of_isGenericPoint_mem_of_mem_irreducibleComponents {C : Set T}
    (hC : C ∈ irreducibleComponents T) {ξ : X} (hξ : IsGenericPoint ξ (Subtype.val '' C))
    {W : Set X} (hW : IsIrreducible W) (hWcl : IsClosed W) (hWT : W ⊆ T) (hξW : ξ ∈ W) :
    W = Subtype.val '' C :=
  eq_image_of_image_subset_of_mem_irreducibleComponents hC hW hWT
    (subset_of_isGenericPoint_mem hξ hWcl hξW)

/-- A component of `T` whose generic point lies in a closed subset `S ⊆ T` is a component of
`S`. -/
theorem preimage_mem_irreducibleComponents_of_isGenericPoint_mem {C : Set T}
    (hC : C ∈ irreducibleComponents T) {ξ : X} (hξ : IsGenericPoint ξ (Subtype.val '' C))
    {S : Set X} (hScl : IsClosed S) (hST : S ⊆ T) (hξS : ξ ∈ S) :
    (Subtype.val ⁻¹' (Subtype.val '' C) : Set S) ∈ irreducibleComponents S := by
  have hCS := subset_of_isGenericPoint_mem hξ hScl hξS
  refine ⟨isIrreducible_preimage_subtypeVal (isIrreducible_image_val hC.1) hCS,
    fun Y hY hle => ?_⟩
  have hYirr := isIrreducible_image_val hY
  have hYT : Subtype.val '' Y ⊆ T := fun _ ⟨y, _, hy⟩ => hy ▸ hST y.2
  have heq := eq_image_of_image_subset_of_mem_irreducibleComponents hC hYirr hYT
    fun x hx => ⟨⟨x, hCS hx⟩, hle hx, rfl⟩
  intro y hy
  show y.1 ∈ Subtype.val '' C
  rw [← heq]
  exact ⟨y, hy, rfl⟩

/-- A closed set of dimension smaller than that of a component of `T` misses the generic point of
the component. -/
theorem notMem_of_topologicalKrullDim_lt {C : Set T} {ξ : X}
    (hξ : IsGenericPoint ξ (Subtype.val '' C)) {S : Set X} (hScl : IsClosed S)
    (hdim : topologicalKrullDim S < topologicalKrullDim (Subtype.val '' C)) : ξ ∉ S := by
  intro hξS
  exact (topologicalKrullDim_le_of_subset (subset_of_isGenericPoint_mem hξ hScl hξS)).not_gt hdim

/-- The image in `X` of a subset of `T` has dimension at most `dim T`. -/
theorem topologicalKrullDim_image_le {C : Set T} :
    topologicalKrullDim (Subtype.val '' C) ≤ topologicalKrullDim T :=
  topologicalKrullDim_le_of_subset fun _ ⟨y, _, hy⟩ => hy ▸ y.2

/-- A closed subset of a component of `T` of finite dimension `n` which misses the generic point
of the component has dimension `< n`. -/
theorem topologicalKrullDim_lt_of_isGenericPoint_notMem {C : Set T}
    (hC : C ∈ irreducibleComponents T) {ξ : X} (hξ : IsGenericPoint ξ (Subtype.val '' C))
    {n : ℕ} (hn : topologicalKrullDim (Subtype.val '' C) = n) {S : Set X} (hScl : IsClosed S)
    (hSC : S ⊆ Subtype.val '' C) (hξS : ξ ∉ S) : topologicalKrullDim S < n := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 (isEmpty_coe_sort.2 rfl)]
    exact WithBot.bot_lt_coe _
  exact topologicalKrullDim_lt_of_ssubset (isIrreducible_image_val hC.1) hScl hSC hne
    (fun h => hξS (h hξ.mem)) hn

/-- If `dim T = n` is finite, an irreducible closed subset of `T` which is none of the components
of `T` of dimension `n` has dimension `< n`. -/
theorem topologicalKrullDim_lt_of_forall_ne {n : ℕ} (hT : topologicalKrullDim T = n)
    {W : Set X} (hW : IsIrreducible W) (hWcl : IsClosed W) (hWT : W ⊆ T)
    (hne : ∀ C ∈ irreducibleComponents T,
      topologicalKrullDim (Subtype.val '' C) = n → W ≠ Subtype.val '' C) :
    topologicalKrullDim W < n := by
  obtain ⟨C, hC, hWC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_preimage_subtypeVal hW hWT)
  have hWC' : W ⊆ Subtype.val '' C := fun w hw => ⟨⟨w, hWT hw⟩, hWC hw, rfl⟩
  have hCle : topologicalKrullDim (Subtype.val '' C) ≤ n := hT ▸ topologicalKrullDim_image_le
  rcases hCle.lt_or_eq with hlt | heq
  · exact (topologicalKrullDim_le_of_subset hWC').trans_lt hlt
  exact topologicalKrullDim_lt_of_ssubset (isIrreducible_image_val hC.1) hWcl hWC' hW.nonempty
    (fun h => hne C hC heq (Subset.antisymm hWC' h)) heq
