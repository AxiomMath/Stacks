module

public import StacksFrontier.Topology.Irreducible.DisjointComponentLocus

/-!
# Irreducible open pieces inside the members of a locally closed cover

Let `X` be a quasi-sober space with finitely many irreducible components, and let `X` be covered
by a family of locally closed subsets `L t`. Then there are pairwise disjoint irreducible opens
`W Z`, one for each irreducible component `Z`, whose union is dense and each of which lies inside
one member of the cover.

This is the topological step of the stratification argument in the proof of Theorem 03SC: a
constructible sheaf is finite locally constant on each stratum of a finite partition by locally
closed subsets, and the opens produced here are where it is finite locally constant *and* the
scheme is a disjoint union of irreducible, hence connected, pieces.

## Main results

* `Stacks.Topology.Irreducible.exists_isIrreducible_opens_of_isLocallyClosed_cover`.

## Implementation notes

The piece attached to `Z` is `U ∩ componentPart Z`, where `componentPart Z` is the part of `Z`
off the other components (`Stacks.Topology.Irreducible.componentPart`) and `U` is an open with
`L t = U ∩ C`, `C` closed, for the member `L t` containing the generic point of `Z`; since `C`
contains that generic point it contains `Z`, so the piece lies in `L t`.
-/

@[expose] public section

open Set Function

namespace Stacks.Topology.Irreducible

variable {X : Type*} [TopologicalSpace X]

/-- **Irreducible open pieces inside a locally closed cover.** In a quasi-sober space with
finitely many irreducible components, covered by locally closed subsets `L t`, there are
pairwise disjoint irreducible opens `W Z`, indexed by the irreducible components, with dense
union, each contained in some `L t`. -/
public theorem exists_isIrreducible_opens_of_isLocallyClosed_cover [QuasiSober X]
    [Finite (irreducibleComponents X)] {κ : Type*} (L : κ → Set X)
    (hL : ∀ t, IsLocallyClosed (L t)) (hcov : ⋃ t, L t = univ) :
    ∃ W : irreducibleComponents X → Set X, (∀ Z, IsOpen (W Z)) ∧ (∀ Z, IsIrreducible (W Z)) ∧
      Pairwise (Disjoint on W) ∧ Dense (⋃ Z, W Z) ∧ ∀ Z, ∃ t, W Z ⊆ L t := by
  classical
  let Zs : irreducibleComponents X → Set X := Subtype.val
  have hZcl : ∀ i, IsClosed (Zs i) := fun i ↦ isClosed_of_mem_irreducibleComponents _ i.2
  have hZcov : ⋃ i, Zs i = univ :=
    iUnion_eq_univ_of_forall_exists_eq fun W hW ↦ ⟨⟨W, hW⟩, rfl⟩
  let η : irreducibleComponents X → X := fun i ↦ (i.2.1).genericPoint
  have hη : ∀ i, IsGenericPoint (η i) (Zs i) := fun i ↦ by
    have := (i.2.1).isGenericPoint_genericPoint_closure
    rwa [(hZcl i).closure_eq] at this
  choose t ht using fun i ↦ iUnion_eq_univ_iff.1 hcov (η i)
  choose U C hU hC hUC using fun i ↦ hL (t i)
  have hO : ∀ i, IsOpen (U i ∩ componentPart Zs i) := fun i ↦
    (hU i).inter (isOpen_componentPart hZcl hZcov i)
  have hηW : ∀ i, η i ∈ U i ∩ componentPart Zs i := fun i ↦
    ⟨(hUC i ▸ ht i).1, genericPoint_mem_componentPart (fun i ↦ i.2) Subtype.val_injective hη i⟩
  refine ⟨fun i ↦ U i ∩ componentPart Zs i, hO, fun i ↦ ⟨⟨_, hηW i⟩, ?_⟩,
    fun i j hij ↦ (disjoint_componentPart hij).mono inter_subset_right inter_subset_right, ?_,
    fun i ↦ ⟨t i, ?_⟩⟩
  · exact (i.2.1.2).open_subset (hO i) (inter_subset_right.trans (componentPart_subset Zs i))
  · intro x
    obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.1 hZcov x
    rw [← hη i] at hi
    exact closure_mono (singleton_subset_iff.2 (mem_iUnion.2 ⟨i, hηW i⟩)) hi
  · rintro x ⟨hxU, hxP⟩
    rw [hUC i]
    exact ⟨hxU, ((hη i).mem_closed_set_iff (hC i)).1 (hUC i ▸ ht i).2
      (componentPart_subset Zs i hxP)⟩

end Stacks.Topology.Irreducible
