module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shrinking a relatively open piece of a closed set to one with a generic point

On a Noetherian quasi-sober space, let `W` be open and `Z` closed with `W ∩ Z` nonempty. Then
there is an open set `V` for which the smaller piece `V ∩ W ∩ Z` of `W ∩ Z` is irreducible and has
a generic point: a point of it whose closure contains it.

The proof is the standard one. The closure of `W ∩ Z` is, the space being Noetherian, a finite
union of irreducible closed sets; pick a member `Y` maximal under inclusion, and let `V` be the
complement of the union of the others. Irreducibility of `Y` keeps it out of that union, so `V`
meets `closure (W ∩ Z)`, hence — `V` being open — meets `W ∩ Z` itself. Every point of
`V ∩ W ∩ Z` lies in `closure (W ∩ Z)` and outside every other member, hence in `Y`; so
`V ∩ W ∩ Z` is a nonempty part of `Y` cut out by the open set `V ∩ W`. Quasi-sobriety gives `Y` a
generic point `ξ`, which lies in every open set meeting `Y`, in particular in `V ∩ W`, and
`Y ⊆ Z`, so `ξ` lies in `V ∩ W ∩ Z`, whose closure is `closure {ξ} = Y`.

## Main results

* `Topology.isGenericPoint_closure_of_mem_of_subset_closure_singleton` and
  `Topology.isIrreducible_of_mem_of_subset_closure_singleton`: a point of a set whose closure
  contains that set is the generic point of its closure, and such a set is irreducible.
* `Topology.exists_isOpen_isIrreducible_genericPoint`: the statement above.

## Implementation notes

The conclusion is in the shape the Noetherian induction
`AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace` asks of its hypothesis
`hP`, for the property of a subset `T` given by `IsIrreducible T ∧ ∃ ξ ∈ T, T ⊆ closure {ξ}`: the
arguments are a closed set, its closedness, and the nonemptiness of its intersection with the
open set, and the conclusion produces an open `V` making `V ∩ W ∩ Z` nonempty with that property.
So the induction applied to this theorem partitions an open subset of a Noetherian sober space
into finitely many locally closed pieces, each irreducible with a generic point.

Quasi-sobriety is a genuine extra hypothesis: the cofinite topology on an infinite set is
Noetherian and irreducible yet has no generic point, and a generic point is exactly what
quasi-sobriety provides. It costs the intended consumer nothing, the underlying space of a scheme
being sober.

The generic point is produced as a point `ξ` of the ambient space together with the inclusion
`T ⊆ closure {ξ}`, rather than as a generic point of the subspace `T`. That is the form the
consumer uses, and `IsGenericPoint ξ T` would be the wrong statement: the closure of `ξ` is the
closure of `T`, which is strictly larger than `T` whenever `T` fails to be closed — as it does
here, `T` being a nonempty open part of the irreducible closed set it is dense in.
-/

@[expose] public section

open Set TopologicalSpace

namespace Topology

variable {α : Type*} [TopologicalSpace α]

section GenericPoint

variable {ξ : α} {T : Set α}

/-- A point of a set whose closure contains that set is the generic point of the closure of the
set. -/
theorem isGenericPoint_closure_of_mem_of_subset_closure_singleton (hξ : ξ ∈ T)
    (hT : T ⊆ closure {ξ}) : IsGenericPoint ξ (closure T) :=
  isGenericPoint_def.mpr <| Subset.antisymm (closure_mono (singleton_subset_iff.mpr hξ))
    (closure_minimal hT isClosed_closure)

/-- A set containing a point whose closure contains the set is irreducible: its closure is the
closure of a point, and a set is irreducible exactly when its closure is. -/
@[ega "0 2.1.2" "more general"]
theorem isIrreducible_of_mem_of_subset_closure_singleton (hξ : ξ ∈ T)
    (hT : T ⊆ closure {ξ}) : IsIrreducible T := by
  refine isIrreducible_iff_closure.mp ?_
  rw [← (isGenericPoint_closure_of_mem_of_subset_closure_singleton hξ hT).def]
  exact isIrreducible_singleton.closure

end GenericPoint

/-- **A relatively open piece of a closed set can be shrunk to an irreducible one with a generic
point.** On a Noetherian quasi-sober space, if an open set `W` meets a closed set `Z`, then some
open set `V` cuts `W ∩ Z` down to a nonempty piece `V ∩ W ∩ Z` which is irreducible and contains a
point whose closure contains it.

This is the input the Noetherian induction of
`AlgebraicGeometry.exists_locallyClosed_partition_of_noetherianSpace` asks for when the property
required of a piece is that it be irreducible with a generic point. -/
theorem exists_isOpen_isIrreducible_genericPoint [NoetherianSpace α] [QuasiSober α] {W : Set α}
    (hW : IsOpen W) (Z : Set α) (hZ : IsClosed Z) (hne : (W ∩ Z).Nonempty) :
    ∃ V : Set α, IsOpen V ∧ (V ∩ W ∩ Z).Nonempty ∧
      IsIrreducible (V ∩ W ∩ Z) ∧ ∃ ξ ∈ V ∩ W ∩ Z, V ∩ W ∩ Z ⊆ closure {ξ} := by
  classical
  -- Decompose `closure (W ∩ Z)` into finitely many irreducible closed pieces.
  have hcl : IsClosed (closure (W ∩ Z)) := isClosed_closure
  obtain ⟨F, hFfin, hFcl, hFirr, hFU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hcl
  have hclne : (closure (W ∩ Z)).Nonempty := hne.mono subset_closure
  have hFne : F.Nonempty := by
    rw [hFU] at hclne
    obtain ⟨t, htF, -⟩ := nonempty_sUnion.mp hclne
    exact ⟨t, htF⟩
  -- Choose a piece `Y` maximal under inclusion.
  obtain ⟨Y, hYF, hYmax⟩ := hFfin.exists_maximal hFne
  have hYirr : IsIrreducible Y := hFirr Y hYF
  have hYsub : Y ⊆ closure (W ∩ Z) := by rw [hFU]; exact subset_sUnion_of_mem hYF
  have hYZ : Y ⊆ Z := hYsub.trans (hZ.closure_subset_iff.mpr inter_subset_right)
  -- The union `D` of the other pieces is closed and does not swallow `Y`, because `Y` is
  -- irreducible and maximal.
  obtain ⟨D, hDcl, hDmem, hYD⟩ :
      ∃ D : Set α, IsClosed D ∧ (∀ t ∈ F, t ≠ Y → t ⊆ D) ∧ ¬Y ⊆ D := by
    have hdfin : (F \ {Y}).Finite := hFfin.sdiff
    refine ⟨⋃₀ (F \ {Y}), hdfin.isClosed_sUnion fun t ht => hFcl t ht.1,
      fun t htF htY => subset_sUnion_of_mem ⟨htF, htY⟩, fun hsub => ?_⟩
    have hsub' : Y ⊆ ⋃₀ (hdfin.toFinset : Set (Set α)) := by rwa [Finite.coe_toFinset]
    obtain ⟨t, htF, hYt⟩ := isIrreducible_iff_sUnion_isClosed.mp hYirr hdfin.toFinset
      (fun t ht => hFcl t (hdfin.mem_toFinset.mp ht).1) hsub'
    rw [hdfin.mem_toFinset] at htF
    exact htF.2 (Subset.antisymm hYt (hYmax htF.1 hYt)).symm
  -- `Dᶜ` is an open set meeting `closure (W ∩ Z)`, hence meeting `W ∩ Z`.
  have hTne : (Dᶜ ∩ W ∩ Z).Nonempty := by
    obtain ⟨y, hyY, hyD⟩ := not_subset.mp hYD
    have h1 : (Dᶜ ∩ closure (W ∩ Z)).Nonempty := ⟨y, hyD, hYsub hyY⟩
    obtain ⟨z, hzD, hzW, hzZ⟩ :=
      closure_nonempty_iff.mp (h1.mono hDcl.isOpen_compl.inter_closure)
    exact ⟨z, ⟨hzD, hzW⟩, hzZ⟩
  -- A point of `W ∩ Z` outside `D` lies in a piece, and that piece must be `Y`.
  have hTsub : Dᶜ ∩ W ∩ Z ⊆ Y := by
    intro x hx
    obtain ⟨t, htF, hxt⟩ := mem_sUnion.mp (by rw [← hFU]; exact subset_closure ⟨hx.1.2, hx.2⟩)
    by_cases htY : t = Y
    · exact htY ▸ hxt
    · exact (hx.1.1 (hDmem t htF htY hxt)).elim
  -- The generic point of `Y` lies in every open set meeting `Y`, in particular in `Dᶜ ∩ W`.
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hYirr (hFcl Y hYF)
  have hξmem : ξ ∈ Dᶜ ∩ W ∩ Z := by
    obtain ⟨z, hzDW, hzZ⟩ := hTne
    exact ⟨(hξ.mem_open_set_iff (hDcl.isOpen_compl.inter hW)).mpr
      ⟨z, hTsub ⟨hzDW, hzZ⟩, hzDW⟩, hYZ hξ.mem⟩
  have hTclos : Dᶜ ∩ W ∩ Z ⊆ closure {ξ} := by rw [hξ.def]; exact hTsub
  exact ⟨Dᶜ, hDcl.isOpen_compl, hTne,
    isIrreducible_of_mem_of_subset_closure_singleton hξmem hTclos, ξ, hξmem, hTclos⟩

end Topology

end
