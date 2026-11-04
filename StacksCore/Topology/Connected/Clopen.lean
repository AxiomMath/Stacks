module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Sets.Closeds

/-! # Connectedness and the Boolean algebra of clopen sets

`preconnectedSpace_iff_clopen` restated for the bundled type `TopologicalSpace.Clopens`, together
with the resulting characterisation of `ConnectedSpace` as simplicity of that Boolean algebra.

Note the one-character distance from Mathlib's `preconnectedSpace_iff_clopen`: the plural names
here are about the bundled lattice `Clopens α`, the singular one about the predicate `IsClopen`.
-/

@[expose] public section

open TopologicalSpace

lemma preconnectedSpace_iff_clopens {α : Type*} [TopologicalSpace α] :
    PreconnectedSpace α ↔ ∀ x : Clopens α, x = ⊥ ∨ x = ⊤ := by
  simpa [preconnectedSpace_iff_clopen, Clopens.ext_iff] using
    ⟨fun hs ⟨x, hx⟩ ↦ hs x hx, fun h s hs ↦ h ⟨s, hs⟩⟩

lemma preconnectedSpace_iff_clopens' {α : Type*} [TopologicalSpace α] :
    PreconnectedSpace α ↔ Set.univ (α := Clopens α) = {⊥, ⊤} := by
  simp [preconnectedSpace_iff_clopens, Set.ext_iff]

lemma Clopens.nontrivial_iff {α : Type*} [TopologicalSpace α] :
    Nontrivial (Clopens α) ↔ Nonempty α :=
  ⟨fun _ ↦ by simpa [-top_ne_bot, Clopens.ext_iff] using top_ne_bot (α := Clopens α), fun _ ↦
    ⟨⊤, ⊥, by simp [Clopens.ext_iff]⟩⟩

theorem connectedSpace_iff_isSimpleOrder_clopens {α : Type*} [TopologicalSpace α] :
    ConnectedSpace α ↔ IsSimpleOrder (Clopens α) := by
  simp [connectedSpace_iff, preconnectedSpace_iff_clopens, isSimpleOrder_iff, and_comm,
    Clopens.nontrivial_iff]
