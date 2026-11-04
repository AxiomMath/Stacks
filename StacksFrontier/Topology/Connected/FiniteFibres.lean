module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Topology.Connected.CardComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite fibres bound the number of connected components

Let `f : X → Y` be a continuous map of nonempty topological spaces with `Y` connected, `f` both
open and closed, and some fibre `f ⁻¹' {y}` finite. Then `X` has at most `#(f ⁻¹' {y})` connected
components, and every connected component of `X` is clopen and surjects onto `Y`.

The cardinality bound is Mathlib's
`IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton` together with
`IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace`; they are
repackaged here as a statement about `Nat.card` and `Set.ncard`.

## Main results

* `finite_fibre_connectedComponents` (Stacks 07VB): `X` has finitely many connected components and
  `Nat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).ncard`.
* `isClopen_connectedComponent_of_finite`: in a space with finitely many connected components each
  component is clopen.
* `connectedComponent_clopen_and_image_eq_univ`: each connected component of `X` is clopen and its
  image is all of `Y`.
-/

@[expose] public section

universe u

open Set

/-- **Stacks 07VB.** If `f : X → Y` is a continuous open and closed map between nonempty
topological spaces, `Y` is connected, and some fibre `f ⁻¹' {y}` is finite, then `X` has finitely
many connected components and their number is at most the cardinality of the fibre. -/
@[stacks 07VB]
theorem finite_fibre_connectedComponents
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y]
    (f : X → Y)
    (hY_conn : ConnectedSpace Y)
    (hf_open : IsOpenMap f) (hf_closed : IsClosedMap f)
    (y : Y) (hy_fin : (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) ∧
      Nat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).ncard := by
  have : Finite (ConnectedComponents X) :=
    hf_open.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
      hf_closed hy_fin
  refine ⟨inferInstance, ?_⟩
  have hbound : ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard :=
    hf_open.enatCard_connectedComponents_le_encard_preimage_singleton hf_closed y
  -- Translate the `ENat`-cardinality bound into one about `Nat.card` and `Set.ncard`.
  rw [ENat.card_eq_coe_natCard, hy_fin.cast_ncard_eq.symm] at hbound
  exact_mod_cast hbound

/-- In a space with finitely many connected components, each connected component is clopen: the
complement of `connectedComponent x` is the union of the finitely many other components, each of
which is closed. -/
@[sga "3 VIA 2.3" "footnote (22)"]
lemma isClopen_connectedComponent_of_finite
    {X : Type u} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    (x : X) : IsClopen (connectedComponent x) := by
  refine ⟨isClosed_connectedComponent, ?_⟩
  rw [← isClosed_compl_iff]
  have hcompl :
      (connectedComponent x)ᶜ =
        ⋃ (c : ConnectedComponents X) (_ : c ≠ ConnectedComponents.mk x),
          ((↑) : X → ConnectedComponents X) ⁻¹' {c} := by
    ext z
    simp only [mem_compl_iff, mem_iUnion, mem_preimage, mem_singleton_iff, exists_prop,
      ← ConnectedComponents.coe_eq_coe']
    exact ⟨fun hz => ⟨_, fun h => hz h, rfl⟩, by rintro ⟨c, hc, rfl⟩ h; exact hc h⟩
  rw [hcompl]
  refine isClosed_iUnion_of_finite fun c => ?_
  by_cases hc : c = ConnectedComponents.mk x
  · subst hc; simp
  · simp only [hc, ne_eq, not_false_eq_true, iUnion_true]
    -- The preimage of `{c}` under the quotient map is a connected component, hence closed.
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent

/-- **Stacks 07VB**, corollary. Under the hypotheses of `finite_fibre_connectedComponents`, every
connected component `T` of `X` is open and closed in `X`, its image `f '' T` is a nonempty open and
closed subset of `Y`, and hence equals all of `Y`. -/
@[stacks 07VB "corollary", sga "3 X 9.7.3" "more general"]
theorem connectedComponent_clopen_and_image_eq_univ
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y]
    (f : X → Y)
    (hY_conn : ConnectedSpace Y)
    (hf_open : IsOpenMap f) (hf_closed : IsClosedMap f)
    (y : Y) (hy_fin : (f ⁻¹' {y}).Finite)
    (T : Set X) (hT : ∃ x : X, T = connectedComponent x) :
    IsOpen T ∧ IsClosed T ∧ (f '' T).Nonempty ∧ IsOpen (f '' T) ∧
      IsClosed (f '' T) ∧ f '' T = Set.univ := by
  have : Finite (ConnectedComponents X) :=
    (finite_fibre_connectedComponents f hY_conn hf_open hf_closed y hy_fin).1
  obtain ⟨x, rfl⟩ := hT
  have hclopen : IsClopen (connectedComponent x) :=
    isClopen_connectedComponent_of_finite x
  have hne : (f '' connectedComponent x).Nonempty := ⟨f x, x, mem_connectedComponent, rfl⟩
  -- `f '' connectedComponent x` is a nonempty clopen of the connected space `Y`, hence all of `Y`.
  exact ⟨hclopen.isOpen, hclopen.isClosed, hne, hf_open _ hclopen.isOpen,
    hf_closed _ hclopen.isClosed,
    IsClopen.eq_univ ⟨hf_closed _ hclopen.isClosed, hf_open _ hclopen.isOpen⟩ hne⟩
