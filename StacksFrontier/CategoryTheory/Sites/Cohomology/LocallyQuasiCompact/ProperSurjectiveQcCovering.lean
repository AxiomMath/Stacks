module

public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-
# Problem Description

Stacks Tag 09X5 (Lemma 21.31.4), in the section "Cohomology on Hausdorff and
locally quasi-compact spaces" (Tag 09WY).

Throughout, "quasi-compact" means *compact* in the sense that every open cover
admits a finite subcover (no separation axiom is built in), matching Mathlib's
`IsCompact`. A "neighbourhood of a point `x`" is any set containing an open set
containing `x` (Mathlib's `∈ nhds x`).

The category `LC` has as objects topological spaces that are simultaneously
Hausdorff (T2) and locally quasi-compact (every point has a quasi-compact
neighbourhood), and continuous maps as morphisms. In Mathlib terms an object of
`LC` is a topological space `X` with instances `[T2Space X]` and
`[LocallyCompactSpace X]`.

## qc covering (Stacks Tag 09X0 / Definition 21.31.2)

Specialized to a one-element family `{f : X → Y}` (Definition 3): the family is
a *qc covering* if for every `y ∈ Y` there exist finitely many quasi-compact
subsets `E₁, …, Eₙ ⊆ X` such that `⋃ⱼ f(Eⱼ)` is a neighbourhood of `y`.

Equivalently (since a finite union of compact sets is compact): for every
`y ∈ Y` there exists a quasi-compact `E ⊆ X` such that `f(E)` is a
neighbourhood of `y`.

## Main Statement (Stacks Tag 09X5 / Lemma 21.31.4)

Let `X` and `Y` be objects of `LC` and let `f : X → Y` be a morphism of `LC`
(a continuous map). If `f` is proper and surjective, then `{f : X → Y}` is a
qc covering.

## Notes

- Properness (Stacks Tag 005R) is `IsProperMap` in Mathlib; key consequences
  used are `IsProperMap.isClosedMap` and that fibres of a proper map are
  compact.
- Local quasi-compactness and Hausdorffness of `Y` are part of the `LC`
  framework but are not strictly needed for this implication.
-/

open Set Topology

-- Main Definition(s)

/-- A single-morphism family `{f : X → Y}` is a *qc covering* if for every
`y : Y` there exist finitely many compact subsets `E₁, …, Eₙ ⊆ X` such that the
union of their images under `f` is a neighbourhood of `y`. This is Definition 3
(the single-morphism specialization of Stacks Tag 09X0). -/
def IsQuasiCompactCovering {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ y : Y, ∃ (n : ℕ) (E : Fin n → Set X), (∀ j, IsCompact (E j)) ∧
    (⋃ j, f '' (E j)) ∈ 𝓝 y

-- Main Statement(s)

/-- **Stacks Tag 09X5 / Lemma 21.31.4.** Let `X` and `Y` be Hausdorff and
locally quasi-compact topological spaces (objects of `LC`) and let `f : X → Y`
be continuous (a morphism of `LC`). If `f` is proper and surjective, then the
family `{f : X → Y}` is a qc covering. -/
@[stacks 09X5]
theorem proper_surjective_isQcCovering {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y]
    (f : X → Y) (hproper : IsProperMap f)
    (hsurj : Function.Surjective f) :
    IsQuasiCompactCovering f := by
  intro y
  obtain ⟨K, hKc, hKnhds⟩ := exists_compact_mem_nhds y
  refine ⟨1, fun _ => f ⁻¹' K, fun _ => hproper.isCompact_preimage hKc, ?_⟩
  rwa [iUnion_const, image_preimage_eq _ hsurj]

/-- Correctness characterization: since a finite union of compact sets is
compact, the qc covering condition (Definition 3) is equivalent to the
single-compact-set formulation (Definition 3, equivalent form): for every
`y : Y` there is a single compact `E ⊆ X` with `f '' E ∈ 𝓝 y`. -/
theorem isQcCovering_iff_single {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    IsQuasiCompactCovering f ↔
      ∀ y : Y, ∃ E : Set X, IsCompact E ∧ f '' E ∈ 𝓝 y := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · obtain ⟨n, E, hEc, hnhds⟩ := h y
    refine ⟨⋃ j, E j, isCompact_iUnion hEc, ?_⟩
    rwa [image_iUnion]
  · obtain ⟨E, hEc, hnhds⟩ := h y
    refine ⟨1, fun _ => E, fun _ => hEc, ?_⟩
    rwa [iUnion_const]
