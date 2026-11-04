module

public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Equidimensional topological spaces

A topological space is *equidimensional* if all of its irreducible components have the same
dimension, that is, any two irreducible components have equal `topologicalKrullDim` as subspaces.

## Main definitions

* `TopologicalSpace.Equidimensional`: all irreducible components have the same dimension.

## Main results

* `TopologicalSpace.Equidimensional.of_preirreducibleSpace`: a preirreducible space is
  equidimensional, having at most one irreducible component.
* `IsPreirreducible.equidimensional`: the same for a preirreducible subset, as a subspace.
* `TopologicalSpace.Equidimensional.of_homeomorph`: equidimensionality is a topological invariant.

## References

* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
-/

@[expose] public section

/-- A topological space `X` is *equidimensional* if every irreducible component of `X` has the same
dimension, i.e. the same topological Krull dimension as a subspace. -/
@[stacks 0058, ega "0 14.1.3"]
def TopologicalSpace.Equidimensional (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Z ∈ irreducibleComponents X, ∀ W ∈ irreducibleComponents X,
    topologicalKrullDim Z = topologicalKrullDim W

/-- A preirreducible space is equidimensional. -/
theorem TopologicalSpace.Equidimensional.of_preirreducibleSpace (X : Type*) [TopologicalSpace X]
    [PreirreducibleSpace X] : TopologicalSpace.Equidimensional X := by
  have key : ∀ Z ∈ irreducibleComponents X, Z = Set.univ := fun Z hZ ↦
    Set.univ_subset_iff.mp (hZ.2 ⟨⟨hZ.1.nonempty.some, Set.mem_univ _⟩,
      PreirreducibleSpace.isPreirreducible_univ⟩ (Set.subset_univ Z))
  intro Z hZ W hW
  rw [key Z hZ, key W hW]

/-- Equidimensionality transports along a homeomorphism. -/
theorem TopologicalSpace.Equidimensional.of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (hY : TopologicalSpace.Equidimensional Y) : TopologicalSpace.Equidimensional X := by
  have himage (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
      e '' Z ∈ irreducibleComponents Y :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
      (fun y => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective hZ
  intro Z hZ W hW
  rw [IsHomeomorph.topologicalKrullDim_eq _ (e.image Z).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (e.image W).isHomeomorph]
  exact hY _ (himage Z hZ) _ (himage W hW)

/-- A preirreducible subset of a topological space is equidimensional as a subspace. -/
theorem IsPreirreducible.equidimensional {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreirreducible s) : TopologicalSpace.Equidimensional s :=
  have := Subtype.preirreducibleSpace hs
  .of_preirreducibleSpace s
