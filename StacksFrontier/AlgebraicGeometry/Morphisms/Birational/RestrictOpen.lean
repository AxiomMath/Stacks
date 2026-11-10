module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField

/-!
# Birational morphisms restricted to an open of the target

Birationality of a morphism of schemes is a condition on the generic points of the irreducible
components of its source and target, and both the set of such generic points and the local ring
at one of them are unchanged by passing to an open neighbourhood. Consequently a birational
morphism stays birational after restriction over any open of its target, and in particular the
normalization morphism of a reduced scheme is birational over every open.

## Main results

* `Topology.IsOpenEmbedding.mem_genericPoints_iff`: an open embedding both preserves and
  reflects membership in the set of generic points of irreducible components.
* `AlgebraicGeometry.Scheme.isBirational_normalization_morphismRestrict`: the normalization
  morphism of a reduced scheme is birational over every open.

Preservation of birationality under restriction over an open of the target is
`AlgebraicGeometry.IsBirational.morphismRestrict`.

## Implementation notes

The restriction of `f : X ⟶ Y` over an open `U : Y.Opens` is `f ∣_ U`, a morphism from the
open subscheme `f ⁻¹ᵁ U` of `X` to the open subscheme `U` of `Y`. Both ends are open
subschemes, so the generic-point statement is applied twice, once at each end.

Finiteness and surjectivity of the normalization morphism are
`AlgebraicGeometry.Scheme.isFinite_normalization` and
`AlgebraicGeometry.Scheme.surjective_normalization`; birationality holds without the Nagata or
dimension assumptions of [Stacks Project, Tag 0C1R] and over an arbitrary open.

## References

* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Topology.IsOpenEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An open embedding carries a generic point of an irreducible component to a generic point of
an irreducible component. -/
public theorem mem_genericPoints {i : X → Y} (hi : Topology.IsOpenEmbedding i) {x : X}
    (hx : x ∈ genericPoints X) : i x ∈ genericPoints Y := by
  obtain ⟨D, hD, hCD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({i x} : Set Y)) isIrreducible_singleton.closure
  have hmem : i x ∈ D := hCD (subset_closure (Set.mem_singleton _))
  have hpre : i ⁻¹' D ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hD hi ⟨i x, hmem, ⟨x, rfl⟩⟩
  have hCpre : closure ({x} : Set X) ⊆ i ⁻¹' D := by
    simpa [hi.closure_eq_preimage_closure_image, Set.image_singleton] using
      (Set.preimage_mono hCD (f := i))
  have hEq : closure ({x} : Set X) = i ⁻¹' D :=
    Set.Subset.antisymm hCpre (hx.2 hpre.1 hCpre)
  have hclosure : closure (i '' (i ⁻¹' D)) = D :=
    closure_image_preimage_of_isPreirreducible i hi.isOpenMap D ⟨x, hmem⟩ hD.1.2
      (isClosed_of_mem_irreducibleComponents D hD)
  have hC : closure ({i x} : Set Y) = D := by
    simpa [← hEq, closure_image_closure hi.continuous] using hclosure
  change closure ({i x} : Set Y) ∈ irreducibleComponents Y
  simpa only [hC] using hD

/-- A point whose image under an open embedding is a generic point of an irreducible component
is itself one. -/
public theorem mem_genericPoints_of_image {i : X → Y} (hi : Topology.IsOpenEmbedding i) {x : X}
    (hx : i x ∈ genericPoints Y) : x ∈ genericPoints X := by
  have hpre : i ⁻¹' closure {i x} ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hx hi
      ⟨i x, subset_closure (Set.mem_singleton _), ⟨x, rfl⟩⟩
  change closure ({x} : Set X) ∈ irreducibleComponents X
  rw [hi.closure_eq_preimage_closure_image]
  simpa using hpre

/-- An open embedding both preserves and reflects membership in the set of generic points of
irreducible components. -/
public theorem mem_genericPoints_iff {i : X → Y} (hi : Topology.IsOpenEmbedding i) {x : X} :
    i x ∈ genericPoints Y ↔ x ∈ genericPoints X :=
  ⟨hi.mem_genericPoints_of_image, hi.mem_genericPoints⟩

end Topology.IsOpenEmbedding

namespace AlgebraicGeometry

namespace Scheme

/-- **Stacks Project, Tag 0C1R.** Over every open of a reduced scheme, the normalization
morphism is birational. -/
@[stacks 0C1R "finite_normalization"]
public theorem isBirational_normalization_morphismRestrict (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (V : X.Opens) : IsBirational (X.normalization hX ∣_ V) :=
  (X.isBirational_normalization hX).morphismRestrict V

end Scheme

end AlgebraicGeometry

add_to_stacks 0C1R "finite_normalization" AlgebraicGeometry.Scheme.isFinite_normalization
add_to_stacks 0C1R "finite_normalization" AlgebraicGeometry.Scheme.surjective_normalization
