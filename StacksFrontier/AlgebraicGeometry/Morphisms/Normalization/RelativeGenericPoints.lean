module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints

/-!
# Generic points of a relative normalization

For a quasi-compact and quasi-separated morphism of schemes, every generic point of an
irreducible component of the relative normalization comes from a generic point of an irreducible
component of the source.

## Main results

* `AlgebraicGeometry.exists_genericPoint_irreducibleComponent_mapping_to` lifts a generic point
  of an irreducible component through the canonical map to the relative normalization.

## Implementation notes

The irreducible components are represented as members of `irreducibleComponents`, and being
their generic points is expressed by `IsGenericPoint`. The equality in the conclusion records
the canonical map `AlgebraicGeometry.Scheme.Hom.toNormalization` rather than merely membership
in its range.

## References

* [Stacks Project, Tag 0AXP](https://stacks.math.columbia.edu/tag/0AXP)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Every generic point of an irreducible component of the relative normalization of the target
in the source is the image of a generic point of an irreducible component of the source. -/
@[stacks 0AXP]
public theorem exists_genericPoint_irreducibleComponent_mapping_to
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    {x : f.normalization} {Z : Set f.normalization}
    (hZ : Z ∈ irreducibleComponents f.normalization) (hx : IsGenericPoint x Z) :
    ∃ (y : Y) (T : Set Y),
      T ∈ irreducibleComponents Y ∧ IsGenericPoint y T ∧ f.toNormalization y = x := by
  have hx' : x ∈ genericPoints f.normalization :=
    show closure ({x} : Set f.normalization) ∈ irreducibleComponents f.normalization from
      hx.symm ▸ hZ
  obtain ⟨y, hy⟩ :=
    (isDominant_iff_genericPoints_subset_range f.toNormalization).mp inferInstance hx'
  let T : irreducibleComponents Y :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  let y' : Y := (genericPoints.ofComponent T : genericPoints Y)
  have hy'T : IsGenericPoint y' T := genericPoints.isGenericPoint_ofComponent T
  have hsub : Z ⊆ closure ({f.toNormalization y'} : Set f.normalization) :=
    (hx.mem_closed_set_iff isClosed_closure).mp <| hy ▸
      (f.toNormalization.base.hom.map_specializes
        (hy'T.specializes mem_irreducibleComponent)).mem_closure
  have heq : closure ({f.toNormalization y'} : Set f.normalization) = Z :=
    (hZ.2 isIrreducible_singleton.closure hsub).antisymm hsub
  exact ⟨y', T, T.2, hy'T, (show IsGenericPoint (f.toNormalization y') Z from heq).eq hx⟩

end AlgebraicGeometry
