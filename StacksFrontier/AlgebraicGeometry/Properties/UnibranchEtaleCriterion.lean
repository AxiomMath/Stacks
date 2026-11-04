module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Branches

/-!
# Unibranchness tested on étale neighbourhoods

A scheme is unibranch at a point exactly when every elementary étale neighbourhood of that point
has a single irreducible component through its distinguished point, and geometrically unibranch
at the point exactly when every étale neighbourhood does.

## Main results

* `AlgebraicGeometry.isUnibranchAt_iff_existsUnique_irreducibleComponent` is the elementary
  criterion.
* `AlgebraicGeometry.isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent` is the
  criterion for every étale neighbourhood.

## Implementation notes

Both statements follow from the two supremum formulas for the number of branches and the number
of geometric branches, together with the characterisation of branch number one. The supremum is
attained at the value one exactly when every term is one, because every term is at least one:
the irreducible component of the distinguished point always passes through it, and
`AlgebraicGeometry.EtaleNeighborhood.self` is an elementary étale neighbourhood, so neither
index set is empty.

"Exactly one irreducible component through the distinguished point" is written as unique
existence in the subtype `irreducibleComponents`, rather than as a cardinality of a separated-out
set of subsets.

## References

* [Stacks Project, Tag 0CB4](https://stacks.math.columbia.edu/tag/0CB4)
-/

public section

namespace AlgebraicGeometry

universe u

/-- A point lies on exactly one irreducible component precisely when the set of irreducible
components through it is a singleton. -/
lemma encard_irreducibleComponentsThrough_eq_one_iff {T : Type*} [TopologicalSpace T]
    (y : T) :
    Set.encard {Z ∈ irreducibleComponents T | y ∈ Z} = 1 ↔
      ∃! Z : irreducibleComponents T, y ∈ (Z : Set T) := by
  rw [Set.encard_eq_one]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨⟨hC₁, hC₂⟩, huniq⟩ := Set.eq_singleton_iff_unique_mem.mp hC
    exact ⟨⟨C, hC₁⟩, hC₂, fun Z hZ => Subtype.ext (huniq _ ⟨Z.2, hZ⟩)⟩
  · rintro ⟨C, hC, huniq⟩
    exact ⟨C, Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨C.2, hC⟩, fun Z hZ => congrArg Subtype.val (huniq ⟨Z, hZ.1⟩ hZ.2)⟩⟩

/-- At least one irreducible component passes through every point. -/
lemma one_le_encard_irreducibleComponentsThrough {T : Type*} [TopologicalSpace T]
    (y : T) : 1 ≤ Set.encard {Z ∈ irreducibleComponents T | y ∈ Z} :=
  Set.one_le_encard_iff_nonempty.mpr
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y,
      mem_irreducibleComponent⟩

/-- **Stacks Project, Tag 0CB4.** A scheme is unibranch at a point if and only if every
elementary étale neighbourhood of that point has exactly one irreducible component passing
through its distinguished point. -/
@[stacks 0CB4 "unibranch_iff"]
theorem isUnibranchAt_iff_existsUnique_irreducibleComponent (X : Scheme.{u}) (x : X) :
    IsUnibranchAt X x ↔
      ∀ U : EtaleNeighborhood X x, U.IsElementary →
        ∃! Z : irreducibleComponents U.scheme, U.point ∈ (Z : Set U.scheme) := by
  rw [← numberOfBranches_eq_one_iff, numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
  simp_rw [← encard_irreducibleComponentsThrough_eq_one_iff]
  refine ⟨fun h U hU => le_antisymm ?_ (one_le_encard_irreducibleComponentsThrough _),
    fun h => le_antisymm (iSup₂_le fun U hU => (h U hU).le) ?_⟩
  · rw [← h]
    exact le_iSup_of_le U (le_iSup_of_le hU le_rfl)
  · exact le_iSup₂_of_le (EtaleNeighborhood.self X x) (EtaleNeighborhood.isElementary_self X x)
      (h _ (EtaleNeighborhood.isElementary_self X x)).ge

/-- **Stacks Project, Tag 0CB4.** A scheme is geometrically unibranch at a point if and only if
every étale neighbourhood of that point has exactly one irreducible component passing through its
distinguished point. -/
@[stacks 0CB4 "geometrically_unibranch_iff",
  ega "IV 7.9.10" "more general",
  sga "3 X 5.14.0" "partial"]
theorem isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent
    (X : Scheme.{u}) (x : X) :
    IsGeometricallyUnibranchAt X x ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z : irreducibleComponents U.scheme, U.point ∈ (Z : Set U.scheme) := by
  have : Nonempty (EtaleNeighborhood X x) := ⟨EtaleNeighborhood.self X x⟩
  rw [← numberOfGeometricBranches_eq_one_iff, numberOfGeometricBranches_eq_iSup_encard]
  simp_rw [← encard_irreducibleComponentsThrough_eq_one_iff]
  refine ⟨fun h U => le_antisymm ?_ (one_le_encard_irreducibleComponentsThrough _), fun h => ?_⟩
  · rw [← h]
    exact le_iSup_of_le U le_rfl
  · rw [iSup_congr h, iSup_const]

end AlgebraicGeometry

end
