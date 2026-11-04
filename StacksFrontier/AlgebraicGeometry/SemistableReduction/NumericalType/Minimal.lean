module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contribution
public import Mathlib

/-!
# The genus of a minimal numerical type with several components

A minimal numerical type with more than one component has genus at least one:
every contribution is nonnegative, and some component is not a minus-two index.

## Main results

* `AlgebraicGeometry.NumericalType.one_le_genus_of_isMinimal`.

## References

* [Stacks Project, Tag 0C7B](https://stacks.math.columbia.edu/tag/0C7B)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- A minimal numerical type with more than one component has genus at least one. -/
@[stacks 0C7B]
public lemma one_le_genus_of_isMinimal (T : NumericalType) (hT : IsMinimal T)
    (hn : 1 < T.componentCount) :
    1 ≤ genus T := by
  exact_mod_cast (show (1 : ℚ) ≤ (genus T : ℚ) from by
    rw [cast_genus]
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin T.componentCount))) =>
      contribution_nonneg_of_isMinimal T hT hn i)
    linarith)

end AlgebraicGeometry.NumericalType
