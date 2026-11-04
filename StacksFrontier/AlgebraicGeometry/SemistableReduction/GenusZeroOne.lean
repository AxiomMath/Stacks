module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Irreducible
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Minimal
public import Mathlib

/-!
# Minimal numerical types of genus zero

A minimal numerical type of genus zero has a single component, and up to
equality there is exactly one such numerical type: the one with `n = 1`,
`m₁ = 1`, `a₁₁ = 0`, `w₁ = 1` and `g₁ = 0`.

## Main results

* `AlgebraicGeometry.NumericalType.componentCount_eq_one_of_isMinimal_of_genus_eq_zero`.
* `AlgebraicGeometry.NumericalType.existsUnique_minimal_genus_zero`.
* `AlgebraicGeometry.NumericalType.data_of_isMinimal_of_genus_eq_zero`.

## References

* [Stacks Project, Tag 0C8S](https://stacks.math.columbia.edu/tag/0C8S)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The one-component numerical type of genus zero: one component of
multiplicity one, weight one and component genus zero. -/
private abbrev genusZeroNumericalType : NumericalType :=
  singletonNumericalType 1 1 0 one_pos one_pos le_rfl

private lemma genus_genusZeroNumericalType :
    genus genusZeroNumericalType = 0 := by
  simpa using singletonNumericalType_genus 1 1 0 one_pos one_pos le_rfl

private lemma minimal_genusZeroNumericalType :
    IsMinimal genusZeroNumericalType := by
  rintro ⟨i, ⟨_, hdiag⟩⟩
  simp [genusZeroNumericalType, singletonNumericalType] at hdiag

/-- A minimal numerical type of genus zero has exactly one component. -/
@[stacks 0C8S "component count"]
public lemma componentCount_eq_one_of_isMinimal_of_genus_eq_zero
    (T : NumericalType) (hminimal : IsMinimal T) (hgenus : genus T = 0) :
    T.componentCount = 1 := by
  by_contra hne
  have hn : 1 < T.componentCount := by have := T.componentCount_pos; omega
  have := one_le_genus_of_isMinimal T hminimal hn
  rw [hgenus] at this
  omega

/-- There is exactly one minimal numerical type of genus zero. -/
@[stacks 0C8S "existence and uniqueness"]
public lemma existsUnique_minimal_genus_zero :
    ∃! T : NumericalType, IsMinimal T ∧ genus T = 0 := by
  refine ⟨genusZeroNumericalType, ⟨minimal_genusZeroNumericalType,
    genus_genusZeroNumericalType⟩, ?_⟩
  intro T hT
  have hcount := componentCount_eq_one_of_isMinimal_of_genus_eq_zero T hT.1 hT.2
  let hT' : IrreducibleTypes 0 := ⟨T, hcount, hT.2⟩
  exact ext_of_componentCount_eq_one T genusZeroNumericalType hcount rfl
    (multiplicity_eq_one_of_genus_zero hT') (weight_eq_one_of_genus_zero hT')
    (componentGenus_eq_zero_of_genus_zero hT')

/-- The minimal numerical type of genus zero, explicitly: a minimal numerical
type of genus zero has a single component, of multiplicity one, self-intersection
number zero, weight one and component genus zero. Together with
`AlgebraicGeometry.NumericalType.existsUnique_minimal_genus_zero` this identifies
the only minimal numerical type of genus zero as `n = 1`, `m₁ = 1`, `a₁₁ = 0`,
`w₁ = 1`, `g₁ = 0`. -/
@[stacks 0C8S "explicit numerical type"]
public lemma data_of_isMinimal_of_genus_eq_zero
    (T : NumericalType) (hminimal : IsMinimal T) (hgenus : genus T = 0) :
    T.componentCount = 1 ∧ (∀ i, T.multiplicity i = 1) ∧
      (∀ i j, T.intersection i j = 0) ∧ (∀ i, T.weight i = 1) ∧
      (∀ i, T.componentGenus i = 0) := by
  have hcount := componentCount_eq_one_of_isMinimal_of_genus_eq_zero T hminimal hgenus
  have hzero (i : Fin T.componentCount) : i = ⟨0, T.componentCount_pos⟩ :=
    Fin.ext (by have := i.isLt; omega)
  let hT : IrreducibleTypes 0 := ⟨T, hcount, hgenus⟩
  refine ⟨hcount, fun i => ?_, fun i j => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hzero i]
    exact multiplicity_eq_one_of_genus_zero hT
  · rw [hzero i, hzero j]
    exact intersection_self_eq_zero_of_componentCount_eq_one T hcount
  · rw [hzero i]
    exact weight_eq_one_of_genus_zero hT
  · rw [hzero i]
    exact componentGenus_eq_zero_of_genus_zero hT

end AlgebraicGeometry.NumericalType
