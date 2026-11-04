module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Normalization of a scheme locally of finite type over a field

A scheme locally of finite type over a field is locally Noetherian, and therefore every
quasi-compact open of it has only finitely many irreducible components. That finiteness is
exactly the hypothesis needed to form the normalization, so the normalization of a locally
algebraic scheme is defined without further assumptions.

## Main definitions

* `AlgebraicGeometry.normalizationSchemeOverField` is the normalization of a scheme locally of
  finite type over a field.
* `AlgebraicGeometry.normalizationOverField` is its normalization morphism.

## Main results

* `AlgebraicGeometry.finite_irreducibleComponents_of_locallyOfFiniteType` proves the finiteness
  condition needed to form the normalization.
* `AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization` gives integrality of the
  normalization morphism. The locally Noetherian dimension-one case, Tag 0C45 in full, is
  `AlgebraicGeometry.normalization_of_isLocallyNoetherian_dimension_one`.

## Implementation notes

A locally algebraic scheme over `k` is represented by a structure morphism to `Spec k` that is
locally of finite type. Its local Noetherianity is the existing theorem
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`. The finiteness result supplies the
hypothesis of `AlgebraicGeometry.Scheme.normalizationScheme` and
`AlgebraicGeometry.Scheme.normalization`; the abbreviations specialize those canonical
constructions without asking users to choose that proof.

## References

* [Stacks Project, Section 33.27 (Normalization)](https://stacks.math.columbia.edu/tag/0BXQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Every quasi-compact open of a scheme locally of finite type over a field has finitely many
irreducible components. -/
@[ega "IV 4.4.1" "partial"]
public theorem finite_irreducibleComponents_of_locallyOfFiniteType
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  intro U hU
  have : CompactSpace U := (isCompact_iff_compactSpace).mp (by simpa using hU)
  have : IsNoetherian U := IsNoetherian.mk
  exact finite_irreducibleComponents_of_isNoetherian (X := U)

/-- The normalization scheme of a scheme locally of finite type over a field. -/
public noncomputable abbrev normalizationSchemeOverField
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : Scheme.{u} :=
  X.normalizationScheme (finite_irreducibleComponents_of_locallyOfFiniteType k p)

/-- The normalization morphism of a scheme locally of finite type over a field. -/
public noncomputable abbrev normalizationOverField
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] : normalizationSchemeOverField k p ⟶ X :=
  X.normalization (finite_irreducibleComponents_of_locallyOfFiniteType k p)

end AlgebraicGeometry
