module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField

/-!
# Normalization transports along an isomorphism

Let `K` be a field and let `A` and `B` be schemes locally of finite type over `K` with `A`
reduced. An isomorphism `A ≅ B` over `K` induces an isomorphism of their normalizations over
`K`, compatible with the two normalization morphisms and hence with the structure morphisms.

## Main results

* `AlgebraicGeometry.exists_iso_normalizationSchemeOverField_of_iso`: the isomorphism of
  normalizations induced by an isomorphism over the base field.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An isomorphism over the base field between a reduced scheme and another scheme, both locally
of finite type over the field, induces an isomorphism of their normalizations over the field,
compatible with the structure morphisms. -/
public theorem exists_iso_normalizationSchemeOverField_of_iso
    (K : Type u) [Field K] {A B : Scheme.{u}} (sA : A ⟶ Spec (.of K)) (sB : B ⟶ Spec (.of K))
    [IsReduced A] [LocallyOfFiniteType sA] [LocallyOfFiniteType sB]
    (τ : A ≅ B) (hτ : τ.hom ≫ sB = sA) :
    ∃ ε : normalizationSchemeOverField K sA ≅ normalizationSchemeOverField K sB,
      ε.hom ≫ normalizationOverField K sB ≫ sB = normalizationOverField K sA ≫ sA := by
  have : IsFinite (normalizationOverField K sA) := isFinite_normalizationOverField K sA
  have : IsNormal (normalizationSchemeOverField K sA) :=
    Scheme.isNormal_normalizationScheme A
      (finite_irreducibleComponents_of_locallyOfFiniteType K sA)
  obtain ⟨ε, hε⟩ := Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational
    (finite_irreducibleComponents_of_locallyOfFiniteType K sB)
    (normalizationOverField K sA ≫ τ.hom)
    (fun U hU ↦ finite_irreducibleComponents_of_locallyOfFiniteType K
      (normalizationOverField K sA ≫ sA) _
      (QuasiCompact.isCompact_preimage (f := normalizationOverField K sA ≫ τ.hom) _ U.2 hU))
    fun U _ ↦ by
      rw [morphismRestrict_comp]
      exact (Scheme.isBirational_normalization_morphismRestrict A
        (finite_irreducibleComponents_of_locallyOfFiniteType K sA) (τ.hom ⁻¹ᵁ U)).comp
        ((isBirational_of_iso τ).restrict U)
  exact ⟨ε, by rw [← Category.assoc, hε, Category.assoc, hτ]⟩

end AlgebraicGeometry

end
