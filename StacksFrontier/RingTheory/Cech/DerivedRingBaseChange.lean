module

public import StacksFrontier.RingTheory.Cech.KFlat
public import StacksFrontier.RingTheory.DerivedCompletion.FunctorialCechComplex

/-!
# The derived base-change map of a K-flat complex

Let `φ : A → B` be a homomorphism of commutative rings, `K` a complex of `A`-modules, `L` a
complex of `B`-modules and `u : K → L` a map of complexes of `A`-modules.
`Stacks.LocalCohomology.derivedBaseChange` is the induced morphism `K ⊗^L_A B → L` of `D(B)`,
defined by transposing `u` across the derived extension–restriction adjunction of
[Stacks, Tag 0GMT]. Condition (c) of [Stacks, Tag 099D] asks that this morphism be an
isomorphism.

This file factors that morphism: it is the comparison from derived to degreewise extension of
scalars at `K`, followed by the localization of the *complex-level* transpose of `u` across the
degreewise extension–restriction adjunction. When `K` is K-flat the comparison is invertible
([Stacks, Tag 06Y5], `TotalDerivedExtensionScalars.comparison_isIso_of_kFlat`), so for a K-flat
`K` the derived base-change map is an isomorphism exactly when the complex-level transpose
`B ⊗_A K → L` is a quasi-isomorphism — a statement with no derived category in it.

## Main results

* `Stacks.LocalCohomology.derivedBaseChange_eq`: the factorization.
* `Stacks.LocalCohomology.isIso_derivedBaseChange_of_kFlat`: for a K-flat `K`, the derived
  base-change map is an isomorphism as soon as the complex-level transpose is one.

## Implementation notes

The factorization is three rewrites: the transpose across an adjunction is the functor applied
to the map followed by the counit; the counit of the derived adjunction at a localized complex is
the degreewise counit
(`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`), which
is what makes the derived adjunction *normalized*; and the comparison is natural. The
`mapDerivedCategoryFactors` isomorphism that `derivedBaseChange` inserts to land in the derived
category cancels against the one the counit formula produces.

All rings live in a single universe and all module categories are `ModuleCat.{u}`, the convention
of `Stacks.LocalCohomology.FunctorialCechData`, whose condition (c) this is about.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The derived base-change map, factored.** For `u : K ⟶ L` a map from a complex of
`A`-modules to a complex of `B`-modules restricted to `A`, the induced morphism
`K ⊗^L_A B ⟶ L` of `D(B)` is the comparison from derived to degreewise extension of scalars at
`K`, followed by the localization of the complex-level transpose `B ⊗_A K ⟶ L` of `u`. -/
theorem derivedBaseChange_eq (φ : A →+* B) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) :
    derivedBaseChange φ u =
      (derivedExtensionScalarsGeneral.{u, u, u} φ).comparison.app K ≫
        DerivedCategory.Q.map
          ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv K L).symm u) := by
  have : Functor.IsLeftDerivedFunctor
      (F := (ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      (L := DerivedCategory.Q)
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor
      (derivedExtensionScalarsGeneral.{u, u, u} φ).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    (derivedExtensionScalarsGeneral.{u, u, u} φ).isLeftDerived
  have hcounit := derivedExtensionScalarsAdjunction_counit_app_eq.{u, u, u} φ
    (derivedExtensionScalarsGeneral.{u, u, u} φ).functor
    (derivedExtensionScalarsGeneral.{u, u, u} φ).comparison L
  have h0 : derivedBaseChange φ u =
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map (DerivedCategory.Q.map u ≫
          (ModuleCat.restrictScalars.{u, u, u} φ).mapDerivedCategoryFactors.inv.app L) ≫
        (derivedExtensionScalarsAdjunction.{u, u, u} φ
            (derivedExtensionScalarsGeneral.{u, u, u} φ).functor
            (derivedExtensionScalarsGeneral.{u, u, u} φ).comparison).counit.app
          (DerivedCategory.Q.obj L) := rfl
  have hcan : ∀ {Z : DerivedCategory (ModuleCat.{u} B)}
      (g : (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.obj
        (((ModuleCat.restrictScalars.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj L) ⟶ Z),
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map
          ((ModuleCat.restrictScalars.{u, u, u} φ).mapDerivedCategoryFactors.inv.app L) ≫
        (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map
            ((ModuleCat.restrictScalars.{u, u, u} φ).mapDerivedCategoryFactors.hom.app L) ≫ g =
        g := by
    intro Z g
    rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  rw [h0, hcounit]
  simp only [Functor.map_comp, Category.assoc, hcan, Adjunction.homEquiv_counit]
  exact (derivedExtensionScalarsGeneral.{u, u, u} φ).comparison.naturality_assoc u _

/-- **The derived base-change map of a K-flat complex.** If `K` is K-flat, degreewise extension of
scalars computes `K ⊗^L_A B` ([Stacks, Tag 06Y5]), so the derived base-change map `K ⊗^L_A B ⟶ L`
induced by `u : K ⟶ L` is an isomorphism as soon as the complex-level transpose
`B ⊗_A K ⟶ L` of `u` is. -/
theorem isIso_derivedBaseChange_of_kFlat (φ : A →+* B) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ ((ModuleCat.restrictScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L)
    (hK : CochainComplex.KFlat.{u, u} K)
    (hu : IsIso (DerivedCategory.Q.map
      ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv K L).symm u))) :
    IsIso (derivedBaseChange φ u) := by
  rw [derivedBaseChange_eq]
  exact IsIso.comp_isIso'
    ((derivedExtensionScalarsGeneral.{u, u, u} φ).comparison_isIso_of_kFlat K hK) hu

end Stacks.LocalCohomology

end
