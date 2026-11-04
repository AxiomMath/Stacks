module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConcreteDGFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated

/-!
# Restriction of scalars is an exact functor of triangulated categories

Let `X` be a ringed site and let `φ : A ⟶ B` be a unit-preserving homomorphism of sheaves of
differential graded algebras on `X`. Restriction of scalars `res_φ : Mod(B, d) ⥤ Mod(A, d)` does
not change the underlying complexes, so it extends to homogeneous maps by the identity on
underlying cochains. It is therefore a functor of differential graded categories, and by
[Stacks, Tag 0FQF] the induced functor `K(Mod(B, d)) ⥤ K(Mod(A, d))` commutes with the
translations and is triangulated. The functor `D(B, d) ⥤ D(A, d)` it induces on the derived
categories inherits both properties along the localization functors.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.restrictionConcreteDGFunctor`: restriction of scalars
  extended to homogeneous maps.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopyRestriction_commShift` and
  `SheafOfModules.DifferentialGradedModule.homotopyRestriction_isTriangulated`: restriction of
  scalars on the homotopy categories commutes with the translations and is triangulated.
* `SheafOfModules.DifferentialGradedModule.derivedRestriction_commShift` and
  `SheafOfModules.DifferentialGradedModule.derivedRestriction_isTriangulated`: **restriction of
  scalars on the derived categories commutes with the translations and is triangulated.**

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A B : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : A ⟶ B)
  (hφ : φ.PreservesOne)

/-- **Restriction of scalars, extended to homogeneous maps**: a cochain between right
differential graded `B`-modules which commutes with the action of `B` is the same cochain between
their restrictions, and commutes with the action of `A` through `φ`. -/
def restrictionConcreteDGFunctor : ConcreteDGFunctor.{u, v, v, w, w} B A where
  functor := restriction.{u, v, w} φ hφ
  mapCochain c _ := c
  isActionLinear_mapCochain _ hc p q m hpq U x a :=
    hc p q m hpq U x ((φ.toHomologicalComplex.f m).val.app U a)
  mapCochain_add _ _ _ _ _ := rfl
  mapCochain_delta _ _ _ := rfl
  mapCochain_comp _ _ _ _ _ _ := rfl
  mapCochain_ofHom _ := rfl

/-- The functor of homotopy categories induced by `restrictionConcreteDGFunctor` is restriction
of scalars on the homotopy categories. -/
theorem restrictionConcreteDGFunctor_homotopyFunctor :
    (restrictionConcreteDGFunctor.{u, v, w} φ hφ).homotopyFunctor =
      homotopyRestriction.{u, v, w} φ hφ :=
  rfl

/-- Restriction of scalars on the homotopy categories commutes with the translations. -/
@[instance_reducible]
instance homotopyRestriction_commShift : (homotopyRestriction.{u, v, w} φ hφ).CommShift ℤ :=
  (restrictionConcreteDGFunctor.{u, v, w} φ hφ).commShift

/-- **Restriction of scalars on the homotopy categories is triangulated** (Tag 0FQF). -/
instance homotopyRestriction_isTriangulated :
    (homotopyRestriction.{u, v, w} φ hφ).IsTriangulated :=
  (restrictionConcreteDGFunctor.{u, v, w} φ hφ).isTriangulated

section Derived

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction of scalars on the derived categories is the localization lift of restriction of
scalars on the homotopy categories followed by the localization functor of `D(A, d)`. -/
instance derivedRestriction_lifting :
    Localization.Lifting (toDerivedCategory.{u, v, w} B) (quasiIsomorphisms.{u, v, w} B)
      (homotopyRestriction.{u, v, w} φ hφ ⋙ toDerivedCategory.{u, v, w} A)
      (derivedRestriction.{u, v, w} φ hφ) :=
  ⟨derivedRestrictionIso.{u, v, w} φ hφ⟩

/-- **Restriction of scalars on the derived categories commutes with the translations**, by the
structure induced along the localization functor from that of restriction of scalars on the
homotopy categories. -/
@[instance_reducible]
instance derivedRestriction_commShift : (derivedRestriction.{u, v, w} φ hφ).CommShift ℤ :=
  Functor.commShiftOfLocalization (toDerivedCategory.{u, v, w} B) (quasiIsomorphisms.{u, v, w} B)
    ℤ (homotopyRestriction.{u, v, w} φ hφ ⋙ toDerivedCategory.{u, v, w} A) _

/-- The identification `derivedRestrictionIso` commutes with the translations. -/
instance derivedRestrictionIso_commShift :
    NatTrans.CommShift (derivedRestrictionIso.{u, v, w} φ hφ).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (toDerivedCategory.{u, v, w} B)
    (quasiIsomorphisms.{u, v, w} B) ℤ
    (homotopyRestriction.{u, v, w} φ hφ ⋙ toDerivedCategory.{u, v, w} A)
    (derivedRestriction.{u, v, w} φ hφ)

/-- **Restriction of scalars on the derived categories is an exact functor of triangulated
categories.** -/
instance derivedRestriction_isTriangulated :
    (derivedRestriction.{u, v, w} φ hφ).IsTriangulated :=
  have := Localization.essSurj_mapArrow (toDerivedCategory.{u, v, w} B)
    (quasiIsomorphisms.{u, v, w} B)
  Functor.isTriangulated_of_precomp_iso (derivedRestrictionIso.{u, v, w} φ hφ)

end Derived

end SheafOfModules.DifferentialGradedModule
