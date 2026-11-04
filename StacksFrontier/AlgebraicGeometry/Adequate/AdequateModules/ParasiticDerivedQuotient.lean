module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryBounded
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Parasitic

/-!
# The bounded derived quotients of adequate modules by the parasitic ones

Let `S` be a scheme, `τ` one of the five topologies, and let `𝒞 ⊂ Adeq(𝒪)` be the full
subcategory of parasitic adequate modules on a chosen big `τ`-site over `S`. [Stacks, Tag 06ZQ]
states

  `D(Adeq(𝒪))/D_𝒞(Adeq(𝒪)) = D(QCoh(𝒪_S))`

*and similarly for the bounded versions*. The unbounded statement is
`Stacks.Adequate.BigSite.isLocalization_mapDerivedCategory_restrictModuleQCoh`
(`StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Parasitic`); this file proves the three
bounded ones

  `D⁺(Adeq(𝒪))/D⁺_𝒞(Adeq(𝒪)) = D⁺(QCoh(𝒪_S))`,
  `D⁻(Adeq(𝒪))/D⁻_𝒞(Adeq(𝒪)) = D⁻(QCoh(𝒪_S))`,
  `Dᵇ(Adeq(𝒪))/Dᵇ_𝒞(Adeq(𝒪)) = Dᵇ(QCoh(𝒪_S))`.

In each, the functor induced by the exact functor `v : Adeq(𝒪) ⥤ QCoh(𝒪_S)` of
[Stacks, Tag 06VN] on the bounded derived categories (Mathlib's `DerivedCategory.Plus`,
`DerivedCategory.Minus`, `DerivedCategory.Bounded`) is a localization functor for the morphisms
whose cone has all its cohomology objects in `𝒞`, i.e. is the Verdier quotient of the bounded
derived category of `Adeq(𝒪)` by its triangulated subcategory `D^?_𝒞(Adeq(𝒪))`
(`DerivedCategoryB.derivedCategoryB`, [Stacks, Tag 06UP]).

## Main results

* `Stacks.Adequate.BigSite.isLocalization_mapDerivedCategoryPlus_restrictModuleQCoh`,
  `Stacks.Adequate.BigSite.isLocalization_mapDerivedCategoryMinus_restrictModuleQCoh` and
  `Stacks.Adequate.BigSite.isLocalization_mapDerivedCategoryBounded_restrictModuleQCoh`:
  [Stacks, Tag 06ZQ], the bounded versions.

## Implementation notes

The source's proof is "Derived Categories, Lemma [Stacks, Tag 06XM]", whose bounded versions are
`isLocalization_mapDerivedCategoryPlus_of_leftAdjoint` and its two siblings, in the namespace
`CategoryTheory.ObjectProperty.SerreClassLocalization`. Their inputs here are all proved: `Adeq(𝒪)`
is abelian ([Stacks, Tag 06VQ], `Stacks.Adequate.abelian_adequate`), `v` is exact
(`StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.RestrictionExactness`), `v` realises the
Serre quotient of `Adeq(𝒪)` by `𝒞` ([Stacks, Tag 06ZN],
`Stacks.Adequate.BigSite.isLocalization_restrictModuleQCoh`), and `v` has the fully faithful left
adjoint `u` of [Stacks, Tag 06VN] (`Stacks.Adequate.BigSite.adeqAdjunction`).

## References

* [Stacks Project, Tag 06ZQ](https://stacks.math.columbia.edu/tag/06ZQ)
* [Stacks Project, Tag 06XM](https://stacks.math.columbia.edu/tag/06XM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategoryB

universe u w w₁ w₂

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

attribute [local instance] abelian_adequate

variable [HasDerivedCategory.{w₁} (adequate.{u, u} B).FullSubcategory]
  [HasDerivedCategory.{w₂} (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]

private instance : B.associatedModuleAdeq.Full := B.full_associatedModuleAdeq

private instance : B.associatedModuleAdeq.Faithful := B.faithful_associatedModuleAdeq

/-- **[Stacks, Tag 06ZQ], bounded below version.**
`D⁺(Adeq(𝒪))/D⁺_𝒞(Adeq(𝒪)) = D⁺(QCoh(𝒪_S))`: the functor
`D⁺(v) : D⁺(Adeq(𝒪)) ⥤ D⁺(QCoh(𝒪_S))` is a localization functor for the morphisms of
`D⁺(Adeq(𝒪))` whose cone has all its cohomology objects in the Serre subcategory `𝒞` of
parasitic adequate modules. -/
@[stacks 06ZQ "bounded below version `D⁺(Adeq(𝒪))/D⁺_𝒞(Adeq(𝒪)) = D⁺(QCoh(𝒪_S))`"]
public theorem BigSite.isLocalization_mapDerivedCategoryPlus_restrictModuleQCoh :
    B.restrictModuleQCoh.mapDerivedCategoryPlus.IsLocalization
      ((derivedCategoryB B.parasiticAdequate).inverseImage DerivedCategory.Plus.ι).trW := by
  exact ObjectProperty.SerreClassLocalization.isLocalization_mapDerivedCategoryPlus_of_leftAdjoint
    B.restrictModuleQCoh B.adeqAdjunction B.parasiticAdequate

/-- **[Stacks, Tag 06ZQ], bounded above version.**
`D⁻(Adeq(𝒪))/D⁻_𝒞(Adeq(𝒪)) = D⁻(QCoh(𝒪_S))`: the functor
`D⁻(v) : D⁻(Adeq(𝒪)) ⥤ D⁻(QCoh(𝒪_S))` is a localization functor for the morphisms of
`D⁻(Adeq(𝒪))` whose cone has all its cohomology objects in the Serre subcategory `𝒞` of
parasitic adequate modules. -/
@[stacks 06ZQ "bounded above version `D⁻(Adeq(𝒪))/D⁻_𝒞(Adeq(𝒪)) = D⁻(QCoh(𝒪_S))`"]
public theorem BigSite.isLocalization_mapDerivedCategoryMinus_restrictModuleQCoh :
    B.restrictModuleQCoh.mapDerivedCategoryMinus.IsLocalization
      ((derivedCategoryB B.parasiticAdequate).inverseImage DerivedCategory.Minus.ι).trW := by
  exact ObjectProperty.SerreClassLocalization.isLocalization_mapDerivedCategoryMinus_of_leftAdjoint
    B.restrictModuleQCoh B.adeqAdjunction B.parasiticAdequate

/-- **[Stacks, Tag 06ZQ], bounded version.**
`Dᵇ(Adeq(𝒪))/Dᵇ_𝒞(Adeq(𝒪)) = Dᵇ(QCoh(𝒪_S))`: the functor
`Dᵇ(v) : Dᵇ(Adeq(𝒪)) ⥤ Dᵇ(QCoh(𝒪_S))` is a localization functor for the morphisms of
`Dᵇ(Adeq(𝒪))` whose cone has all its cohomology objects in the Serre subcategory `𝒞` of
parasitic adequate modules. -/
@[stacks 06ZQ "bounded version `Dᵇ(Adeq(𝒪))/Dᵇ_𝒞(Adeq(𝒪)) = Dᵇ(QCoh(𝒪_S))`"]
public theorem BigSite.isLocalization_mapDerivedCategoryBounded_restrictModuleQCoh :
    B.restrictModuleQCoh.mapDerivedCategoryBounded.IsLocalization
      ((derivedCategoryB B.parasiticAdequate).inverseImage DerivedCategory.Bounded.ι).trW := by
  exact
    ObjectProperty.SerreClassLocalization.isLocalization_mapDerivedCategoryBounded_of_leftAdjoint
      B.restrictModuleQCoh B.adeqAdjunction B.parasiticAdequate

end Stacks.Adequate

end
