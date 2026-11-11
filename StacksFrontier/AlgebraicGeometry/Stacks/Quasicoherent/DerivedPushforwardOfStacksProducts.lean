module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardOfStacksUnbounded
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulePullbackOfStacks
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProductsRightDerived

/-!
# The unbounded derived direct image of an algebraic stack: products and shifts

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let `Rf_* : D(𝒪_𝒳) ⥤ D(𝒪_𝒴)` be the
unbounded total derived direct image of fppf modules at module universe `u + 1`
(`AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacks`). This file proves:

* the direct image `f_*` carries K-injective complexes to K-injective complexes, because it has
  the exact left adjoint `f^*` (**Stacks 08BJ**);
* the derived categories `D(𝒪_𝒳)` have all products indexed by a type in `Type`, and `Rf_*`
  preserves them: a termwise product of K-injective complexes is K-injective and represents
  the product in the derived category (**Stacks 0BK6**), `f_*` preserves products and
  K-injectivity, and `Rf_*` is computed on K-injective complexes;
* `Rf_*` commutes with the shift, as every right derived functor of a functor commuting with
  the shift does.

No exactness of products of fppf modules is used (and none holds in general).

## Main results

* `AlgebraicGeometry.Stack.isKInjective_map_fppfModuleSheafPushforwardOfStacks`: `f_*` preserves
  K-injective complexes.
* `AlgebraicGeometry.Stack.hasProductsOfShape_derivedCategory_fppfModulesUnivLE`: products in
  `D(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.preservesLimitsOfShape_fppfDerivedPushforwardOfStacks`: `Rf_*`
  preserves products.
* `AlgebraicGeometry.Stack.commShift_fppfDerivedPushforwardOfStacks`: `Rf_*` commutes with
  shifts.
* `AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacksPiShiftIso`:
  `Rf_*(∏ⱼ Kⱼ[kⱼ]) ≅ ∏ⱼ (Rf_*Kⱼ)[kⱼ]`, compatibly with the projections, and its special case
  `AlgebraicGeometry.Stack.fppfDerivedPushforwardOfStacksPiShiftNatIso`.

## Implementation notes

The products are those indexed by an arbitrary `T : Type` (so `ℕ` and `ℕ × ℕ` among them), through
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective` and
`Stacks.KInjectiveProductsRightDerived.preservesProducts_of_isKInjective`.

## References

* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart, imported with the countable products of derived categories of sheaves of modules,
leave a stuck universe constraint against the modules at the pinned universe `u + 1`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

attribute [local instance] additive_fppfModuleSheafPushforwardOfStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Products in the derived category of fppf modules of an algebraic stack**, at module
universe `u + 1` and for any index type `T : Type`, from K-injective resolutions
(**Stacks 0BK6**). -/
instance hasProductsOfShape_derivedCategory_fppfModulesUnivLE
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)] (T : Type) :
    HasProductsOfShape T (DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒵)) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_of_exists_quasiIso_isKInjective
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒵)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **Stacks 08BJ for the direct image of fppf modules of algebraic stacks**: `f_*` carries
K-injective complexes to K-injective complexes, because its left adjoint `f^*` is exact. -/
theorem isKInjective_map_fppfModuleSheafPushforwardOfStacks
    (I : CochainComplex (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((fppfModuleSheafPushforwardOfStacks B S hS f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (fppfModuleAdjunctionOfStacks B S hS f) I

/-- The direct image of fppf modules preserves all small limits, being a right adjoint. -/
theorem preservesLimitsOfShape_fppfModuleSheafPushforwardOfStacks (T : Type) :
    PreservesLimitsOfShape (Discrete T) (fppfModuleSheafPushforwardOfStacks B S hS f) :=
  have h : PreservesLimitsOfSize.{0, 0} (fppfModuleSheafPushforwardOfStacks B S hS f) :=
    (fppfModuleAdjunctionOfStacks B S hS f).rightAdjoint_preservesLimits
  h.preservesLimitsOfShape

variable [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]

/-- The comparison `f_*I ⟶ Rf_*I` is an isomorphism at a K-injective complex `I`
(**Stacks 070K**). -/
theorem isIso_fppfDerivedPushforwardOfStacksUnit_app
    (I : CochainComplex (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳) ℤ) (hI : I.IsKInjective) :
    IsIso ((fppfDerivedPushforwardOfStacksUnit B S hS f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  have := isRightDerivedFunctor_fppfDerivedPushforwardOfStacks B S hS f
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((fppfModuleSheafPushforwardOfStacks B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒳)).2 DerivedCategory.Qh
      (fppfDerivedPushforwardOfStacks B S hS f) (fppfDerivedPushforwardOfStacksUnit B S hS f)
      I hI

/-- **The unbounded derived direct image preserves products** indexed by any `T : Type`
(in particular by `ℕ` and by `ℕ × ℕ`). -/
instance preservesLimitsOfShape_fppfDerivedPushforwardOfStacks (T : Type) :
    PreservesLimitsOfShape (Discrete T) (fppfDerivedPushforwardOfStacks B S hS f) :=
  have := preservesLimitsOfShape_fppfModuleSheafPushforwardOfStacks B S hS f T
  Stacks.KInjectiveProductsRightDerived.preservesProducts_of_isKInjective
    (fppfModuleSheafPushforwardOfStacks B S hS f) (fppfDerivedPushforwardOfStacks B S hS f)
    (fppfDerivedPushforwardOfStacksUnit B S hS f)
    (existsKInjectiveResolution_fppfModulesUnivLESucc B S hS 𝒳)
    (isIso_fppfDerivedPushforwardOfStacksUnit_app B S hS f)
    (fun I hI ↦ have := hI; isKInjective_map_fppfModuleSheafPushforwardOfStacks B S hS f I)

/-- **The unbounded derived direct image commutes with the shift**: it is the right derived
functor of a functor commuting with the shift, along a localization commuting with the shift. -/
instance commShift_fppfDerivedPushforwardOfStacks :
    (fppfDerivedPushforwardOfStacks B S hS f).CommShift ℤ :=
  have := isRightDerivedFunctor_fppfDerivedPushforwardOfStacks B S hS f
  Functor.IsRightDerivedFunctor.commShift _ (fppfDerivedPushforwardOfStacksUnit B S hS f)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ

/-- **`Rf_*` of a product of shifts is the product of the shifts of `Rf_*`**:
`Rf_*(∏ⱼ Kⱼ[kⱼ]) ≅ ∏ⱼ (Rf_*Kⱼ)[kⱼ]`, the product comparison followed by the commutation of
`Rf_*` with the shifts. -/
def fppfDerivedPushforwardOfStacksPiShiftIso {T : Type}
    (K : T → DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)) (k : T → ℤ) :
    (fppfDerivedPushforwardOfStacks B S hS f).obj (∏ᶜ fun j ↦ (K j)⟦k j⟧) ≅
      ∏ᶜ fun j ↦ ((fppfDerivedPushforwardOfStacks B S hS f).obj (K j))⟦k j⟧ :=
  PreservesProduct.iso (fppfDerivedPushforwardOfStacks B S hS f) (fun j ↦ (K j)⟦k j⟧) ≪≫
    Pi.mapIso fun j ↦ ((fppfDerivedPushforwardOfStacks B S hS f).commShiftIso (k j)).app (K j)

/-- The isomorphism `fppfDerivedPushforwardOfStacksPiShiftIso` is compatible with the
projections: on the factor `j` it is `Rf_*` of the projection followed by the commutation of
`Rf_*` with the shift by `kⱼ`. -/
@[reassoc (attr := simp)]
theorem fppfDerivedPushforwardOfStacksPiShiftIso_hom_π {T : Type}
    (K : T → DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)) (k : T → ℤ) (j : T) :
    (fppfDerivedPushforwardOfStacksPiShiftIso B S hS f K k).hom ≫ Pi.π _ j =
      (fppfDerivedPushforwardOfStacks B S hS f).map (Pi.π (fun j ↦ (K j)⟦k j⟧) j) ≫
        ((fppfDerivedPushforwardOfStacks B S hS f).commShiftIso (k j)).hom.app (K j) := by
  simp [fppfDerivedPushforwardOfStacksPiShiftIso]

/-- The special case `Rf_*(∏ₘ K[m]) ≅ ∏ₘ (Rf_*K)[m]`, the product over `m : ℕ`. -/
def fppfDerivedPushforwardOfStacksPiShiftNatIso
    (K : DerivedCategory (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)) :
    (fppfDerivedPushforwardOfStacks B S hS f).obj (∏ᶜ fun m : ℕ ↦ K⟦(m : ℤ)⟧) ≅
      ∏ᶜ fun m : ℕ ↦ ((fppfDerivedPushforwardOfStacks B S hS f).obj K)⟦(m : ℤ)⟧ :=
  fppfDerivedPushforwardOfStacksPiShiftIso B S hS f (fun _ ↦ K) fun m : ℕ ↦ (m : ℤ)

end AlgebraicGeometry.Stack
