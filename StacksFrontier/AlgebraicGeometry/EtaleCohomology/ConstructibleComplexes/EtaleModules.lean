module
public import StacksCore.CategoryTheory.Filtration.Preadditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteType

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRingUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Constructible and torsion sheaves of `Λ`-modules in the model `EtaleModules Λ X`

The derived lower shriek `Stacks.EtaleCohomology.derivedLowerShriekUnbounded` is a functor
between derived categories of `Stacks.EtaleCohomology.EtaleModules Λ X`, the sheaves of
`Λ`-modules on Mathlib's small étale site `X.smallEtaleTopology`. Constructibility of sheaves of
`Λ`-modules (Tag 03RW part (3)) is defined in this repository on the small étale site of
Tag 021B cut out of a big étale site, `AlgebraicGeometry.IsConstructibleModuleSheaf`. This file
brings that notion to `EtaleModules Λ X` by transport and, with the torsion predicate
`Stacks.EtaleCohomology.IsTorsionEtaleModule` of Section 0F7H, defines the derived categories
`D_c(X_étale, Λ)` and `D^+_{tors, c}(X_étale, Λ)` of Tag 0GK2 and
Section 0F7H.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleToBoundedSite`: the equivalence of sheaf categories between
  `EtaleModules Λ X` and the sheaves of `Λ`-modules on the small étale site of Tag 021B of any big
  étale site containing `X`, read from Mathlib's site to Stacks' site (it is restriction along the
  dense subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`).
* `Stacks.EtaleCohomology.IsConstructibleEtaleModule`: a sheaf of `Λ`-modules is constructible
  when its transport to the small étale site of Tag 021B of the canonical big étale site
  `AlgebraicGeometry.BigEtaleSite.containing X` is constructible.
* `Stacks.EtaleCohomology.IsConstructibleEtaleComplex`: `D_c(X_étale, Λ)`, the objects of
  `D(X_étale, Λ)` whose cohomology sheaves are constructible.
* `Stacks.EtaleCohomology.IsTorsionConstructibleEtaleComplexPlus`: `D^+_{tors, c}(X_étale, Λ)`,
  the bounded below objects whose cohomology sheaves are torsion and constructible.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff`:
  local constancy of finite type (Tag 093U) is the same on Mathlib's small étale site and on the
  small étale site of Tag 021B of any big étale site containing `X`.
* `Stacks.EtaleCohomology.isWeakSerreClass_isConstructibleEtaleModule`: for `Λ` Noetherian the
  constructible sheaves of `Λ`-modules form a weak Serre subcategory of `EtaleModules Λ X`
  (Tag 03RZ part (3), transported from
  `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf`).
* `Stacks.EtaleCohomology.isWeakSerreClass_isTorsionEtaleModule` and
  `Stacks.EtaleCohomology.isWeakSerreClass_isTorsion_and_isConstructibleEtaleModule`: torsion
  sheaves, and torsion constructible sheaves, form weak Serre subcategories, so that
  `D_c` and `D^+_{tors, c}` are triangulated subcategories
  (`DerivedCategoryB.derivedCategoryB_isTriangulated`,
  `DerivedCategoryB.derivedCategoryBPlus_isTriangulated`).
* `CategoryTheory.ObjectProperty.isWeakSerreClass_inverseImage_general` and
  `CategoryTheory.ObjectProperty.isWeakSerreClass_inf_general`: inverse images along exact
  functors and intersections of weak Serre classes are weak Serre classes.

## Implementation notes

The definition of constructibility goes through one big étale site, the canonical
`AlgebraicGeometry.BigEtaleSite.containing X`, whose small étale site is
`AlgebraicGeometry.Scheme.smallEtaleSite X`. Sheaves on it and on Mathlib's small étale site
correspond under `AlgebraicGeometry.SmallEtale.sheafEquiv`, so no second notion of constructibility
is introduced: the predicate is `AlgebraicGeometry.IsConstructibleModuleSheaf` itself, read
through that equivalence.

The sheaf categories involved have coefficients `ModuleCat.{max (u + 1) r} Λ`, the coefficient
universe of `EtaleModules Λ X`; at it the two coefficient hypotheses of
`AlgebraicGeometry.IsConstructibleModuleSheaf` are
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCat` and
`AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCat`.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 0GK2](https://stacks.math.columbia.edu/tag/0GK2)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ZeroObject

universe u r

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- Two weak Serre classes intersect in a weak Serre class. -/
theorem isWeakSerreClass_inf_general (P Q : ObjectProperty C) [P.IsWeakSerreClass]
    [Q.IsWeakSerreClass] :
    ObjectProperty.IsWeakSerreClass (fun X ↦ P X ∧ Q X : ObjectProperty C) :=
  (isWeakSerreClass_iff_prop_obj₂_of_exact _).2
    ⟨⟨0, P.prop_of_isZero (isZero_zero C), Q.prop_of_isZero (isZero_zero C)⟩,
      fun S hS h₀ h₁ h₃ h₄ ↦ ⟨P.prop_obj₂_of_exact S hS h₀.1 h₁.1 h₃.1 h₄.1,
        Q.prop_obj₂_of_exact S hS h₀.2 h₁.2 h₃.2 h₄.2⟩⟩

/-- The inverse image of a weak Serre class along an exact functor between abelian categories is
a weak Serre class. -/
theorem isWeakSerreClass_inverseImage_general (P : ObjectProperty D) [P.IsWeakSerreClass]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (P.inverseImage F).IsWeakSerreClass :=
  (isWeakSerreClass_iff_prop_obj₂_of_exact _).2
    ⟨⟨0, P.prop_of_isZero (F.map_isZero (isZero_zero C))⟩, fun S hS h₀ h₁ h₃ h₄ ↦
      P.prop_obj₂_of_exact ((F.mapComposableArrows 4).obj S)
        (Stacks.ConstantSheaf.mapComposableArrows_exact F S hS) h₀ h₁ h₃ h₄⟩

end CategoryTheory.ObjectProperty

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] {X : Scheme.{u}}

/-- **Transport to the small étale site of Tag 021B.** For a big étale site `B` containing `X`,
sheaves of `Λ`-modules on Mathlib's small étale site of `X` are sheaves on the small étale site of
Tag 021B cut out of `B`; this functor is restriction along the dense subsite inclusion, the inverse
of `AlgebraicGeometry.SmallEtale.sheafEquiv`, hence an equivalence. -/
abbrev etaleModuleToBoundedSite (B : BigEtaleSite.{u}) (hX : B.Contains X) :
    EtaleModules.{u, r} Λ X ⥤
      Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) r} Λ) :=
  (SmallEtale.sheafEquiv B X hX
    (ModuleCat.{max (u + 1) r} Λ)).inverse

/-- **Local constancy of finite type is the same in the two models** (Tag 093U). A sheaf of
`Λ`-modules on Mathlib's small étale site of `X` is locally constant of finite type exactly when
its transport to the small étale site of Tag 021B of a big étale site containing `X` is: the
inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite` is a fully faithful dense subsite inclusion,
so `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff`
applies. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff
    (B : BigEtaleSite.{u}) (hX : B.Contains X) (F : EtaleModules.{u, r} Λ X) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        (SmallEtale.topology B X hX) Λ ((etaleModuleToBoundedSite Λ B hX).obj F) ↔
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        X.smallEtaleTopology Λ F :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff
    (SmallEtale.topology B X hX) X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX) Λ F

/-- **Constructible sheaves of `Λ`-modules** (Tag 03RW part (3)) in the model `EtaleModules Λ X`:
the transport of the sheaf to the small étale site of Tag 021B of the canonical big étale site
`AlgebraicGeometry.BigEtaleSite.containing X` is constructible in the sense of
`AlgebraicGeometry.IsConstructibleModuleSheaf`. -/
abbrev IsConstructibleEtaleModule : ObjectProperty (EtaleModules.{u, r} Λ X) := fun F ↦
  IsConstructibleModuleSheaf (BigEtaleSite.containing X)
    ((BigEtaleSite.containing X).obj X (BigEtaleSite.contains_containing X)) Λ
    ((etaleModuleToBoundedSite Λ (BigEtaleSite.containing X)
      (BigEtaleSite.contains_containing X)).obj F)

/-- **`D_c(X_étale, Λ)`** (Tag 0GK2): the objects of `D(X_étale, Λ)` all of whose cohomology
sheaves are constructible sheaves of `Λ`-modules. -/
abbrev IsConstructibleEtaleComplex :
    ObjectProperty (DerivedCategory (EtaleModules.{u, r} Λ X)) :=
  DerivedCategoryB.derivedCategoryB (IsConstructibleEtaleModule Λ)

/-- **`D^+_{tors, c}(X_étale, Λ)`** (Section 0F7H with Tag 0GK2): the bounded below objects of
`D(X_étale, Λ)` all of whose cohomology sheaves are torsion and constructible. -/
abbrev IsTorsionConstructibleEtaleComplexPlus :
    ObjectProperty (DerivedCategory (EtaleModules.{u, r} Λ X)) :=
  DerivedCategoryB.derivedCategoryBPlus
    (fun F ↦ IsTorsionEtaleModule Λ X F ∧ IsConstructibleEtaleModule Λ F)

/-- **Stacks Project, Tag 03RZ part (3), in the model `EtaleModules Λ X`.** For a Noetherian
ring `Λ`, the constructible sheaves of `Λ`-modules form a weak Serre subcategory: the statement
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf` transported along the
equivalence `Stacks.EtaleCohomology.etaleModuleToBoundedSite`. -/
instance isWeakSerreClass_isConstructibleEtaleModule [IsNoetherianRing Λ] :
    (IsConstructibleEtaleModule.{u, r} Λ (X := X)).IsWeakSerreClass :=
  have := SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r, r}
    (BigEtaleSite.containing X)
    ((BigEtaleSite.containing X).obj X (BigEtaleSite.contains_containing X)) Λ
  have : (etaleModuleToBoundedSite Λ (BigEtaleSite.containing X)
      (BigEtaleSite.contains_containing X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  ObjectProperty.isWeakSerreClass_inverseImage_general
    (fun G : Sheaf (SmallEtale.topology (BigEtaleSite.containing X) X
        (BigEtaleSite.contains_containing X)) (ModuleCat.{max (u + 1) r} Λ) ↦
      IsConstructibleModuleSheaf (BigEtaleSite.containing X)
        ((BigEtaleSite.containing X).obj X (BigEtaleSite.contains_containing X)) Λ G)
    (etaleModuleToBoundedSite Λ (BigEtaleSite.containing X) (BigEtaleSite.contains_containing X))

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp in
/-- The torsion condition of Section 0F7H on a sheaf of `Λ`-modules is the torsion condition on its
underlying abelian sheaf. -/
theorem isTorsionEtaleModule_iff_torsionSheafProperty_unconditional (F : EtaleModules.{u, r} Λ X) :
    IsTorsionEtaleModule Λ X F ↔
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj F) :=
  Iff.rfl

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp in
/-- **Torsion sheaves of `Λ`-modules form a weak Serre subcategory**: they are the inverse image of
the Serre class of torsion abelian sheaves along the exact forgetful functor. -/
instance isWeakSerreClass_isTorsionEtaleModule :
    ObjectProperty.IsWeakSerreClass (IsTorsionEtaleModule.{u, r} Λ X) :=
  ObjectProperty.isWeakSerreClass_inverseImage_general
    (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology)
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X)

/-- For a Noetherian ring `Λ`, the torsion constructible sheaves of `Λ`-modules form a weak Serre
subcategory; `D^+_{tors, c}(X_étale, Λ)` is cut out by it. -/
instance isWeakSerreClass_isTorsion_and_isConstructibleEtaleModule [IsNoetherianRing Λ] :
    ObjectProperty.IsWeakSerreClass (fun F : EtaleModules.{u, r} Λ X ↦
      IsTorsionEtaleModule Λ X F ∧ IsConstructibleEtaleModule Λ F) :=
  ObjectProperty.isWeakSerreClass_inf_general _ _

end Stacks.EtaleCohomology

end
