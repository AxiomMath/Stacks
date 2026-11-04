module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingInjectiveQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The total alternating Čech complex of an unbounded complex and derived global sections

Let `(X, O_X)` be a ringed space and let `U : I → Opens X` be a *finite* open covering of `X`.
For an arbitrary complex `F^•` of `O_X`-modules there is a canonical map

`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(X, F^•)`,

functorial in `F^•` and compatible with the augmentation of Tag 08C0.

## Main definitions

* `Stacks.Cech.globalSectionsUliftDerivedFunctor`: the complex of global sections of an
  unbounded complex of sheaves of modules, in `D(Ab)`.
* `Stacks.Cech.alternatingCechDerivedFunctor`: the total alternating Čech complex, in `D(Ab)`.
* `Stacks.Cech.unboundedDerivedGlobalSectionsFunctor`: derived global sections of an unbounded
  complex, represented by the global sections of its functorial K-injective resolution.
* `Stacks.Cech.globalSectionsToUnboundedDerived`: the canonical map from ordinary to derived
  global sections.
* `Stacks.Cech.AlternatingCechToDerivedGlobalSections`: the comparison maps for all finite
  coverings at once, together with their compatibility with Tag 08C0.

## Main results

* `Stacks.Cech.alternatingCechToDerivedGlobalSections`: the canonical system of comparison maps
  exists. This is Tag 08C1.
* `Stacks.Cech.isIso_globalSectionsToAlternatingCechDerived_of_injective`: on a complex of
  injectives the augmentation of Tag 08C0 is invertible in the derived category.

## Implementation notes

Derived global sections of an unbounded complex are represented by the global sections of its
functorial K-injective resolution (Tag 079P), and the canonical map from ordinary to derived
global sections is global sections of the resolution inclusion. Functoriality in the
coefficient complex is part of the natural-transformation structure, and compatibility with
Tag 08C0 is the `globalSections` field.

The space and the coefficient universes coincide, as the Čech product API and Tag 01EG
require.

## References

* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08C0](https://stacks.math.columbia.edu/tag/08C0)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

noncomputable section

variable (X : TopCat.{u})

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

attribute [local instance] HasDerivedCategory.standard

/-- Sheaves of modules on a site form a Grothendieck abelian category. -/
local instance modulesIsGrothendieckAbelian
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  inferInstance

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The functorial K-injective resolution of an unbounded complex of sheaves of modules,
from Tag 079P. -/
noncomputable abbrev kInjectiveResolution :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ CochainComplex (SheafOfModules.{u} R) ℤ :=
  Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} R)

/-- The inclusion of an unbounded complex of sheaves of modules into its functorial
K-injective resolution, from Tag 079P. -/
noncomputable abbrev kInjectiveResolutionInclusion :
    Functor.id (CochainComplex (SheafOfModules.{u} R) ℤ) ⟶ kInjectiveResolution X R :=
  Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} R)

/-- The inclusion of a complex of sheaves of modules into its functorial K-injective
resolution, at a fixed complex. -/
noncomputable def kInjectiveResolutionUnit (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    K ⟶ (kInjectiveResolution X R).obj K :=
  (kInjectiveResolutionInclusion X R).app K

/-- The complex of global sections of an unbounded complex of sheaves of modules, viewed in
`D(Ab)`. -/
noncomputable def globalSectionsUliftDerivedFunctor :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  underlyingPresheafComplexFunctor X R ⋙ globalSectionsUliftComplexFunctor.{u, u, u} X ⋙
    DerivedCategory.Q

/-- The total alternating Čech complex of an unbounded complex of sheaves of modules, viewed
in `D(Ab)`. -/
noncomputable def alternatingCechDerivedFunctor {I : Type u} (U : I → Opens X) :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  underlyingPresheafComplexFunctor X R ⋙ alternatingCechTotalComplexFunctor U ⋙
    DerivedCategory.Q

/-- Derived global sections of an unbounded complex of sheaves of modules: the global sections
of its functorial K-injective resolution, viewed in `D(Ab)`. -/
noncomputable def unboundedDerivedGlobalSectionsFunctor :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  kInjectiveResolution X R ⋙ globalSectionsUliftDerivedFunctor X R

/-- The augmentation of Tag 08C0, followed by passage to the derived category. -/
noncomputable def globalSectionsToAlternatingCechDerived {I : Type u} (U : I → Opens X) :
    globalSectionsUliftDerivedFunctor X R ⟶ alternatingCechDerivedFunctor X R U :=
  Functor.whiskerRight
    (Functor.whiskerLeft (underlyingPresheafComplexFunctor X R)
      (globalSectionsToAlternatingCech X U))
    DerivedCategory.Q

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- The component of `globalSectionsToAlternatingCechDerived` at a complex `K` is the image in the
derived category of the augmentation at the underlying complex of presheaves of `K`. -/
@[simp]
theorem globalSectionsToAlternatingCechDerived_app {I : Type u} (U : I → Opens X)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (globalSectionsToAlternatingCechDerived X R U).app K =
      DerivedCategory.Q.map ((globalSectionsToAlternatingCech X U).app
        ((underlyingPresheafComplexFunctor X R).obj K)) :=
  rfl

/-- **The canonical map from ordinary to derived global sections**: global sections of the
inclusion of a complex into its K-injective resolution. -/
noncomputable def globalSectionsToUnboundedDerived :
    globalSectionsUliftDerivedFunctor X R ⟶ unboundedDerivedGlobalSectionsFunctor X R :=
  (Functor.leftUnitor (globalSectionsUliftDerivedFunctor X R)).inv ≫
    Functor.whiskerRight (kInjectiveResolutionInclusion X R)
      (globalSectionsUliftDerivedFunctor X R)

/-- The component of `globalSectionsToUnboundedDerived` at a complex `K` is global sections of
the inclusion of `K` into its K-injective resolution. -/
@[simp]
theorem globalSectionsToUnboundedDerived_app (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (globalSectionsToUnboundedDerived X R).app K =
      (globalSectionsUliftDerivedFunctor X R).map (kInjectiveResolutionUnit X R K) :=
  Category.id_comp _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- On a complex of injectives the augmentation of Tag 08C0 is invertible in the derived
category. -/
theorem isIso_globalSectionsToAlternatingCechDerived_of_injective
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (L : CochainComplex (SheafOfModules.{u} R) ℤ) (hL : ∀ n : ℤ, Injective (L.X n)) :
    IsIso ((globalSectionsToAlternatingCechDerived X R U).app L) := by
  have := quasiIso_globalSectionsToAlternatingCech_of_injective X U hU L hL
  show IsIso (DerivedCategory.Q.map
    ((globalSectionsToAlternatingCech X U).app ((underlyingPresheafComplexFunctor X R).obj L)))
  infer_instance

/-- The augmentation of Tag 08C0 on the functorial K-injective resolution. -/
noncomputable def kInjectiveResolutionAlternatingCechMap {I : Type u} (U : I → Opens X) :
    unboundedDerivedGlobalSectionsFunctor X R ⟶
      kInjectiveResolution X R ⋙ alternatingCechDerivedFunctor X R U :=
  Functor.whiskerLeft (kInjectiveResolution X R)
    (globalSectionsToAlternatingCechDerived X R U)

/-- The component of `kInjectiveResolutionAlternatingCechMap` at a complex `K` is the
augmentation at the K-injective resolution of `K`. -/
@[simp]
theorem kInjectiveResolutionAlternatingCechMap_app {I : Type u} (U : I → Opens X)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (kInjectiveResolutionAlternatingCechMap X R U).app K =
      (globalSectionsToAlternatingCechDerived X R U).app
        ((kInjectiveResolution X R).obj K) :=
  rfl

/-- On the functorial K-injective resolution the augmentation of Tag 08C0 is an isomorphism. -/
theorem isIso_kInjectiveResolutionAlternatingCechMap
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    IsIso (kInjectiveResolutionAlternatingCechMap X R U) := by
  have happ : ∀ K, IsIso ((kInjectiveResolutionAlternatingCechMap X R U).app K) := fun K ↦
    isIso_globalSectionsToAlternatingCechDerived_of_injective X R U hU
      ((kInjectiveResolution X R).obj K) (fun _ ↦ inferInstance)
  exact NatIso.isIso_of_isIso_app _

/-- On the functorial K-injective resolution the augmentation of Tag 08C0 is an isomorphism. -/
noncomputable def kInjectiveResolutionAlternatingCechIso
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    unboundedDerivedGlobalSectionsFunctor X R ≅
      kInjectiveResolution X R ⋙ alternatingCechDerivedFunctor X R U := by
  have := isIso_kInjectiveResolutionAlternatingCechMap X R U hU
  exact asIso (kInjectiveResolutionAlternatingCechMap X R U)

/-- The component of the forward map of `kInjectiveResolutionAlternatingCechIso` at a complex
`K` is the augmentation at the K-injective resolution of `K`. -/
@[simp]
theorem kInjectiveResolutionAlternatingCechIso_hom_app
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (kInjectiveResolutionAlternatingCechIso X R U hU).hom.app K =
      (globalSectionsToAlternatingCechDerived X R U).app
        ((kInjectiveResolution X R).obj K) :=
  rfl

/-- The total alternating Čech complex of the inclusion of a complex into its K-injective
resolution, in the derived category. -/
noncomputable def alternatingCechResolutionMap {I : Type u} (U : I → Opens X)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (alternatingCechDerivedFunctor X R U).obj K ⟶
      (kInjectiveResolution X R ⋙ alternatingCechDerivedFunctor X R U).obj K :=
  (alternatingCechDerivedFunctor X R U).map (kInjectiveResolutionUnit X R K)

/-- The comparison map from the total alternating Čech complex to derived global sections, for
one finite covering: resolve, then invert the augmentation of Tag 08C0 on the resolution. -/
noncomputable def alternatingCechToDerivedComparison
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    alternatingCechDerivedFunctor X R U ⟶ unboundedDerivedGlobalSectionsFunctor X R :=
  (Functor.leftUnitor (alternatingCechDerivedFunctor X R U)).inv ≫
    Functor.whiskerRight (kInjectiveResolutionInclusion X R)
      (alternatingCechDerivedFunctor X R U) ≫
    (kInjectiveResolutionAlternatingCechIso X R U hU).symm.hom

/-- The components of the comparison map: resolve, then invert the augmentation of Tag 08C0 on
the resolution. -/
theorem alternatingCechToDerivedComparison_app
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (alternatingCechToDerivedComparison X R U hU).app K =
      alternatingCechResolutionMap X R U K ≫
        (kInjectiveResolutionAlternatingCechIso X R U hU).inv.app K := by
  simp only [alternatingCechToDerivedComparison, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Iso.symm_hom, Category.id_comp]
  rfl

/-- **Compatibility with Tag 08C0.** After the augmentation of Tag 08C0 the comparison map is
the canonical map from ordinary to derived global sections. -/
theorem globalSectionsToAlternatingCechDerived_comp_alternatingCechToDerivedComparison
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (globalSectionsToAlternatingCechDerived X R U).app K ≫
        (alternatingCechToDerivedComparison X R U hU).app K =
      (globalSectionsToUnboundedDerived X R).app K := by
  refine (cancel_mono ((kInjectiveResolutionAlternatingCechIso X R U hU).hom.app K)).mp ?_
  simp only [alternatingCechToDerivedComparison_app, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, globalSectionsToUnboundedDerived_app]
  exact ((globalSectionsToAlternatingCechDerived X R U).naturality
    (kInjectiveResolutionUnit X R K)).symm

/-- A functorial comparison from the total alternating Čech complex to derived global sections,
simultaneously for all finite open coverings. The second field is the compatibility with the
augmentation of Tag 08C0. -/
structure AlternatingCechToDerivedGlobalSections where
  /-- The comparison for a particular finite open covering. -/
  map {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    alternatingCechDerivedFunctor X R U ⟶ unboundedDerivedGlobalSectionsFunctor X R
  /-- After the augmentation of Tag 08C0, the comparison is the canonical map from ordinary to
  derived global sections. -/
  globalSections {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    globalSectionsToAlternatingCechDerived X R U ≫ map U hU =
      globalSectionsToUnboundedDerived X R

/-- **Stacks Project, Tag 08C1.** For a ringed space `(X, O_X)` and a finite open covering `U`
of `X`, the total alternating Čech complex of an unbounded complex of `O_X`-modules has a
canonical map to its derived global sections, functorial in the complex and compatible with
the augmentation of Tag 08C0. -/
@[stacks 08C1]
noncomputable def alternatingCechToDerivedGlobalSections :
    AlternatingCechToDerivedGlobalSections X R where
  map U hU := alternatingCechToDerivedComparison X R U hU
  globalSections U hU := by
    ext K
    exact globalSectionsToAlternatingCechDerived_comp_alternatingCechToDerivedComparison
      X R U hU K

/-- The composite of the augmentation of Tag 08C0 with the comparison map does not depend on
the covering. -/
theorem AlternatingCechToDerivedGlobalSections.globalSections_comp
    (S : AlternatingCechToDerivedGlobalSections X R)
    {I J : Type u} [Finite I] [Finite J]
    (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (V : J → Opens X) (hV : (⊤ : Opens X) = iSup V) :
    globalSectionsToAlternatingCechDerived X R U ≫ S.map U hU =
      globalSectionsToAlternatingCechDerived X R V ≫ S.map V hV :=
  (S.globalSections U hU).trans (S.globalSections V hV).symm

end

end Stacks.Cech

end
