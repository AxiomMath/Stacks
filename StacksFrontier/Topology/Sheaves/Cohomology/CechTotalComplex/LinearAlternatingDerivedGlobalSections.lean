module

public import StacksFrontier.Algebra.Homology.CatCenterModuleLift
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingDerivedGlobalSections

/-!
# The comparison of Tag 08C1 linearly over a ring acting centrally

Let `(X, O_X)` be a ringed space, let `A` be a ring and let `ρ : A →+* CatCenter (Mod(O_X))`
be a ring map into the centre of the category of `O_X`-modules — for instance multiplication
through a ring map `A → Γ(X, O_X)` into global sections when the structure sheaf is
commutative. Then `a ∈ A` acts on every complex of `O_X`-modules by a morphism of complexes,
naturally in the complex, and therefore on the complex of global sections and on the total
alternating Čech complex of every family of opens; these actions commute with every map the
constructions produce. For a finite open covering `U` of `X` this file builds

`Tot(Č_alt^•(U, F^•)) ⟶ RΓ(X, F^•)` in `D(A)`,

natural in the complex `F^•` and compatible with the augmentation of Tag 08C0, and proves that
it is an isomorphism exactly when the comparison map of Tag 08C1 in `D(Ab)` is one.

## Main definitions

* `complexCenter`: the action of `A` on complexes of `O_X`-modules.
* `linearAlternatingCechTotalComplexFunctor` and `linearGlobalSectionsComplexFunctor`: the total
  alternating Čech complex and the complex of global sections, as complexes of `A`-modules.
* `linearGlobalSectionsToAlternatingCech`: the augmentation of Tag 08C0, `A`-linearly.
* `linearAlternatingCechDerivedFunctor` and `linearUnboundedDerivedGlobalSectionsFunctor`: the
  two sides, in `D(A)`.
* `linearAlternatingCechToDerivedComparison`: the comparison map, in `D(A)`.

## Main results

* `linearGlobalSectionsToAlternatingCechDerived_comp_linearAlternatingCechToDerivedComparison`:
  after the augmentation of Tag 08C0 the comparison is the canonical map from global sections
  to derived global sections.
* `isIso_linearAlternatingCechToDerivedComparison_app_iff`: the comparison in `D(A)` is
  invertible at a complex exactly when the one in `D(Ab)` is.

## Implementation notes

The `A`-linear complexes are the abelian-group-valued complexes
`alternatingCechTotalComplexFunctor` and `globalSectionsUliftComplexFunctor` with the module
structure induced by the central action (`Stacks.CenterLift.liftFunctor`). Derived global
sections are represented, as in `D(Ab)`, by the global sections of the functorial K-injective
resolution of Tag 079P.

## References

* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08C0](https://stacks.math.columbia.edu/tag/08C0)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.CenterLift

universe u w

namespace Stacks.Cech

noncomputable section

variable (X : TopCat.{u})

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

attribute [local instance] HasDerivedCategory.standard

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {A : Type w} [Ring A] (ρ : A →+* CatCenter (SheafOfModules.{u} R))

/-- The action of `A` on complexes of `O_X`-modules, termwise through `ρ`. -/
def complexCenter : A →+* CatCenter (CochainComplex (SheafOfModules.{u} R) ℤ) :=
  catCenterHomologicalComplex.comp ρ

/-- The total alternating Čech complex of a complex of `O_X`-modules, as a complex of
`A`-modules. -/
def linearAlternatingCechTotalComplexFunctor {I : Type u} (U : I → Opens X) :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  liftFunctor (underlyingPresheafComplexFunctor X R ⋙ alternatingCechTotalComplexFunctor U)
    (complexCenter X R ρ)

/-- The complex of global sections of a complex of `O_X`-modules, as a complex of
`A`-modules. -/
def linearGlobalSectionsComplexFunctor :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  liftFunctor (underlyingPresheafComplexFunctor X R ⋙
    globalSectionsUliftComplexFunctor.{u, u, u} X) (complexCenter X R ρ)

/-- The augmentation of Tag 08C0, from the complex of global sections to the total alternating
Čech complex, as a map of complexes of `A`-modules. -/
def linearGlobalSectionsToAlternatingCech {I : Type u} (U : I → Opens X) :
    linearGlobalSectionsComplexFunctor X R ρ ⟶ linearAlternatingCechTotalComplexFunctor X R ρ U :=
  liftNatTrans (complexCenter X R ρ)
    (Functor.whiskerLeft (underlyingPresheafComplexFunctor X R)
      (globalSectionsToAlternatingCech.{u, u, u} X U))

/-- The total alternating Čech complex of a complex of `O_X`-modules, in `D(A)`. -/
abbrev linearAlternatingCechDerivedFunctor {I : Type u} (U : I → Opens X) :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  linearAlternatingCechTotalComplexFunctor X R ρ U ⋙ DerivedCategory.Q

/-- Derived global sections of a complex of `O_X`-modules, in `D(A)`: the global sections of
its functorial K-injective resolution. -/
abbrev linearUnboundedDerivedGlobalSectionsFunctor :
    CochainComplex (SheafOfModules.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  kInjectiveResolution X R ⋙ linearGlobalSectionsComplexFunctor X R ρ ⋙ DerivedCategory.Q

/-- The canonical map from global sections to derived global sections, in `D(A)`: global
sections of the inclusion of a complex into its K-injective resolution. -/
def linearGlobalSectionsToUnboundedDerived :
    linearGlobalSectionsComplexFunctor X R ρ ⋙ DerivedCategory.Q ⟶
      linearUnboundedDerivedGlobalSectionsFunctor X R ρ :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (kInjectiveResolutionInclusion X R)
      (linearGlobalSectionsComplexFunctor X R ρ ⋙ DerivedCategory.Q)

/-- The canonical map from global sections to derived global sections at a complex `K` is the
image of the inclusion of `K` into its K-injective resolution. -/
theorem linearGlobalSectionsToUnboundedDerived_app (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (linearGlobalSectionsToUnboundedDerived X R ρ).app K =
      (linearGlobalSectionsComplexFunctor X R ρ ⋙ DerivedCategory.Q).map
        (kInjectiveResolutionUnit X R K) :=
  Category.id_comp _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat] in
/-- On a complex of injectives the `A`-linear augmentation of Tag 08C0 is a
quasi-isomorphism. -/
theorem quasiIso_linearGlobalSectionsToAlternatingCech_of_injective
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (L : CochainComplex (SheafOfModules.{u} R) ℤ) (hL : ∀ n : ℤ, Injective (L.X n)) :
    QuasiIso ((linearGlobalSectionsToAlternatingCech X R ρ U).app L) :=
  (quasiIso_liftNatTrans_app_iff _ _ _ _).mpr
    (quasiIso_globalSectionsToAlternatingCech_of_injective X U hU L hL)

/-- The `A`-linear augmentation of Tag 08C0, followed by passage to `D(A)`. -/
def linearGlobalSectionsToAlternatingCechDerived {I : Type u} (U : I → Opens X) :
    linearGlobalSectionsComplexFunctor X R ρ ⋙ DerivedCategory.Q ⟶
      linearAlternatingCechDerivedFunctor X R ρ U :=
  Functor.whiskerRight (linearGlobalSectionsToAlternatingCech X R ρ U) DerivedCategory.Q

/-- The `A`-linear augmentation of Tag 08C0 on the functorial K-injective resolution, in
`D(A)`. -/
def linearKInjectiveResolutionAlternatingCechMap {I : Type u} (U : I → Opens X) :
    linearUnboundedDerivedGlobalSectionsFunctor X R ρ ⟶
      kInjectiveResolution X R ⋙ linearAlternatingCechDerivedFunctor X R ρ U :=
  Functor.whiskerLeft (kInjectiveResolution X R)
    (linearGlobalSectionsToAlternatingCechDerived X R ρ U)

/-- At a complex `K`, the `A`-linear augmentation on the K-injective resolution is the image in
`D(A)` of the augmentation at the resolution of `K`. -/
theorem linearKInjectiveResolutionAlternatingCechMap_app {I : Type u} (U : I → Opens X)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (linearKInjectiveResolutionAlternatingCechMap X R ρ U).app K =
      DerivedCategory.Q.map
        ((linearGlobalSectionsToAlternatingCech X R ρ U).app ((kInjectiveResolution X R).obj K)) :=
  rfl

/-- For a finite open covering, the `A`-linear augmentation of Tag 08C0 on the functorial
K-injective resolution is an isomorphism in `D(A)`. -/
theorem isIso_linearKInjectiveResolutionAlternatingCechMap
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    IsIso (linearKInjectiveResolutionAlternatingCechMap X R ρ U) := by
  have happ : ∀ K, IsIso ((linearKInjectiveResolutionAlternatingCechMap X R ρ U).app K) :=
    fun K ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := _)).mpr
      (quasiIso_linearGlobalSectionsToAlternatingCech_of_injective X R ρ U hU
        ((kInjectiveResolution X R).obj K) (fun _ ↦ inferInstance))
  exact NatIso.isIso_of_isIso_app _

/-- On the functorial K-injective resolution the `A`-linear augmentation of Tag 08C0 is an
isomorphism in `D(A)`. -/
def linearKInjectiveResolutionAlternatingCechIso
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    linearUnboundedDerivedGlobalSectionsFunctor X R ρ ≅
      kInjectiveResolution X R ⋙ linearAlternatingCechDerivedFunctor X R ρ U :=
  have := isIso_linearKInjectiveResolutionAlternatingCechMap X R ρ U hU
  asIso (linearKInjectiveResolutionAlternatingCechMap X R ρ U)

/-- At a complex `K`, the forward map of `linearKInjectiveResolutionAlternatingCechIso` is the
augmentation, in `D(A)`, at the K-injective resolution of `K`. -/
theorem linearKInjectiveResolutionAlternatingCechIso_hom_app
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (linearKInjectiveResolutionAlternatingCechIso X R ρ U hU).hom.app K =
      (linearGlobalSectionsToAlternatingCechDerived X R ρ U).app
        ((kInjectiveResolution X R).obj K) :=
  rfl

/-- **The comparison map of Tag 08C1 in `D(A)`**, for a finite open covering: the total
alternating Čech complex of the inclusion of `F^•` into its K-injective resolution, followed by
the inverse of the `A`-linear augmentation of Tag 08C0 on the resolution. -/
def linearAlternatingCechToDerivedComparison
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    linearAlternatingCechDerivedFunctor X R ρ U ⟶
      linearUnboundedDerivedGlobalSectionsFunctor X R ρ :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (kInjectiveResolutionInclusion X R)
      (linearAlternatingCechDerivedFunctor X R ρ U) ≫
    (linearKInjectiveResolutionAlternatingCechIso X R ρ U hU).inv

/-- At a complex `K`, the comparison map is the total alternating Čech complex of the inclusion
of `K` into its K-injective resolution, followed by the inverse of the augmentation there. -/
theorem linearAlternatingCechToDerivedComparison_app
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    (linearAlternatingCechToDerivedComparison X R ρ U hU).app K =
      (linearAlternatingCechDerivedFunctor X R ρ U).map (kInjectiveResolutionUnit X R K) ≫
        (linearKInjectiveResolutionAlternatingCechIso X R ρ U hU).inv.app K :=
  Category.id_comp _

/-- **Compatibility with Tag 08C0, `A`-linearly.** After the augmentation of Tag 08C0 the
comparison map is the canonical map from global sections to derived global sections. -/
theorem linearGlobalSectionsToAlternatingCechDerived_comp_linearAlternatingCechToDerivedComparison
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U) :
    linearGlobalSectionsToAlternatingCechDerived X R ρ U ≫
        linearAlternatingCechToDerivedComparison X R ρ U hU =
      linearGlobalSectionsToUnboundedDerived X R ρ := by
  ext K
  rw [NatTrans.comp_app, linearAlternatingCechToDerivedComparison_app,
    linearGlobalSectionsToUnboundedDerived_app, ← Category.assoc,
    ← (linearGlobalSectionsToAlternatingCechDerived X R ρ U).naturality
      (kInjectiveResolutionUnit X R K), Category.assoc,
    ← linearKInjectiveResolutionAlternatingCechIso_hom_app X R ρ U hU, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- **The comparison in `D(A)` is invertible exactly when the comparison of Tag 08C1 in
`D(Ab)` is.** -/
theorem isIso_linearAlternatingCechToDerivedComparison_app_iff
    {I : Type u} [Finite I] (U : I → Opens X) (hU : (⊤ : Opens X) = iSup U)
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    IsIso ((linearAlternatingCechToDerivedComparison X R ρ U hU).app K) ↔
      IsIso ((alternatingCechToDerivedComparison X R U hU).app K) := by
  rw [linearAlternatingCechToDerivedComparison_app, alternatingCechToDerivedComparison_app,
    isIso_comp_right_iff, isIso_comp_right_iff]
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso
      (φ := (linearAlternatingCechTotalComplexFunctor X R ρ U).map
        (kInjectiveResolutionUnit X R K))).trans
    ((quasiIso_liftFunctor_map_iff _ _ _).trans
      (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := _)).symm)

end

end Stacks.Cech

end
