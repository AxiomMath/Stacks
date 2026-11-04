module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SiteEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSchemeModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ChartModel
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentSpellings
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectForward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparisonConverse
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealSheafKernel

/-!
# Perfectness and pseudo-coherence on a represented algebraic space and on its scheme

Let `U` be an object of the big fppf site over `S` with underlying scheme `T`, and let
`h_U = yoneda.obj U` be the algebraic space it represents.  The small étale site of `h_U` and the
small étale site of `T` are equivalent, with structure sheaves matching on the nose
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`,
`AlgebraicGeometry.Space.representedModuleEquivalence`). The two transports of modules along
that equivalence preserve perfectness and `m`-pseudo-coherence, and the comparison `ε^*` from
modules on `T` carries perfect objects to perfect objects and reflects `m`-pseudo-coherence.

## Main results

* `AlgebraicGeometry.Space.isPerfect_representedModulePushforward`: a perfect object on the small
  étale site of `T` is carried to a perfect object on the small étale site of `h_U`.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedModuleRestriction`: an
  `m`-pseudo-coherent object on the small étale site of `h_U` is carried to an
  `m`-pseudo-coherent object on the small étale site of `T`.
* `AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule`: `ε^*` of a perfect
  object is perfect.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_representedDerivedAssociatedModule`: if
  `ε^*E₀` is `m`-pseudo-coherent then so is `E₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The first coherence identity for the inverse equivalence of small étale sites. -/
theorem representedStructureMap_symm_counit_whiskerRight :
    Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS U).symm.counit)
        (ringStructureSheaf B S hS (yoneda.obj U)).obj =
      (representedStructureMap B S hS U).hom ≫
        (representedSmallEtaleEquivalence B S hS U).symm.inverse.op.whiskerLeft
          (representedStructureMapInverse B S hS U).hom := by
  ext : 2
  rfl

/-- The second coherence identity for the inverse equivalence of small étale sites. -/
theorem representedStructureMap_symm_unit_whiskerRight :
    (representedStructureMapInverse B S hS U).hom ≫
        (representedSmallEtaleEquivalence B S hS U).symm.functor.op.whiskerLeft
          (representedStructureMap B S hS U).hom ≫
        Functor.whiskerRight (NatTrans.op (representedSmallEtaleEquivalence B S hS U).symm.unit)
          (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj =
      𝟙 (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj := by
  ext : 2
  rfl

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- The transport of modules from the small étale site of `T` to that of `h_U` is right exact,
being the functor of an equivalence. -/
instance preservesFiniteColimits_representedModulePushforward :
    PreservesFiniteColimits (representedModulePushforward B S hS U) :=
  inferInstanceAs (PreservesFiniteColimits (representedModuleEquivalence.{u, u} B S hS U).functor)

/-- The transport of modules from the small étale site of `h_U` to that of `T` is exact, being
the inverse of an equivalence. -/
instance preservesFiniteLimits_representedModuleRestriction :
    PreservesFiniteLimits (representedModuleRestriction B S hS U) :=
  inferInstanceAs (PreservesFiniteLimits (representedModuleEquivalence.{u, u} B S hS U).inverse)

/-- The transport of modules from the small étale site of `h_U` to that of `T` is right exact,
being the inverse of an equivalence. -/
instance preservesFiniteColimits_representedModuleRestriction :
    PreservesFiniteColimits (representedModuleRestriction B S hS U) :=
  inferInstanceAs (PreservesFiniteColimits (representedModuleEquivalence.{u, u} B S hS U).inverse)

/-- The inverse comparison of structure sheaves is invertible, being the identity. -/
instance isIso_representedStructureMapInverse :
    IsIso (representedStructureMapInverse B S hS U) := by
  rw [← ObjectProperty.isIso_hom_iff]
  exact IsIso.id _

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-- **Perfectness is carried from the small étale site of `T` to that of `h_U`.** -/
theorem isPerfect_representedModulePushforward
    (P : DerivedCategory (SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)))
    (hP : (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).IsPerfect P) :
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      ((representedModulePushforward B S hS U).mapDerivedCategory.obj P) :=
  RingedSite.isPerfect_pushforward_of_siteEquivalence
    (X := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (Y := _root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleEquivalence B S hS U).symm
    (hFc := isContinuous_representedSmallEtaleEquivalence_inverse B S hS U)
    (hIc := isContinuous_representedSmallEtaleEquivalence_functor B S hS U)
    (representedStructureMapInverse B S hS U) (representedStructureMap B S hS U)
    (representedStructureMap_symm_counit_whiskerRight B S hS U)
    (representedStructureMap_symm_unit_whiskerRight B S hS U)
    (hψ := isIso_representedStructureMap B S hS U) P hP

/-- **`m`-pseudo-coherence is carried from the small étale site of `h_U` to that of `T`.** -/
theorem isPseudoCoherentFrom_representedModuleRestriction
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom E m) :
    (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).IsPseudoCoherentFrom
      ((representedModuleRestriction B S hS U).mapDerivedCategory.obj E) m :=
  RingedSite.isPseudoCoherentFrom_pushforward_of_siteEquivalence
    (Y := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (X := _root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleEquivalence B S hS U)
    (hFc := isContinuous_representedSmallEtaleEquivalence_functor B S hS U)
    (hIc := isContinuous_representedSmallEtaleEquivalence_inverse B S hS U)
    (representedStructureMap B S hS U) (representedStructureMapInverse B S hS U)
    (representedStructureMap_counit_whiskerRight B S hS U)
    (representedStructureMap_unit_whiskerRight B S hS U)
    (hψ := isIso_representedStructureMapInverse B S hS U) E m hE

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

/-- The functor of the equivalence of module categories of the two small étale sites is
additive: it is `AlgebraicGeometry.Space.representedModulePushforward`. -/
local instance additive_representedModuleEquivalence_functor :
    (representedModuleEquivalence.{u, u} B S hS U).functor.Additive :=
  inferInstanceAs (representedModulePushforward B S hS U).Additive

/-! ### Pseudo-coherence on the Zariski site of a scheme -/

/-- Pseudo-coherence on the small Zariski ringed site of a scheme is ringed-space
pseudo-coherence. -/
theorem isPseudoCoherentFrom_toRingedSpace_of_zariskiRingedSite (X : Scheme.{u})
    (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ)
    (h : X.zariskiRingedSite.IsPseudoCoherentFrom E m) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m :=
  RingedSpace.PseudoCoherence.isPseudoCoherentFrom_of_ringedSite X.toRingedSpace E m h

/-! ### The comparison `ε^*` and the three properties -/

/-- **`ε^*` of a perfect object is perfect.** -/
theorem isPerfect_representedDerivedAssociatedModule
    (P₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hP₀ : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) P₀) :
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      ((representedDerivedAssociatedModule B S hS U).obj P₀) := by
  have h₁ := Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect
    ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace P₀ hP₀
  have h₂ := SmallEtale.perfectToAssociatedModule_of_slice_exact (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property P₀ h₁
  obtain ⟨K, hK, ⟨e⟩⟩ := isPerfect_representedModulePushforward B S hS U _ h₂
  exact ⟨K, hK, ⟨e ≪≫ (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
    (SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedModulePushforward B S hS U)).app P₀⟩⟩

/-- **Pseudo-coherence descends along `ε^*`**: if `ε^*E₀` is `m`-pseudo-coherent then so is
`E₀`. -/
theorem isPseudoCoherentFrom_of_representedDerivedAssociatedModule
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules) (m : ℤ)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom
        ((representedDerivedAssociatedModule B S hS U).obj E₀) m) :
    RingedSpace.IsPseudoCoherentFrom
      (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E₀ m := by
  obtain ⟨K, hK, ⟨f⟩⟩ := isPseudoCoherentFrom_representedModuleRestriction B S hS U _ m h
  have e : (representedModuleRestriction B S hS U).mapDerivedCategory.obj
      ((representedDerivedAssociatedModule B S hS U).obj E₀) ≅
      (SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapDerivedCategory.obj E₀ :=
    (representedModuleRestriction B S hS U).mapDerivedCategory.mapIso
      ((Stacks.DerivedGlueing.mapDerivedCategoryCompIso
        (SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
        (representedModulePushforward B S hS U)).app E₀).symm ≪≫
    ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
      (representedModuleEquivalence.{u, u} B S hS U)).unitIso.app _).symm
  have h₂ : SmallEtale.IsPseudoCoherentFromSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property E₀ m := ⟨K, hK, ⟨f.trans e⟩⟩
  exact isPseudoCoherentFrom_toRingedSpace_of_zariskiRingedSite _ E₀ m
    (SmallEtale.associatedModuleToPseudoCoherent (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property E₀ m h₂)

end AlgebraicGeometry.Space

end
