module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPerfectPseudoCoherentTransport

/-!
# `ε^*` carries pseudo-coherence from a scheme to the algebraic space it represents

Let `U` be an object of the big fppf site over `S` with scheme `T`, and let `h_U` be the
algebraic space it represents.  This file proves that `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})` carries an
`m`-pseudo-coherent object (ringed-space pseudo-coherence, Stacks 08CB) to an `m`-pseudo-coherent
object of the small étale ringed site of `h_U` (Stacks 08FT): this is Stacks 08HE, clause
(1) ⇒ (2), read on the represented algebraic space, and the companion of
`AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule` and of
`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_representedDerivedAssociatedModule`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedModulePushforward`: an
  `m`-pseudo-coherent object on the small étale site of `T` is carried to an
  `m`-pseudo-coherent object on the small étale site of `h_U`.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_representedDerivedAssociatedModule`: `ε^*` of an
  `m`-pseudo-coherent object is `m`-pseudo-coherent.

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-- **`m`-pseudo-coherence is carried from the small étale site of `T` to that of `h_U`.** -/
theorem isPseudoCoherentFrom_representedModulePushforward
    (P : DerivedCategory (SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)))
    (m : ℤ)
    (hP : (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).IsPseudoCoherentFrom P m) :
    (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom
      ((representedModulePushforward B S hS U).mapDerivedCategory.obj P) m :=
  RingedSite.isPseudoCoherentFrom_pushforward_of_siteEquivalence
    (X := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (Y := _root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleEquivalence B S hS U).symm
    (hFc := isContinuous_representedSmallEtaleEquivalence_inverse B S hS U)
    (hIc := isContinuous_representedSmallEtaleEquivalence_functor B S hS U)
    (representedStructureMapInverse B S hS U) (representedStructureMap B S hS U)
    (representedStructureMap_symm_counit_whiskerRight B S hS U)
    (representedStructureMap_symm_unit_whiskerRight B S hS U)
    (hψ := isIso_representedStructureMap B S hS U) P m hP

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

/-- **`ε^*` of an `m`-pseudo-coherent object is `m`-pseudo-coherent** (Stacks 08HE, clause
(1) ⇒ (2), read on the represented algebraic space). -/
theorem isPseudoCoherentFrom_representedDerivedAssociatedModule
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules) (m : ℤ)
    (hE₀ : RingedSpace.IsPseudoCoherentFrom
      (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E₀ m) :
    (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).IsPseudoCoherentFrom
      ((representedDerivedAssociatedModule B S hS U).obj E₀) m := by
  have h₁ := RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite
    ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace E₀ m hE₀
  have h₂ := SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property E₀ m h₁
  obtain ⟨K, hK, ⟨e⟩⟩ := isPseudoCoherentFrom_representedModulePushforward B S hS U _ m h₂
  exact ⟨K, hK, ⟨e ≪≫ (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
    (SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedModulePushforward B S hS U)).app E₀⟩⟩

end AlgebraicGeometry.Space

end
