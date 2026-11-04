module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedZariskiLocalTorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedZariskiPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InverseImageSliceTensor

/-!
# Relative perfectness across `ε` for a morphism of representable algebraic spaces

Let `g : T ⟶ T'` be a morphism of the big fppf site over `S` whose underlying morphism of schemes
`g₀ : X_0 ⟶ Y_0` is flat and locally of finite presentation. An object `E` of `D(𝒪_{X_0})` is
`Y_0`-perfect (Stacks 0DI0) exactly when `Lε^* E` is `yoneda.obj T'`-perfect (Stacks 0DKN) along
the represented morphism.

## Main results

* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_representedZariskiDerivedPullback_iff`:
  `Lε^* E` is perfect relative to `yoneda.obj T'` if and only if `E` is `Y_0`-perfect.
-/
@[expose] public noncomputable section

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

attribute [local instance] AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (g : T ⟶ T')

/-- For `g₀ : X_0 ⟶ Y_0` flat and locally of finite presentation, `E ∈ D(𝒪_{X_0})` is
`Y_0`-perfect exactly when `Lε^* E` is perfect relative to `yoneda.obj T'` along the represented
morphism. -/
theorem isPerfectRelativeToCanonical_representedZariskiDerivedPullback_iff
    [Flat ((BigFppfOver.toScheme B S hS).map g)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)]
    (hfl : IsFlat B S hS (representedSpaceMap B S hS g).hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS (representedSpaceMap B S hS g).hom)
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS (representedSpaceMap B S hS g) hfl hlfp
        ((representedZariskiDerivedPullback B S hS T).obj E) ↔
      ((BigFppfOver.toScheme B S hS).map g).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u}
          (RingedSpace.inverseImage
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T').toRingedSpace
            ((BigFppfOver.toScheme B S hS).map g).base)) E :=
  and_congr (isPseudoCoherent_representedZariskiDerivedPullback_iff T E)
    ((locallyHasFiniteTorDimension_derivedScalarRestriction_iff_representedZariskiDerivedPullback g
      (canonicalSliceDerivedTensorProduct B S hS (representedSpaceMap B S hS g)) E).symm.trans
      (RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff.{u + 1, u + 1, u}
        _ _).symm)

end AlgebraicGeometry.Space

end
