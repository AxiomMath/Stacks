module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.RelativePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointTensorPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeAffineTargetPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Relative dualizing complexes of algebraic spaces

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation. Over an
affine `Y`, with `a` the right adjoint of `Rf_*` on `D_QCoh` (Stacks 0E55), `a(𝒪_Y)` is
`Y`-perfect (Stacks 0E5V (1)): `Rf_*(E ⊗^L a(𝒪_Y)) ≅ (Rf_* E^∨)^∨` is perfect for every perfect
`E`, and Stacks 0GFL applies after reading `f` over `Spec Γ(Y, 𝒪_Y)`. From this follow Stacks
0E5V (3), Stacks 0E5Y, Stacks 0E5Z and Stacks 0E60.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isPerfectRelativeToCanonical_affineRightAdjoint`: Stacks 0E5V (1).
* `isIso_smallEtaleDerivedHomothety_affineRightAdjoint`: Stacks 0E5V (3).
* `RelativeDualizingComplex.ofIsAffine`: existence over an affine base.
* `RelativeDualizingComplex.isIso_smallEtaleDerivedHomothety_and_isLE`: Stacks 0E5Y.
* `RelativeDualizingComplex.existsUnique_iso_of_relativeDualizingComplex`: Stacks 0E5Z.
* `RelativeDualizingPair.isAffineBaseChangePair_of_isEtaleCovering_of_isProper`: Stacks 0E60.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  sheafTensor_additive_inverseImageRingedSite_over
  sheafTensor_obj_additive_inverseImageRingedSite_over
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0E5V (1).** For `Y` affine and `f : X ⟶ Y` proper, flat and of finite
presentation, with `a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, the object
`a(𝒪_Y)` of `D(𝒪_X)` is `Y`-perfect. -/
@[stacks 0E5V "(1)"]
theorem isPerfectRelativeToCanonical_affineRightAdjoint {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hY : IsAffineSpace B S hS Y.1) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hfp.1
      ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj := by
  obtain ⟨A, _, hA, g, eY, XA, e, he⟩ := exists_relocalizeSpec_of_isAffineSpace f hY
  let K := ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj
  have hK : QcohDerived B S hS X K :=
    ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).property
  let rb := relocalizeBaseHom B hA hS g
  have : IsIso rb.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map rb))
  have : IsIso eY.hom.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map eY.hom))
  have : IsIso e.inv.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map e.inv))
  -- the properties of `f` read over `Spec A`
  have hflF : IsFlat B S hS (f ≫ eY.hom).hom :=
    (Space.holdsOnEveryEtaleChart_comp_iso_iff B S hS _ f.hom eY.hom.hom).2 hfl
  have hfpF : IsFinitePresentation B S hS (f ≫ eY.hom).hom :=
    isFinitePresentation_of_arrowIso B S hS f.hom (f ≫ eY.hom).hom (𝟙 _) eY.hom.hom
      (Category.id_comp _) hfp
  have hflT := (isFlat_iff_of_relocalizeSpace_iso e he).1 hflF
  have hfpT := (isFinitePresentation_iff_of_relocalizeSpace_iso e he).1 hfpF
  have w₀ : e.inv ≫ relocalizeHom B hA hS g (toFinalHom B hA XA) ≫ rb = f ≫ eY.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  have w : e.inv.hom ≫ (relocalizeHom B hA hS g (toFinalHom B hA XA)).hom =
      f.hom ≫ eY.hom.hom ≫ inv rb.hom := by
    have : Mono rb.hom := IsIso.mono_of_iso _
    rw [← cancel_mono rb.hom, Category.assoc, Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact congrArg (fun φ => φ.hom) w₀
  have hsepT : IsSeparated B _ hA (toFinalHom B hA XA).hom :=
    isSeparated_of_relocalize B _ hA hS g
      (relativelyRepresentable_pullbackDiagonal B _ hA (toFinalHom B hA XA).hom XA.2)
      (isSeparated_of_arrowIso B S hS f.hom _ e.inv.hom (eY.hom.hom ≫ inv rb.hom) w hf.1)
  rw [← DerivedChow.toBase_eq_toFinalHom] at hflT hfpT hsepT
  -- the object of `D(𝒪_{X_A})` corresponding to `a(𝒪_Y)`
  let ρ := relocalizeDerivedEquivalence B hA hS g XA.1 XA.2
  have hQ : QcohDerived B _ hA XA
      (ρ.inverse.obj ((smallEtaleDerivedModulePullback B S hS e.hom).obj K)) :=
    (qcohDerived_relocalizeDerivedFunctor_obj_iff B hA hS g XA.2 _).1
      ((QcohDerived B S hS _).prop_of_iso (ρ.counitIso.app _).symm
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ e.hom K hK))
  have hh := isPerfect_derivedSections_tensor_relocalize he K
    (isPerfect_derivedModulePushforward_tensor_rightAdjoint hZ f
      (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY.isQuasiCompactSpace hf hfl hfp)
  exact isPerfectRelativeToCanonical_of_relocalizeSpec he hfl hfp.1 K hK hflT hfpT.1
    (isPerfectRelativeToCanonical_of_isPerfect_derivedSections_tensor B hA hsepT hfpT hflT _ hQ hh)

/-- **Stacks 0E5V (3).** For `Y` affine and `f : X ⟶ Y` proper, flat and of finite
presentation, with `a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, the map
`𝒪_X ⟶ R𝓗om(a(𝒪_Y), a(𝒪_Y))` is an isomorphism. -/
@[stacks 0E5V "(3)"]
theorem isIso_smallEtaleDerivedHomothety_affineRightAdjoint {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hY : IsAffineSpace B S hS Y.1) :
    IsIso (smallEtaleDerivedHomothety B S hS X
      ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :=
  isIso_smallEtaleDerivedHomothety_affineRightAdjoint_of_isPerfectRelativeTo hZ f hf hfl hfp hY
    (isPerfectRelativeToCanonical_affineRightAdjoint hZ f hf hfl hfp hY)

/-- **The relative dualizing complex over an affine base** (the discussion after Stacks 0E5X):
for `Y` affine and `f : X ⟶ Y` proper, flat and of finite presentation, `(a(𝒪_Y), Tr)` is a
relative dualizing complex. -/
def RelativeDualizingComplex.ofIsAffine {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hY : IsAffineSpace B S hS Y.1) :
    RelativeDualizingComplex hZ f hf hfl hfp :=
  RelativeDualizingComplex.ofIsAffineSpace hZ f hf hfl hfp hY
    (isPerfectRelativeToCanonical_affineRightAdjoint hZ f hf hfl hfp hY)

/-- The hypothesis of the reduction lemmas: every affine base change of `f` has `a(𝒪_{Y'})`
perfect relative to `Y'`. -/
private theorem isPerfectRelativeToCanonical_affineBaseChange {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) :
    ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
        ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
        ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp).1
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj :=
  fun _ _ f' _ _ sq hY' =>
    isPerfectRelativeToCanonical_affineRightAdjoint hZ f'
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp) hY'

namespace RelativeDualizingComplex

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {hf : IsProper B S hS f.hom}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}

/-- **Stacks 0E5Y.** Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite
presentation. For a relative dualizing complex `(ω, τ)`, the map `𝒪_X ⟶ R𝓗om(ω, ω)` is an
isomorphism and `Rf_* ω` has vanishing cohomology sheaves in positive degrees. -/
@[stacks 0E5Y]
theorem isIso_smallEtaleDerivedHomothety_and_isLE (ω : RelativeDualizingComplex hZ f hf hfl hfp) :
    IsIso (smallEtaleDerivedHomothety B S hS X ω.ω) ∧
      ((derivedModulePushforward B S hS f).obj ω.ω).IsLE 0 :=
  ω.isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo
    (isPerfectRelativeToCanonical_affineBaseChange hZ hf hfl hfp)

/-- **Stacks 0E5Z.** Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite
presentation. Two relative dualizing complexes `(ω₁, τ₁)`, `(ω₂, τ₂)` on `X/Y` have a unique
isomorphism of pairs: a unique `e : ω₁ ≅ ω₂` with `τ₂ ∘ Rf_* e = τ₁`. -/
@[stacks 0E5Z]
theorem existsUnique_iso_of_relativeDualizingComplex
    (D₁ D₂ : RelativeDualizingComplex hZ f hf hfl hfp) :
    ∃! e : D₁.ω ≅ D₂.ω, (derivedModulePushforward B S hS f).map e.hom ≫ D₂.τ = D₁.τ :=
  existsUnique_iso_of_isPerfectRelativeTo D₁ D₂
    (isPerfectRelativeToCanonical_affineBaseChange hZ hf hfl hfp)

end RelativeDualizingComplex

namespace RelativeDualizingPair

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}

/-- **Stacks 0E60.** Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite
presentation, `(ω, τ)` a pair of a `Y`-perfect object of `D(𝒪_X)` and a map
`τ : Rf_* ω ⟶ 𝒪_Y`, and `X_i ⟶ Y_i` the base changes of `f` to the members of an étale covering
`{Y_i ⟶ Y}` by affines, over which `(ω, τ)` is isomorphic to `(a_i(𝒪_{Y_i}), Tr)`. Then
`(ω, τ)` is a relative dualizing complex: its base change to every affine `Y'` is isomorphic to
`(a'(𝒪_{Y'}), Tr)`. -/
@[stacks 0E60]
theorem isAffineBaseChangePair_of_isEtaleCovering_of_isProper
    (P : RelativeDualizingPair f hfl hfp) (hf : IsProper B S hS f.hom)
    {ι : Type v} {Yi Xi : ι → AlgebraicSpaces B S hS} {fi : ∀ i, Xi i ⟶ Yi i}
    {gi : ∀ i, Yi i ⟶ Y} {g'i : ∀ i, Xi i ⟶ X} (sqi : ∀ i, IsPullback (g'i i) (fi i) f (gi i))
    (hYi : ∀ i, IsAffineSpace B S hS (Yi i).1)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (gi i).hom))
    (hi : ∀ i, IsAffineBaseChangePair hZ (sqi i) hfp (hYi i) P.ω P.τ)
    ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1) :
    IsAffineBaseChangePair hZ sq hfp hY' P.ω P.τ :=
  P.isAffineBaseChangePair_of_isEtaleCovering_of_isPerfectRelativeTo hf
    (isPerfectRelativeToCanonical_affineBaseChange hZ hf hfl hfp)
    sqi hYi hcov hi f' g g' sq hY'

end RelativeDualizingPair

end AlgebraicGeometry.Space

end
