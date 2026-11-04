module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRelativeDualizingAffineBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRelativeDualizingHomothetyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexLocal

/-!
# Relative dualizing complexes from the `Y'`-perfectness of `a'(𝒪_{Y'})`

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation. Over an
affine `Y'` with base change `f' : X' ⟶ Y'` and right adjoint `a'` of `Rf'_*` (Stacks 0E55),
Stacks 0E5V (1) says that `a'(𝒪_{Y'})` is `Y'`-perfect. This file derives from that single input
Stacks 0E5V (3), Stacks 0E5Y, Stacks 0E5Z and Stacks 0E60, by the arguments of the source:

* 0E5V (3): `a'(𝒪_{Y'})` is pseudo-coherent, so `R𝓗om(a'(𝒪_{Y'}), a'(𝒪_{Y'}))` is quasi-coherent
  and the homothety map is invertible;
* 0E5Y: étale locally on `Y` a relative dualizing complex is `a'(𝒪_{Y'})`, with Stacks 0E5V (2);
* 0E5Z: the local isomorphisms of pairs glue, by Stacks 0E5Y;
* 0E60: `(a'(𝒪_{Y'}), Tr)` is a relative dualizing complex over every affine `Y'`.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isIso_smallEtaleDerivedHomothety_affineRightAdjoint_of_isPerfectRelativeTo`: Stacks 0E5V (3).
* `RelativeDualizingComplex.isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo`:
  Stacks 0E5Y.
* `RelativeDualizingComplex.existsUnique_iso_of_isPerfectRelativeTo`: Stacks 0E5Z.
* `RelativeDualizingPair.isAffineBaseChangePair_of_isEtaleCovering_of_isPerfectRelativeTo`:
  Stacks 0E60.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

-- No global `HasDerivedCategory` instance applies to the categories of modules here: the global
-- `SheafOfModules.hasDerivedCategory` needs a `SmallCategory`, and small étale sites are not.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

/-- **Stacks 0E5V (3), granted Stacks 0E5V (1).** For `Y` affine and `f : X ⟶ Y` proper, flat
and of finite presentation, if `a(𝒪_Y)` is `Y`-perfect then `𝒪_X ⟶ R𝓗om(a(𝒪_Y), a(𝒪_Y))` is an
isomorphism. -/
theorem isIso_smallEtaleDerivedHomothety_affineRightAdjoint_of_isPerfectRelativeTo
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (hperf : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hfp.1
      ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :
    IsIso (smallEtaleDerivedHomothety B S hS X
      ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :=
  isIso_smallEtaleDerivedHomothety_rightAdjoint_of_isPseudoCoherent hZ f
    (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY.isQuasiCompactSpace hf hfl hfp
    hperf.1

/-- Properness, flatness and finite presentation are stable under base change. -/
private theorem isProper_and_isFlat_and_isFinitePresentation_of_isPullback
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) :
    IsProper B S hS f'.hom ∧ IsFlat B S hS f'.hom ∧ IsFinitePresentation B S hS f'.hom :=
  ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf,
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl,
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp⟩

namespace RelativeDualizingComplex

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {hf : IsProper B S hS f.hom}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}

/-- **Stacks 0E5Y, granted Stacks 0E5V (1) over every affine base change.** If `a'(𝒪_{Y'})` is
`Y'`-perfect for the base change `f'` of `f` to every affine `Y'`, then for a relative dualizing
complex `(ω, τ)` the map `𝒪_X ⟶ R𝓗om(ω, ω)` is an isomorphism and `Rf_* ω` has vanishing
cohomology sheaves in positive degrees. -/
theorem isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo
    (ω : RelativeDualizingComplex hZ f hf hfl hfp)
    (hperf : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
        ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
        ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp).1
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj) :
    IsIso (smallEtaleDerivedHomothety B S hS X ω.ω) ∧
      ((derivedModulePushforward B S hS f).obj ω.ω).IsLE 0 :=
  ⟨ω.isIso_smallEtaleDerivedHomothety_of_affine fun _ _ f' g g' sq hY' =>
      let h := isProper_and_isFlat_and_isFinitePresentation_of_isPullback sq hf hfl hfp
      isIso_smallEtaleDerivedHomothety_affineRightAdjoint_of_isPerfectRelativeTo hZ f'
        h.1 h.2.1 h.2.2 hY' (hperf f' g g' sq hY'),
    ω.isLE_derivedModulePushforward_of_affine fun _ _ f' _ _ sq hY' =>
      let h := isProper_and_isFlat_and_isFinitePresentation_of_isPullback sq hf hfl hfp
      isLE_derivedModulePushforward_affineRightAdjoint hZ f' h.1 h.2.1 h.2.2 hY'⟩

/-- **Stacks 0E5Z, granted Stacks 0E5V (1) over every affine base change.** Two relative
dualizing complexes `(ω₁, τ₁)`, `(ω₂, τ₂)` on `X/Y` have a unique isomorphism of pairs: a unique
`e : ω₁ ≅ ω₂` with `τ₂ ∘ Rf_* e = τ₁`. -/
theorem existsUnique_iso_of_isPerfectRelativeTo (D₁ D₂ : RelativeDualizingComplex hZ f hf hfl hfp)
    (hperf : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
        ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
        ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp).1
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj) :
    ∃! e : D₁.ω ≅ D₂.ω, (derivedModulePushforward B S hS f).map e.hom ≫ D₂.τ = D₁.τ :=
  existsUnique_iso_of_isIso_homothety D₁ D₂
    (D₁.isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo hperf).1
    (D₂.isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo hperf).1
    (D₁.isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo hperf).2
    (D₂.isIso_smallEtaleDerivedHomothety_and_isLE_of_isPerfectRelativeTo hperf).2

end RelativeDualizingComplex

namespace RelativeDualizingPair

variable {hZ} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {hfl : IsFlat B S hS f.hom} {hfp : IsFinitePresentation B S hS f.hom}

/-- **Stacks 0E60, granted Stacks 0E5V (1) over every affine base change.** Let `(ω, τ)` be a
pair of a `Y`-perfect object of `D(𝒪_X)` and a map `τ : Rf_* ω ⟶ 𝒪_Y`, and let `X_i ⟶ Y_i` be
base changes of `f` to the members of an étale covering `{Y_i ⟶ Y}` by affines over which
`(ω, τ)` is isomorphic to `(a_i(𝒪_{Y_i}), Tr)`. Then the base change of `(ω, τ)` to every affine
`Y'` is isomorphic to `(a'(𝒪_{Y'}), Tr)`, i.e. `(ω, τ)` is a relative dualizing complex. -/
theorem isAffineBaseChangePair_of_isEtaleCovering_of_isPerfectRelativeTo
    (P : RelativeDualizingPair f hfl hfp) (hf : IsProper B S hS f.hom)
    (hperf : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
      IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
        ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
        ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp).1
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj)
    {ι : Type v} {Yi Xi : ι → AlgebraicSpaces B S hS} {fi : ∀ i, Xi i ⟶ Yi i}
    {gi : ∀ i, Yi i ⟶ Y} {g'i : ∀ i, Xi i ⟶ X} (sqi : ∀ i, IsPullback (g'i i) (fi i) f (gi i))
    (hYi : ∀ i, IsAffineSpace B S hS (Yi i).1)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (gi i).hom))
    (hi : ∀ i, IsAffineBaseChangePair hZ (sqi i) hfp (hYi i) P.ω P.τ)
    ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1) :
    IsAffineBaseChangePair hZ sq hfp hY' P.ω P.τ :=
  P.isAffineBaseChangePair_of_isEtaleCovering hf (fun _ _ f' g g' sq hY' =>
    let h := isProper_and_isFlat_and_isFinitePresentation_of_isPullback sq hf hfl hfp
    ⟨RelativeDualizingComplex.ofIsAffineSpace hZ f' h.1 h.2.1 h.2.2 hY' (hperf f' g g' sq hY'),
      Iso.refl _, (congrArg (· ≫ affineBaseChangeTrace hZ sq hfp hY')
        ((derivedModulePushforward B S hS f').map_id _)).trans (Category.id_comp _)⟩)
    sqi hYi hcov hi f' g g' sq hY'

end RelativeDualizingPair

end AlgebraicGeometry.Space

end
