module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InverseImageSliceTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
import StacksCore.Tactic.StacksAttribute

/-!
# Relative dualizing complexes for proper flat morphisms of algebraic spaces

Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces of finite presentation. A relative
dualizing complex for `X/Y` is a `Y`-perfect object `ω` of `D(𝒪_X)` with a map
`τ : Rf_* ω ⟶ 𝒪_Y` whose base change to every affine `Y'` is the pair `(a'(𝒪_{Y'}), Tr)` of the
right adjoint `a'` of `Rf'_*` and its trace map (Stacks 0E5X).

## Main definitions

* `AlgebraicGeometry.Space.RelativeDualizingPair`: the underlying pair `(ω, τ)`.
* `AlgebraicGeometry.Space.RelativeDualizingComplex`: a relative dualizing complex for `X/Y`.
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (hfp : IsFinitePresentation B S hS f.hom)
  (hY' : IsAffineSpace B S hS Y'.1)

include sq hfp in
/-- The base change of a morphism of finite presentation is quasi-compact. -/
theorem isQuasiCompact_of_isPullback_of_isFinitePresentation : IsQuasiCompact B S hS f'.hom :=
  IsQuasiCompact.of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hfp.2.1

include sq hfp in
/-- The base change of a morphism of finite presentation is quasi-separated. -/
theorem isQuasiSeparated_of_isPullback_of_isFinitePresentation :
    IsQuasiSeparated B S hS f'.hom :=
  isQuasiSeparated_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hfp.2.2

/-- The right adjoint `a'` of `Rf'_* : D_QCoh(𝒪_{X'}) ⥤ D_QCoh(𝒪_{Y'})` for the base change
`f' : X' ⟶ Y'` of a morphism of finite presentation to an affine algebraic space (Stacks 0E55). -/
abbrev affineBaseChangeRightAdjoint :
    QuasicoherentDerivedCategory.{u, u} B S hS Y'.1 Y'.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2 :=
  quasicoherentDerivedRightAdjoint hZ f'
    (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS
        f'.hom hY' (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp))
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS
        hZ
        f'.hom
        (CategoryTheory.ObjectProperty.FullSubcategory.property _)
        hY'
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp))
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')

/-- The trace map `Tr_{f', 𝒪_{Y'}} : Rf'_* a'(𝒪_{Y'}) ⟶ 𝒪_{Y'}` in `D(𝒪_{Y'})` (Stacks 0E5K):
the counit of `Rf'_* ⊣ a'` at the structure sheaf. -/
def affineBaseChangeTrace :
    (derivedModulePushforward B S hS f').obj
        ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
          (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj ⟶
      (derivedStructureSheaf B S hS Y'.1 Y'.2).obj :=
  ((quasicoherentDerivedRightAdjointAdjunction hZ f'
    (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS
        f'.hom hY' (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp))
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS
        hZ
        f'.hom
        (CategoryTheory.ObjectProperty.FullSubcategory.property _)
        hY'
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp))
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
    (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp)
    (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp)).counit.app
      (derivedStructureSheaf B S hS Y'.1 Y'.2)).hom

/-- A pair `(ω, τ)` with `τ : Rf_* ω ⟶ 𝒪_Y`, pulled back along the cartesian square, is isomorphic
to the pair `(a'(𝒪_{Y'}), Tr_{f', 𝒪_{Y'}})`: there is an isomorphism `e : L(g')^* ω ≅ a'(𝒪_{Y'})`
under which `Lg^* τ`, read through the base change map `Lg^* Rf_* ω ⟶ Rf'_* L(g')^* ω` of
Stacks 07A7, is the trace map. -/
def IsAffineBaseChangePair (ω : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (τ : (derivedModulePushforward B S hS f).obj ω ⟶ (derivedStructureSheaf B S hS Y.1 Y.2).obj) :
    Prop :=
  ∃ e : (smallEtaleDerivedModulePullback B S hS g').obj ω ≅
      ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
        (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj,
    (smallEtaleDerivedModulePullback B S hS g).map τ ≫
        (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom =
      smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w ω ≫
        (derivedModulePushforward B S hS f').map e.hom ≫ affineBaseChangeTrace hZ sq hfp hY'

/-- The adjunction `Rf'_* ⊣ a'` whose counit defines `affineBaseChangeTrace`. -/
private abbrev affineBaseChangeAdjunction :=
  quasicoherentDerivedRightAdjointAdjunction hZ f'
    (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS
        f'.hom hY' (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp))
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS
        hZ
        f'.hom
        (CategoryTheory.ObjectProperty.FullSubcategory.property _)
        hY'
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp))
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
    (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp)
    (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp)

/-- **Maps into `a'(𝒪_{Y'})` are determined by their composite with the trace** (the second
remark after Stacks 0E5X): for `M` in `D_QCoh(𝒪_{X'})`, `φ ↦ Tr ∘ Rf'_* φ` is injective on
`Hom(M, a'(𝒪_{Y'}))`. -/
theorem affineBaseChangeTrace_comp_injective
    (M : QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2)
    {φ ψ : M.obj ⟶ ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
      (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj}
    (h : (derivedModulePushforward B S hS f').map φ ≫ affineBaseChangeTrace hZ sq hfp hY' =
      (derivedModulePushforward B S hS f').map ψ ≫ affineBaseChangeTrace hZ sq hfp hY') :
    φ = ψ := by
  have h' : ((affineBaseChangeAdjunction hZ sq hfp hY').homEquiv _ _).symm
      (ObjectProperty.homMk φ) =
      ((affineBaseChangeAdjunction hZ sq hfp hY').homEquiv _ _).symm (ObjectProperty.homMk ψ) := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    exact ObjectProperty.hom_ext _ h
  exact congrArg InducedCategory.Hom.hom (Equiv.injective _ h')

/-- **Every map `Rf'_* M ⟶ 𝒪_{Y'}` is the trace of a map `M ⟶ a'(𝒪_{Y'})`** (the second remark
after Stacks 0E5X). -/
theorem exists_affineBaseChangeTrace_comp
    (M : QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2)
    (t : (derivedModulePushforward B S hS f').obj M.obj ⟶
      (derivedStructureSheaf B S hS Y'.1 Y'.2).obj) :
    ∃ φ : M.obj ⟶ ((affineBaseChangeRightAdjoint hZ sq hfp hY').obj
      (derivedStructureSheaf B S hS Y'.1 Y'.2)).obj,
      (derivedModulePushforward B S hS f').map φ ≫ affineBaseChangeTrace hZ sq hfp hY' = t := by
  refine ⟨((affineBaseChangeAdjunction hZ sq hfp hY').homEquiv M _
    (ObjectProperty.homMk t)).hom, ?_⟩
  have h := congrArg InducedCategory.Hom.hom
    (((affineBaseChangeAdjunction hZ sq hfp hY').homEquiv M _).symm_apply_apply
      (ObjectProperty.homMk t))
  rwa [Adjunction.homEquiv_counit] at h

end Square

/-- A pair `(ω, τ)` of a `Y`-perfect object `ω` of `D(𝒪_X)` and a map `τ : Rf_* ω ⟶ 𝒪_Y`, for
a flat morphism `f : X ⟶ Y` of finite presentation: the data of a relative dualizing complex
(Stacks 0E5X), without its base change condition. -/
structure RelativeDualizingPair {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom) where
  /-- The complex `ω`. -/
  ω : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)
  /-- `ω` is perfect relative to `Y`. -/
  isPerfectRelativeTo : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hfp.1 ω
  /-- The map `τ : Rf_* ω ⟶ 𝒪_Y`. -/
  τ : (derivedModulePushforward B S hS f).obj ω ⟶ (derivedStructureSheaf B S hS Y.1 Y.2).obj

/-- Let `f : X ⟶ Y` be a proper, flat morphism of algebraic spaces over `S` of finite
presentation. A *relative dualizing complex* for `X/Y` is a pair `(ω, τ)` of a `Y`-perfect object
`ω` of `D(𝒪_X)` and a map `τ : Rf_* ω ⟶ 𝒪_Y` such that for every cartesian square
`g' ≫ f = f' ≫ g` with `Y'` an affine scheme, the pair `(L(g')^* ω, Lg^* τ)` is isomorphic to the
pair `(a'(𝒪_{Y'}), Tr_{f', 𝒪_{Y'}})` of the right adjoint `a'` of `Rf'_*` (Stacks 0E55) and its
trace map (Stacks 0E5K). -/
@[stacks 0E5X]
structure RelativeDualizingComplex {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (_hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) extends RelativeDualizingPair f hfl hfp where
  /-- The base change of `(ω, τ)` to every affine `Y'` is `(a'(𝒪_{Y'}), Tr_{f', 𝒪_{Y'}})`. -/
  isAffineBaseChangePair : ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1),
    IsAffineBaseChangePair hZ sq hfp hY' ω τ

end AlgebraicGeometry.Space

end
