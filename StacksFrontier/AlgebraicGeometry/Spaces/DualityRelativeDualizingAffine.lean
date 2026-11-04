module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffineIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex

/-!
# Relative dualizing complexes over an affine base

Let `Y` be an affine algebraic space and `f : X ⟶ Y` a proper, flat morphism of finite
presentation, with right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` (Stacks 0E55) and
trace map `Tr : Rf_* a(𝒪_Y) ⟶ 𝒪_Y`. By the third remark after Stacks 0E5X, `(a(𝒪_Y), Tr)` is a
relative dualizing complex for `X/Y`: its base change to an affine `Y'` is
`(a'(𝒪_{Y'}), Tr')` through the base change map of Stacks 0E5D, which is compatible with the
trace maps by Stacks 0E5L.

## Main definitions

* `AlgebraicGeometry.Space.affineRightAdjoint`: the right adjoint `a` of `Rf_*` over an affine
  base.
* `AlgebraicGeometry.Space.affineTrace`: the trace map `Rf_* a(𝒪_Y) ⟶ 𝒪_Y`.
* `AlgebraicGeometry.Space.RelativeDualizingComplex.ofIsAffineSpace`: the relative dualizing
  complex `(a(𝒪_Y), Tr)`, from the `Y`-perfectness of `a(𝒪_Y)` (Stacks 0E5V (1)); the base
  change maps `L(g')^* a(𝒪_Y) ⟶ a'(𝒪_{Y'})` are invertible by Stacks 0E5I (1).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

section Affine

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfp : IsFinitePresentation B S hS f.hom)
  (hY : IsAffineSpace B S hS Y.1)

/-- The right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` for a morphism of finite
presentation to an affine algebraic space (Stacks 0E55). -/
abbrev affineRightAdjoint :
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  quasicoherentDerivedRightAdjoint hZ f
    (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY)

/-- The trace map `Tr_{f, 𝒪_Y} : Rf_* a(𝒪_Y) ⟶ 𝒪_Y` (Stacks 0E5K) over an affine base: the
counit of `Rf_* ⊣ a` at the structure sheaf. -/
def affineTrace :
    (derivedModulePushforward B S hS f).obj
        ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj ⟶
      (derivedStructureSheaf B S hS Y.1 Y.2).obj :=
  ((quasicoherentDerivedRightAdjointAdjunction hZ f
    (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hfp.2.1 hfp.2.2).counit.app
      (derivedStructureSheaf B S hS Y.1 Y.2)).hom

/-- The right adjoint of the base change of a morphism of finite presentation to an affine `Y'`
is `affineRightAdjoint` of the base change. -/
theorem affineBaseChangeRightAdjoint_eq {X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hfp : IsFinitePresentation B S hS f.hom) (hY' : IsAffineSpace B S hS Y'.1) :
    affineBaseChangeRightAdjoint hZ sq hfp hY' =
      affineRightAdjoint hZ f' ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        sq hfp) hY' :=
  rfl

/-- The trace map of the base change of a morphism of finite presentation to an affine `Y'` is
`affineTrace` of the base change. -/
theorem affineBaseChangeTrace_eq {X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hfp : IsFinitePresentation B S hS f.hom) (hY' : IsAffineSpace B S hS Y'.1) :
    affineBaseChangeTrace hZ sq hfp hY' =
      affineTrace hZ f' ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        sq hfp) hY' :=
  rfl

end Affine

/-- The diagram chase identifying the base change of the trace map: `h₁` is the compatibility
of the base change map with the traces, `h₂` the naturality of the trace. -/
theorem affineTrace_baseChange_aux {C : Type*} [Category C] {P Q R T U V : C}
    (bc : P ⟶ Q) (rα : Q ⟶ R) (t₁ : R ⟶ T) (lt : P ⟶ T) (u : T ⟶ U) (ra : R ⟶ V) (t₂ : V ⟶ U)
    (h₁ : bc ≫ rα ≫ t₁ = lt) (h₂ : ra ≫ t₂ = t₁ ≫ u) (r : Q ⟶ V) (hr : r = rα ≫ ra) :
    lt ≫ u = bc ≫ r ≫ t₂ := by
  subst hr
  rw [← h₁]
  simp only [Category.assoc, h₂]

namespace RelativeDualizingComplex

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
  (hfl : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
  (hY : IsAffineSpace B S hS Y.1)

/-- The base change map `L(g')^* a(𝒪_Y) ⟶ a'(Lg^* 𝒪_Y)` of Stacks 0E5D at the structure sheaf,
for a cartesian square over an affine `Y` with `Y'` affine. -/
abbrev affineRightAdjointBaseChangeMap ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : IsPullback g' f' f g) (hY' : IsAffineSpace B S hS Y'.1) :=
  (quasicoherentDerivedRightAdjointBaseChangeMap hZ sq
    (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY'.isQuasiCompactSpace
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
    (torIndependent_of_isFlat_left f g hfl)).app (derivedStructureSheaf B S hS Y.1 Y.2)

/-- **The relative dualizing complex `(a(𝒪_Y), Tr)` over an affine base** (third remark after
Stacks 0E5X), from the `Y`-perfectness of `a(𝒪_Y)` (Stacks 0E5V (1)): the base change maps
`L(g')^* a(𝒪_Y) ⟶ a'(Lg^* 𝒪_Y)` for `Y'` affine are invertible (Stacks 0E5I (1)) and compatible
with the trace maps by Stacks 0E5L. -/
def ofIsAffineSpace
    (hperf : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hfp.1
      ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj) :
    RelativeDualizingComplex hZ f hf hfl hfp where
  ω := ((affineRightAdjoint hZ f hfp hY).obj (derivedStructureSheaf B S hS Y.1 Y.2)).obj
  isPerfectRelativeTo := hperf
  τ := affineTrace hZ f hfp hY
  isAffineBaseChangePair := fun X' Y' f' g g' sq hY' => by
    have := isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isFlat hZ sq hf hfl hfp hY
      hY' (derivedStructureSheaf B S hS Y.1 Y.2)
    let uQ : (quasicoherentDerivedModulePullback g).obj (derivedStructureSheaf B S hS Y.1 Y.2) ≅
        derivedStructureSheaf B S hS Y'.1 Y'.2 :=
      ObjectProperty.isoMk _ (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g)
    let a' := affineBaseChangeRightAdjoint hZ sq hfp hY'
    let α := affineRightAdjointBaseChangeMap hZ f hfl hfp hY f' g g' sq hY'
    refine ⟨(ObjectProperty.ι _).mapIso (asIso α ≪≫ a'.mapIso uQ), ?_⟩
    have h₁ := congrArg InducedCategory.Hom.hom
      (quasicoherentDerivedRightAdjointBaseChangeMap_trace hZ sq
        (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
        (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
        (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY'.isQuasiCompactSpace
        (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
        (torIndependent_of_isFlat_left f g hfl) (derivedStructureSheaf B S hS Y.1 Y.2))
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at h₁
    have h₂ := congrArg InducedCategory.Hom.hom
      ((quasicoherentDerivedRightAdjointAdjunction hZ f'
        (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f'
          (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp) hY')
        (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f'
          (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp) hY')
        (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
        (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp)
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp)).counit.naturality uQ.hom)
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom] at h₂
    exact affineTrace_baseChange_aux
      (C := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
      _ _ _ _ _ _ _ h₁ h₂ _ (Functor.map_comp _ _ _)

end RelativeDualizingComplex

end AlgebraicGeometry.Space

end
