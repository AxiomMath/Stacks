module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PointHomologyPullbackCoyoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomComp

/-!
# Products of `M ↦ Hom(P, Lf^*(M[0][i]))` from a model over a smaller base ring

Let `f : X ⟶ T` be flat over an affine `T` with `R = Γ(T, 𝒪_T)`, and let `P` be perfect on the
spaces-étale model of `X`. The criterion
`Space.isPseudoCoherent_pointDerivedEquiv_derivedPushforward_derivedDual_of_preservesLimit`
asks that `M ↦ Hom(P, Lf^*(M[0][i]))` preserve products of copies of `R`. This file derives that
from a model of the situation over a ring `R₀ ⟶ R`: a flat `f₀ : X₀ ⟶ T₀` with `Γ(T₀) = R₀`, a
morphism `g : X ⟶ X₀` with `P ≅ Lg^*P₀` for a perfect `P₀`, a base change identification
`Rg_* Lf^*(M[0][i]) ≅ Lf₀^*((M as an R₀-module)[0][i])` natural in the `R`-module `M`, and
perfectness of `RΓ(X₀, P₀^∨)` on the point `(pt, R₀)` (true for `R₀` Noetherian and `f₀` proper,
`Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper_of_isNoetherianRing`).

Indeed `Hom(P, Lf^*K) ≅ Hom(P₀, Rg_*Lf^*K)` by the adjunction `Lg^* ⊣ Rg_*`, then
`≅ Hom(P₀, Lf₀^*K₀) ≅ Hom(RΓ(X₀, P₀^∨)^∨, K₀)` (Stacks 08JJ, 08IN, 0B56:
`Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaIso`), and every functor in
`M ↦ Hom(L₀^∨, (M as an R₀-module)[0][i])` preserves products: restriction of scalars, placing a
module in degree zero (products are exact in module categories, Stacks 07KC), shifts and
corepresentable functors.

This is the product step of the proof of Stacks 0CTM by Noetherian approximation.

## Main results

* `AlgebraicGeometry.Space.preservesLimitsOfShape_singleFunctor_point_discrete`.
* `AlgebraicGeometry.Space.preservesLimit_coyoneda_derivedPullback_of_baseChange`.

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

/-- **Placing a module over the punctual ringed topos in degree zero commutes with products.**
Products of modules over the point are exact, being those of `R`-modules, so the localization
`Q` preserves them (Stacks 07KC), and so does placing a module in degree zero. -/
theorem preservesLimitsOfShape_singleFunctor_point_discrete {R : Type u} [CommRing R]
    (A : Type u) :
    PreservesLimitsOfShape (Discrete A)
      (DerivedCategory.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0) := by
  have : HasExactLimitsOfShape (Discrete A) (pointRingedTopos (CommRingCat.of R)).Modules :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete A)
      (baseRingPointModulesEquiv (R := R)).symm
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q
    (A := (pointRingedTopos (CommRingCat.of R)).Modules) (I := A)
  have : PreservesLimitsOfShape (Discrete A)
      (CochainComplex.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete A)
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0))
  have : PreservesLimitsOfShape (Discrete A)
      (CochainComplex.singleFunctor (pointRingedTopos (CommRingCat.of R)).Modules 0 ⋙
        DerivedCategory.Q) := comp_preservesLimitsOfShape _ _
  exact preservesLimitsOfShape_of_natIso (DerivedCategory.singleFunctorIsoCompQ _ 0).symm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X₀ : AlgebraicSpaces B S hS} {T T₀ : BigFppfOver B S hS}

attribute [local instance] hasCoproducts_derivedCategory_point
  hasCoproducts_derivedCategory_spacesEtaleModel

/-- **`M ↦ Hom(P, Lf^*(M[0][i]))` preserves products, given a model over a smaller base ring.**
Let `f : X ⟶ T` and `f₀ : X₀ ⟶ T₀` be flat over affines, `X₀` quasi-compact and
quasi-separated, `α : Γ(T₀) ⟶ Γ(T)`, `g : X ⟶ X₀`, `P ≅ Lg^*P₀` with `P₀` perfect, and suppose
`Rg_* Lf^*(M[0][i]) ≅ Lf₀^*((M as a Γ(T₀)-module)[0][i])` naturally in `M` and `RΓ(X₀, P₀^∨)` is
perfect on the point. Then `M ↦ Hom(P, Lf^*(M[0][i]))` preserves every product. -/
theorem preservesLimit_coyoneda_derivedPullback_of_baseChange (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f₀ : X₀ ⟶ schemeSpace T₀) (hflat₀ : IsFlat B S hS f₀.hom)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hX₀qc : IsQuasiCompactSpace B S hS X₀.1)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1)
    (g : X ⟶ X₀) (α : baseRing B S hS T₀ →+* baseRing B S hS T) (i : ℤ)
    (hbc : letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
      letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
      ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
          DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
          derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))) ⋙
          derivedPushforward.{u} (spacesEtaleModelHom B S hS g) ≅
        (ModuleCat.restrictScalars.{u} α ⋙
          (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse ⋙
          DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i) ⋙
          derivedPullback (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)))
    (P : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (P₀ : DerivedCategory (spacesEtaleModelRingedTopos B S hS X₀).Modules)
    (hP₀ : (spacesEtaleModelRingedTopos B S hS X₀).toRingedSite.IsPerfect P₀)
    (eP : (derivedPullback (spacesEtaleModelHom B S hS g)).obj P₀ ≅ P)
    (hL₀ : letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
      (pointRingedTopos (CommRingCat.of (baseRing B S hS T₀))).toRingedSite.IsPerfect
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀))).obj
          (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X₀).toRingedSite P₀)))
    (A : Type u) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    PreservesLimit (Discrete.functor fun _ : A => ModuleCat.of (baseRing B S hS T)
        (baseRing B S hS T))
      ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
        coyoneda.obj (op P)) := by
  let := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  let := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
  let R₀ := baseRing B S hS T₀
  let f₀' := spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)
  let hmos₀ := isMorphismOfSites_spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)
  let W := (baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
    derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))
  let V := ModuleCat.restrictScalars.{u} α ⋙ (baseRingPointModulesEquiv (R := R₀)).inverse ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i
  let G := derivedPushforward.{u} (spacesEtaleModelHom B S hS g)
  let C₀ := coyoneda.obj (op P₀)
  have hpf₀ : ∀ K, IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      f₀' hmos₀ (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X₀).toRingedSite P₀)
      K) := fun K =>
    isIso_projectionFormulaMap_spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)
      hZ hX₀qc hX₀qs _
      (derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS X₀.1 X₀.2 _
        (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X₀ _
          (RingedSite.isPerfect_derivedDual _ _ hP₀))) K
  let e₁ : W ⋙ coyoneda.obj (op P) ≅ W ⋙ (G ⋙ C₀) :=
    Functor.isoWhiskerLeft W (coyoneda.mapIso eP.op ≪≫
      (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction
        (spacesEtaleModelHom B S hS g)
        (isMorphismOfSites_spacesEtaleModelHom B S hS g)).compCoyonedaIso.app (op P₀))
  let e₂ : W ⋙ (G ⋙ C₀) ≅ V ⋙ coyoneda.obj (op (RingedSite.derivedDual
      (pointRingedTopos (CommRingCat.of R₀)).toRingedSite
      ((derivedPushforward f₀').obj
        (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X₀).toRingedSite P₀)))) :=
    (Functor.associator W G C₀).symm ≪≫ Functor.isoWhiskerRight hbc C₀ ≪≫
      Functor.associator V (derivedPullback f₀') C₀ ≪≫
      Functor.isoWhiskerLeft V
        (Stacks.Cohomology.ProjectionFormulaDualHom.derivedPullbackCoyonedaIso f₀' hmos₀ P₀ hP₀
          hpf₀ hL₀)
  have : PreservesLimitsOfShape (Discrete A)
      (DerivedCategory.singleFunctor (pointRingedTopos (CommRingCat.of R₀)).Modules 0) :=
    preservesLimitsOfShape_singleFunctor_point_discrete A
  have : PreservesLimitsOfShape (Discrete A) (ModuleCat.restrictScalars.{u} α) :=
    (ModuleCat.extendRestrictScalarsAdj α).rightAdjoint_preservesLimits.preservesLimitsOfShape
  exact preservesLimit_of_natIso _ (e₁ ≪≫ e₂).symm

/-- **The base change identification in degree zero gives it after every shift.** From
`Rg_* Lf^*(M[0]) ≅ Lf₀^*((M as a Γ(T₀)-module)[0])` naturally in `M`, the derived functors
commuting with shifts (Stacks 06YY, and `Rg_*` as a right adjoint) give
`Rg_* Lf^*(M[0][i]) ≅ Lf₀^*((M as a Γ(T₀)-module)[0][i])`. -/
def derivedPushforwardPullbackSingleShiftIso
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f₀ : X₀ ⟶ schemeSpace T₀) (hflat₀ : IsFlat B S hS f₀.hom)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (g : X ⟶ X₀) (α : baseRing B S hS T₀ →+* baseRing B S hS T)
    (hbc : letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
      letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
      ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
          DerivedCategory.singleFunctor _ 0) ⋙
          (derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
          derivedPushforward.{u} (spacesEtaleModelHom B S hS g)) ≅
        ((ModuleCat.restrictScalars.{u} α ⋙
          (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
          DerivedCategory.singleFunctor _ 0) ⋙
          derivedPullback (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)))
    (i : ℤ) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
    ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))) ⋙
        derivedPushforward.{u} (spacesEtaleModelHom B S hS g) ≅
      (ModuleCat.restrictScalars.{u} α ⋙
        (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i) ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)) :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
  letI := (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction
    (spacesEtaleModelHom B S hS g)
    (isMorphismOfSites_spacesEtaleModelHom B S hS g)).rightAdjointCommShift ℤ
  let U := (baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
    DerivedCategory.singleFunctor _ 0
  let U₀ := (ModuleCat.restrictScalars.{u} α ⋙
    (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
    DerivedCategory.singleFunctor _ 0
  let F := derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))
  let F₀ := derivedPullback (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀))
  let G := derivedPushforward.{u} (spacesEtaleModelHom B S hS g)
  let sh := shiftFunctor (DerivedCategory (pointRingedTopos (CommRingCat.of
    (baseRing B S hS T))).Modules) i
  let sh₀ := shiftFunctor (DerivedCategory (pointRingedTopos (CommRingCat.of
    (baseRing B S hS T₀))).Modules) i
  let sh' := shiftFunctor (DerivedCategory (spacesEtaleModelRingedTopos B S hS X₀).Modules) i
  (Functor.associator U (sh ⋙ F) G ≪≫ Functor.isoWhiskerLeft U (Functor.associator sh F G)) ≪≫
    Functor.isoWhiskerLeft U ((F ⋙ G).commShiftIso i) ≪≫
    (Functor.associator U (F ⋙ G) sh').symm ≪≫
    Functor.isoWhiskerRight hbc sh' ≪≫
    Functor.associator U₀ F₀ sh' ≪≫
    Functor.isoWhiskerLeft U₀ (F₀.commShiftIso i).symm ≪≫
    (Functor.associator U₀ sh₀ F₀).symm

/-- **`Lf^*(M[0]) = (f^*M)[0]` on the spaces-étale model, naturally in `M`**, for flat
`f : X ⟶ T` over an affine `T`: the derived pullback along `X ⟶ (pt, Γ(T))` is computed
degreewise (`Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso`). -/
def singleDerivedPullbackToBaseRingIso (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    (baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        DerivedCategory.singleFunctor _ 0 ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ≅
      ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        DerivedCategory.singleFunctor _ 0 :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  letI := preservesFiniteLimits_pullbackTopos_toBaseRing f hflat hT
  letI := preservesFiniteColimits_pullbackTopos_toBaseRing (B := B) (S := S) (hS := hS) (X := X)
    (baseRingHomOfMap f)
  let f' := spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso f')) ≪≫
    Functor.isoWhiskerLeft _ (f'.pullbackTopos.mapDerivedCategorySingleFunctor 0) ≪≫
    (Functor.associator _ _ _).symm

/-- **The derived base change identification from its underived pieces.** If
`Rg_*((f^*M)[0]) ≅ (g_*f^*M)[0]` naturally in `M` (`g` affine, `f^*M` quasi-coherent, Stacks
073H) and `g_*f^*M ≅ f₀^*(M as a Γ(T₀)-module)` naturally in `M` (affine base change on the
cartesian square), then `Rg_* Lf^*(M[0]) ≅ Lf₀^*((M as a Γ(T₀)-module)[0])` naturally in `M`. -/
def derivedPushforwardPullbackSingleIso
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f₀ : X₀ ⟶ schemeSpace T₀) (hflat₀ : IsFlat B S hS f₀.hom)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (g : X ⟶ X₀) (α : baseRing B S hS T₀ →+* baseRing B S hS T)
    (hacyc : ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ derivedPushforward.{u} (spacesEtaleModelHom B S hS g) ≅
      ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos ⋙ DerivedCategory.singleFunctor _ 0)
    (hpush : ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos ≅
      (ModuleCat.restrictScalars.{u} α ⋙
        (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
        (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)).pullbackTopos) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
    ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        DerivedCategory.singleFunctor _ 0) ⋙
        (derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
        derivedPushforward.{u} (spacesEtaleModelHom B S hS g)) ≅
      ((ModuleCat.restrictScalars.{u} α ⋙
        (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
        DerivedCategory.singleFunctor _ 0) ⋙
        derivedPullback (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)) :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀
  let τ := (baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
    (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos
  let G := derivedPushforward.{u} (spacesEtaleModelHom B S hS g)
  let s₁ := DerivedCategory.singleFunctor (spacesEtaleModelRingedTopos B S hS X).Modules 0
  let s₀ := DerivedCategory.singleFunctor (spacesEtaleModelRingedTopos B S hS X₀).Modules 0
  let r := ModuleCat.restrictScalars.{u} α
  Functor.isoWhiskerRight (singleDerivedPullbackToBaseRingIso f hflat hT) G ≪≫
    Functor.associator τ s₁ G ≪≫ hacyc ≪≫
    (Functor.associator τ (spacesEtaleModelHom B S hS g).pushforwardTopos s₀).symm ≪≫
    Functor.isoWhiskerRight hpush s₀ ≪≫
    Functor.associator r ((baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse ⋙
      (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)).pullbackTopos) s₀ ≪≫
    Functor.isoWhiskerLeft r (singleDerivedPullbackToBaseRingIso f₀ hflat₀ hT₀).symm

/-- **`RΓ(X, E)` is pseudo-coherent once every perfect object has a model over a smaller base
ring.** Let `f : X ⟶ T` be flat over an affine `T` with `X` quasi-compact and quasi-separated,
and suppose that for every perfect `P` on the spaces-étale model of `X` there are a flat
`f₀ : X₀ ⟶ T₀` over an affine `T₀` with `X₀` quasi-compact and quasi-separated, a morphism
`g : X ⟶ X₀`, a ring map `α : Γ(T₀) ⟶ Γ(T)`, a perfect `P₀` with `Lg^*P₀ ≅ P` and
`RΓ(X₀, P₀^∨)` perfect on the point, and `Rg_* Lf^*(M[0]) ≅ Lf₀^*((M as a Γ(T₀)-module)[0])`
naturally in `M`. Then the image of `Rf_*E` in `D(Γ(T))` is pseudo-coherent for every perfect
`E`: apply the product criterion to `P = E^∨`, using `E ≅ E^∨^∨` (Stacks 08JJ). -/
theorem isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_baseChangeModels
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (hmodel : ∀ P : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules,
      (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect P →
      ∃ (X₀ : AlgebraicSpaces B S hS) (T₀ : BigFppfOver B S hS) (f₀ : X₀ ⟶ schemeSpace T₀)
        (hflat₀ : IsFlat B S hS f₀.hom) (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
        (_ : IsQuasiCompactSpace B S hS X₀.1)
        (_ : IsAbsolutelyQuasiSeparated B S hS hZ X₀.1)
        (g : X ⟶ X₀) (α : baseRing B S hS T₀ →+* baseRing B S hS T)
        (P₀ : DerivedCategory (spacesEtaleModelRingedTopos B S hS X₀).Modules),
        (spacesEtaleModelRingedTopos B S hS X₀).toRingedSite.IsPerfect P₀ ∧
        Nonempty ((derivedPullback (spacesEtaleModelHom B S hS g)).obj P₀ ≅ P) ∧
        (letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀;
          (pointRingedTopos (CommRingCat.of (baseRing B S hS T₀))).toRingedSite.IsPerfect
            ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X₀
              (baseRingHomOfMap f₀))).obj
              (RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X₀).toRingedSite P₀))) ∧
        (letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT;
          letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f₀ hflat₀ hT₀;
          Nonempty (((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
              DerivedCategory.singleFunctor _ 0) ⋙
              (derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)) ⋙
              derivedPushforward.{u} (spacesEtaleModelHom B S hS g)) ≅
            ((ModuleCat.restrictScalars.{u} α ⋙
              (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
              DerivedCategory.singleFunctor _ 0) ⋙
              derivedPullback (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)))))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
          E)) := by
  let P := RingedSite.derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite E
  have hP : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect P :=
    RingedSite.isPerfect_derivedDual (spacesEtaleModelRingedTopos B S hS X).toRingedSite E hE
  obtain ⟨X₀, T₀, f₀, hflat₀, hT₀, hX₀qc, hX₀qs, g, α, P₀, hP₀, ⟨eP⟩, hL₀, ⟨hbc⟩⟩ :=
    hmodel P hP
  have h := isPseudoCoherent_pointDerivedEquiv_derivedPushforward_derivedDual_of_preservesLimit
    hZ f hflat hT hXqc hXqs P hP (fun A i =>
      preservesLimit_coyoneda_derivedPullback_of_baseChange hZ f hflat hT f₀ hflat₀ hT₀ hX₀qc
        hX₀qs g α i (derivedPushforwardPullbackSingleShiftIso f hflat hT f₀ hflat₀ hT₀ g α hbc i)
        P P₀ hP₀ eP hL₀ A)
  exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso h
    ((pointDerivedEquiv (R := baseRing B S hS T)).functor.mapIso
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).mapIso
        (RingedSite.derivedBidualIso (spacesEtaleModelRingedTopos B S hS X).toRingedSite E
          hE).symm))

end AlgebraicGeometry.Space

end
