module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardFibreSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiInputs
public import StacksFrontier.Homology.Perfect.BettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented

/-!
# The Betti numbers of the fibres of a flat proper family of algebraic spaces

Let `Y` be a scheme, `f : X ⟶ Y` a proper, flat morphism of finite presentation from an
algebraic space, and `𝓕` an `𝒪_X`-module of finite presentation, flat over `Y`. For `i ∈ ℤ` the
`i`-th Betti-number function is `β_i(y) = dim_{κ(y)} H^i(X_y, 𝓕_y)`. Stacks 0E0R: its formation
commutes with arbitrary base change, it is upper semicontinuous, and its level sets are locally
constructible.

## Main definitions

* `AlgebraicGeometry.Space.fibreBetti`: the function `β_i` on the points of `Y`.

## Main results

* `AlgebraicGeometry.Space.fibreBetti_baseChange`: Stacks 0E0R (1).
* `AlgebraicGeometry.Space.upperSemicontinuous_fibreBetti`: Stacks 0E0R (2).
* `isLocallyConstructible_fibreBetti_preimage`: Stacks 0E0R (3), in
  `StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiLevelSets`.

The three results hold without the flatness of `f`.

## Implementation notes

The scheme `Y` is an object `U` of the big fppf site, `X ⟶ Y` a morphism of algebraic spaces to
the representable `yoneda.obj U`. The fibre `X_y` is the fibre product of `X` with
`Spec κ(y) ⟶ Y`, and `H^i(X_y, 𝓕_y)` is read as the degree-`i` cohomology of
`RΓ(Spec κ(y), Rf_{y,*}𝓕_y)`, a module over `Γ(Spec κ(y), 𝒪) = κ(y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Set.Notation

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- global `HasDerivedCategory` instances in scope here compete with the standard model in which
-- the derived functors used here are stated (as in `CohomologyBaseChangeProper`)
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- **Extension of fields does not change the dimension of cohomology.** For a homomorphism
`ψ : A ⟶ L` of fields and `N ∈ D(A)`, `dim_L Hⁱ(N ⊗^L_A L) = dim_A Hⁱ(N)`. -/
theorem finrank_homology_totalDerivedExtensionScalars_of_isField {A L : Type u} [CommRing A]
    [CommRing L] (hA : IsField A) (hL : IsField L) (ψ : A →+* L)
    (N : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Module.finrank L ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj N)) =
      Module.finrank A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N) := by
  have hflat : ψ.Flat := by
    let := hA.toField
    let := ψ.toAlgebra
    change Module.Flat A L
    infer_instance
  have := extendScalars_preservesFiniteLimits_of_flat'.{u, u} ψ hflat
  let G := ModuleCat.extendScalars.{u, u, u} ψ
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj
      ((totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj N) ≅
      G.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N) :=
    (DerivedCategory.homologyFunctor _ i).mapIso
        ((Dualizing.totalDerivedExtensionScalarsIsoExtendScalars ψ).app N) ≪≫
      (G.mapDerivedCategoryHomologyIso i).app N
  exact e.toLinearEquiv.finrank_eq.trans
    (SpecField.finrank_extendScalars (R := CommRingCat.of A) (S := CommRingCat.of L) hA hL
      (CommRingCat.ofHom ψ) _)

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- **A further extension of fields does not change the dimension of the cohomology of a
derived base change.** For `φ : A ⟶ A'` and `ψ : A' ⟶ L` with `A'`, `L` fields,
`dim_L Hⁱ(M ⊗^L_A L) = dim_{A'} Hⁱ(M ⊗^L_A A')`. -/
theorem finrank_homology_totalDerivedExtensionScalars_comp {A A' L : Type u} [CommRing A]
    [CommRing A'] [CommRing L] (hA' : IsField A') (hL : IsField L) (φ : A →+* A')
    (ψ : A' →+* L) (M : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Module.finrank L ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} (ψ.comp φ)).functor.obj M)) =
      Module.finrank A' ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj M)) :=
  (((DerivedCategory.homologyFunctor _ i).mapIso
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp φ ψ).app
      M).symm).toLinearEquiv.finrank_eq).trans
    (finrank_homology_totalDerivedExtensionScalars_of_isField hA' hL ψ _ i)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars) in
/-- **The derived sections of a derived pullback between affine objects.** For `t : T ⟶ V` of
objects of the site with affine underlying schemes and `E ∈ D_QCoh(𝒪_V)`,
`RΓ(V, E) ⊗^L_{Γ(V)} Γ(T) ≅ RΓ(T, Lt^*E)`. -/
theorem nonempty_totalDerivedExtensionScalars_derivedSections_iso {T V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (t : T ⟶ V)
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)))
    (hE : QcohDerived B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ E) :
    Nonempty ((representedAffineDerivedExtension B S hS t).functor.obj
        ((representedAffineDerivedSections B S hS V).obj E) ≅
      (representedAffineDerivedSections B S hS T).obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj E)) := by
  have hcounit : IsIso ((representedAffineDerivedAdjunction B S hS V).counit.app E) :=
    isIso_representedAffineDerivedAdjunction_counit_app B S hS V E hE
  exact ⟨asIso ((representedAffineDerivedAdjunction B S hS T).unit.app _) ≪≫
    (representedAffineDerivedSections B S hS T).mapIso
      (((representedAffineDerivedBaseChangeIso B S hS t).app _).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).mapIso
          (@asIso _ _ _ _ _ hcounit))⟩

variable {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- The cohomology `RΓ(T, R(f_T)_*𝓕_T)` of the base change of `𝓕` to `X ×_Y T`, for an affine
object `T` over `Y`. -/
abbrev baseChangeDerivedSections {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t : T ⟶ U)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :=
  (representedAffineDerivedSections B S hS T).obj
    ((derivedModulePushforward B S hS (pullback.snd f (representedSpaceMap B S hS t))).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS t))).obj F)))

/-- **Cohomology and base change at `Rf_*𝓕`.** For `f` proper and of finite presentation and
`𝓕` of finite presentation and flat over `Y`, and any `t : T ⟶ Y`,
`Lt^*Rf_*𝓕 ≅ R(f_T)_*𝓕_T` (Stacks 0CTM (2)). -/
theorem nonempty_derivedPullback_iso_baseChange (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F)
    {T : BigFppfOver B S hS} (t : T ⟶ U) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (derivedModulePushforward B S hS (pullback.snd f (representedSpaceMap B S hS t))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS t))).obj F))) := by
  let g := representedSpaceMap B S hS t
  have h := (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp F hFfp
    hF).2 g (pullback.snd f g) (pullback.fst f g) (IsPullback.of_hasPullback f g)
  let C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)
  exact ⟨(smallEtaleDerivedModulePullback B S hS g).mapIso
      ((derivedModulePushforward B S hS f).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app F)) ≪≫ @asIso _ _ _ _ _ h ≪≫
    (derivedModulePushforward B S hS (pullback.snd f g)).mapIso
      (DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback B S hS (pullback.fst f g)) (ComplexShape.up ℤ) 0).app F) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm)⟩

/-- The pushforward `Rf_*𝓕` is derived quasi-coherent when `f` is proper and of finite
presentation and `𝓕` is of finite presentation and flat over `Y`. -/
private theorem qcohDerived_derivedModulePushforward_single (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) :
    QcohDerived B S hS _
      ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  derivedCategoryB_of_isPerfect B S hS _ _
    (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp F hFfp hF).1

/-- The hypotheses on `(f, 𝓕)` are stable under base change along `g : U' ⟶ U`. -/
private theorem isProper_and_isFinitePresentation_and_isFlatOver_pullback
    (hf : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFfp : F.IsFinitePresentation)
    (hF : IsFlatOver B S hS X.2 f.hom F) {U' : BigFppfOver B S hS} (g : U' ⟶ U) :
    IsProper B S hS (pullback.snd f (representedSpaceMap B S hS g)).hom ∧
      IsFinitePresentation B S hS (pullback.snd f (representedSpaceMap B S hS g)).hom ∧
      ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj
        F).IsFinitePresentation ∧
      IsFlatOver B S hS _ (pullback.snd f (representedSpaceMap B S hS g)).hom
        ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj F) := by
  have hpb := IsPullback.of_hasPullback f (representedSpaceMap B S hS g)
  have : F.IsQuasicoherentOnSite :=
    @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ F
      (isFinitePresentationOnSite_of_isFinitePresentation' F hFfp)
  have hF'fp := isFinitePresentation_modulePullback
    (pullback.fst f (representedSpaceMap B S hS g)) F hFfp
  have : ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj
      F).IsQuasicoherentOnSite :=
    @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _
      (isFinitePresentationOnSite_of_isFinitePresentation' _ hF'fp)
  exact ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback hpb hf,
    (isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
      hpb hfp, hF'fp,
    isFlatOver_modulePullback B S hS hpb F hF⟩

/-- `Γ(Spec κ(y), 𝒪) = κ(y)` is a field. -/
theorem isField_residueFieldSiteObj (U : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    IsField Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y), ⊤) :=
  (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField _)

/-- The morphism `Spec κ(y') ⟶ Spec κ(g y')` of the site induced by `g : U' ⟶ U` at a point `y'`
of `U'`. -/
def residueFieldSiteMap {U' U : BigFppfOver B S hS} (g : U' ⟶ U)
    (y' : (BigFppfOver.toScheme B S hS).obj U') :
    residueFieldSiteObj B S hS U' y' ⟶
      residueFieldSiteObj B S hS U (((BigFppfOver.toScheme B S hS).map g).base y') :=
  Over.homMk ⟨Spec.map (((BigFppfOver.toScheme B S hS).map g).residueFieldMap y')⟩ (by
    ext1
    exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc _ _ _).trans
      (congrArg (((BigFppfOver.toScheme B S hS).obj U').fromSpecResidueField y' ≫ ·)
        (congrArg InducedCategory.Hom.hom (Over.w g))))

/-- The square formed by `Spec κ(y') ⟶ U'`, `g : U' ⟶ U`, `Spec κ(g y') ⟶ U` and
`residueFieldSiteMap g y'` commutes. -/
theorem residueFieldSiteHom_comp {U' U : BigFppfOver B S hS} (g : U' ⟶ U)
    (y' : (BigFppfOver.toScheme B S hS).obj U') :
    residueFieldSiteHom B S hS U' y' ≫ g =
      residueFieldSiteMap g y' ≫ residueFieldSiteHom B S hS U _ := by
  ext1
  ext1
  exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ _).symm

/-- **Stacks 0E0R, part (1): the formation of `β_i` commutes with arbitrary base change.** For
`f : X ⟶ Y` proper and of finite presentation, `𝓕` of finite presentation and flat over `Y`,
and any morphism `g : Y' ⟶ Y` of schemes of the site, the `i`-th Betti-number function of the
base change `(X ×_Y Y' ⟶ Y', 𝓕_{Y'})` is `β_i ∘ g`. -/
@[stacks 0E0R "(1)"]
theorem fibreBetti_baseChange (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F)
    {U' : BigFppfOver B S hS} (g : U' ⟶ U) (i : ℤ) :
    fibreBettiFunction (pullback.snd f (representedSpaceMap B S hS g))
        ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj F) i =
      fibreBettiFunction f F i ∘ ((BigFppfOver.toScheme B S hS).map g).base := by
  funext y'
  let gS := representedSpaceMap B S hS g
  let f' := pullback.snd f gS
  let F' := (modulePullback B S hS (pullback.fst f gS)).obj F
  let y := ((BigFppfOver.toScheme B S hS).map g).base y'
  let t' := residueFieldSiteHom B S hS U' y'
  let t := residueFieldSiteHom B S hS U y
  let h := residueFieldSiteMap g y'
  obtain ⟨hf', hfp', hF'fp, hF'⟩ :=
    isProper_and_isFinitePresentation_and_isFlatOver_pullback f hf hfp F hFfp hF g
  let K := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  have hKq := qcohDerived_derivedModulePushforward_single f hf hfp F hFfp hF
  obtain ⟨e1⟩ := nonempty_derivedPullback_iso_baseChange f' hf' hfp' F' hF'fp hF' t'
  obtain ⟨e2⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF g
  obtain ⟨e3⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF t
  obtain ⟨e5⟩ := nonempty_totalDerivedExtensionScalars_derivedSections_iso h
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj K)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K hKq)
  have hm : representedSpaceMap B S hS t' ≫ gS =
      representedSpaceMap B S hS h ≫ representedSpaceMap B S hS t := by
    rw [representedSpaceMap_comp, representedSpaceMap_comp, residueFieldSiteHom_comp]
  obtain ⟨e4⟩ : Nonempty
      ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t')).obj
          ((smallEtaleDerivedModulePullback B S hS gS).obj K) ≅
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj K)) := by
    refine ⟨(smallEtaleDerivedModulePullbackCompIso B S hS _ gS).app K ≪≫ ?_ ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app K).symm⟩
    rw [hm]
  let RΓ' := representedAffineDerivedSections B S hS (residueFieldSiteObj B S hS U' y')
  let chain : baseChangeDerivedSections f' t' F' ≅
      (representedAffineDerivedExtension B S hS h).functor.obj
        (baseChangeDerivedSections f t F) :=
    RΓ'.mapIso (e1.symm ≪≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t')).mapIso e2.symm ≪≫
      e4) ≪≫ e5.symm ≪≫
    (representedAffineDerivedExtension B S hS h).functor.mapIso
      ((representedAffineDerivedSections B S hS (residueFieldSiteObj B S hS U y)).mapIso e3)
  exact (((DerivedCategory.homologyFunctor _ i).mapIso chain).toLinearEquiv.finrank_eq).trans
    (finrank_homology_totalDerivedExtensionScalars_of_isField (isField_residueFieldSiteObj U y)
      (isField_residueFieldSiteObj U' y') _ _ i)

/-- **The dimension of `Hⁱ(X_T, 𝓕_T)` is unchanged along a morphism of field-like affine objects
over `Y`.** For `t₁ = k ≫ t₂` with `Γ(T₁)`, `Γ(T₂)` fields,
`dim_{Γ(T₁)} Hⁱ(X_{T₁}, 𝓕_{T₁}) = dim_{Γ(T₂)} Hⁱ(X_{T₂}, 𝓕_{T₂})`. -/
theorem finrank_homology_baseChangeDerivedSections_eq (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F)
    {T₁ T₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₂)] (t₁ : T₁ ⟶ U) (t₂ : T₂ ⟶ U)
    (k : T₁ ⟶ T₂) (hk : k ≫ t₂ = t₁)
    (h₁ : IsField Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤))
    (h₂ : IsField Γ((BigFppfOver.toScheme B S hS).obj T₂, ⊤)) (i : ℤ) :
    Module.finrank Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T₁, ⊤))
          i).obj (baseChangeDerivedSections f t₁ F)) =
      Module.finrank Γ((BigFppfOver.toScheme B S hS).obj T₂, ⊤)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj T₂, ⊤))
          i).obj (baseChangeDerivedSections f t₂ F)) := by
  subst hk
  let K := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  have hKq := qcohDerived_derivedModulePushforward_single f hf hfp F hFfp hF
  obtain ⟨e1⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF (k ≫ t₂)
  obtain ⟨e3⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF t₂
  obtain ⟨e5⟩ := nonempty_totalDerivedExtensionScalars_derivedSections_iso k
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t₂)).obj K)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K hKq)
  obtain ⟨e4⟩ : Nonempty ((smallEtaleDerivedModulePullback B S hS
      (representedSpaceMap B S hS (k ≫ t₂))).obj K ≅
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS k)).obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t₂)).obj K)) := by
    rw [← representedSpaceMap_comp]
    exact ⟨((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app K).symm⟩
  let chain : baseChangeDerivedSections f (k ≫ t₂) F ≅
      (representedAffineDerivedExtension B S hS k).functor.obj
        (baseChangeDerivedSections f t₂ F) :=
    (representedAffineDerivedSections B S hS T₁).mapIso (e1.symm ≪≫ e4) ≪≫ e5.symm ≪≫
    (representedAffineDerivedExtension B S hS k).functor.mapIso
      ((representedAffineDerivedSections B S hS T₂).mapIso e3)
  exact (((DerivedCategory.homologyFunctor _ i).mapIso chain).toLinearEquiv.finrank_eq).trans
    (finrank_homology_totalDerivedExtensionScalars_of_isField h₂ h₁ _ _ i)

section Affine

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **The fibre cohomology over `Spec κ(𝔭)` for affine `Y`.** For `Y` affine and `𝔭` a prime of
`A = Γ(Y, 𝒪)`, `dim_{κ(𝔭)} Hⁱ(X_{κ(𝔭)}, 𝓕_{κ(𝔭)}) = dim_{κ(𝔭)} Hⁱ(K ⊗^L_A κ(𝔭))` with
`K = RΓ(Y, Rf_*𝓕)`. -/
theorem finrank_homology_baseChangeDerivedSections_residueFieldSiteMapOfIsAffine
    (hf : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFfp : F.IsFinitePresentation)
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (p : Ideal Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) [p.IsPrime] (i : ℤ) :
    Module.finrank Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObject B hS
        (specGlobalSectionsPoint B S hS U p)
        (contains_spec_residueField_specGlobalSectionsPoint B S hS U p)), ⊤)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj
        (residueFieldSiteObject B hS (specGlobalSectionsPoint B S hS U p)
          (contains_spec_residueField_specGlobalSectionsPoint B S hS U p)), ⊤)) i).obj
        (baseChangeDerivedSections f (residueFieldSiteMapOfIsAffine B S hS U p) F)) =
      StacksDraft.Perfect.fibreBetti.{u, u} ((representedAffineDerivedSections B S hS U).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) i
        ⟨p, inferInstance⟩ := by
  let t := residueFieldSiteMapOfIsAffine B S hS U p
  let T := residueFieldSiteObject B hS (specGlobalSectionsPoint B S hS U p)
    (contains_spec_residueField_specGlobalSectionsPoint B S hS U p)
  let K := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  have hKq := qcohDerived_derivedModulePushforward_single f hf hfp F hFfp hF
  obtain ⟨e3⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF t
  obtain ⟨e5⟩ := nonempty_totalDerivedExtensionScalars_derivedSections_iso t K hKq
  let e := residueFieldSiteObjectRingEquivOfIsAffine B S hS U p
  have hT : IsField Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    e.toMulEquiv.isField (Field.toIsField _)
  have h := finrank_homology_totalDerivedExtensionScalars_comp hT
    (Field.toIsField p.ResidueField) (representedAffineCommRingCatHom B S hS t).hom
    (e : _ →+* p.ResidueField) ((representedAffineDerivedSections B S hS U).obj K) i
  rw [residueFieldSiteObjectRingEquivOfIsAffine_comp] at h
  exact (((DerivedCategory.homologyFunctor _ i).mapIso
    ((representedAffineDerivedSections B S hS T).mapIso e3.symm ≪≫
      e5.symm)).toLinearEquiv.finrank_eq).trans h.symm

/-- **The Betti numbers over an affine base.** For `Y` affine with `A = Γ(Y, 𝒪)`,
`β_i(y) = dim_{κ(𝔭)} Hⁱ(K ⊗^L_A κ(𝔭))`, where `K = RΓ(Y, Rf_*𝓕)` and `𝔭` is the prime of `A`
corresponding to `y`. -/
theorem fibreBetti_eq_comp_isoSpec (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ) :
    fibreBettiFunction f F i =
      StacksDraft.Perfect.fibreBetti.{u, u} ((representedAffineDerivedSections B S hS U).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) i ∘
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.base := by
  funext y
  let Y := (BigFppfOver.toScheme B S hS).obj U
  let q := Y.isoSpec.hom.base y
  let k : residueFieldSiteObj B S hS U y ⟶ residueFieldSiteObject B hS
      (specGlobalSectionsPoint B S hS U q.asIdeal)
      (contains_spec_residueField_specGlobalSectionsPoint B S hS U q.asIdeal) :=
    Over.homMk ⟨Spec.map (Y.isoSpec.hom.residueFieldMap y)⟩ (by
      ext1
      change Spec.map (Y.isoSpec.hom.residueFieldMap y) ≫
          ((Spec Γ(Y, ⊤)).fromSpecResidueField q ≫ Y.isoSpec.inv ≫ B.inclusion.map U.hom) =
        Y.fromSpecResidueField y ≫ U.hom.hom
      rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Iso.hom_inv_id_assoc]
      rfl)
  have hk : k ≫ residueFieldSiteMapOfIsAffine B S hS U q.asIdeal =
      residueFieldSiteHom B S hS U y := by
    ext1
    ext1
    change Spec.map (Y.isoSpec.hom.residueFieldMap y) ≫
        ((Spec Γ(Y, ⊤)).fromSpecResidueField q ≫ Y.isoSpec.inv) = Y.fromSpecResidueField y
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact (finrank_homology_baseChangeDerivedSections_eq f hf hfp F hFfp hF _ _ k hk
    (isField_residueFieldSiteObj U y)
    ((residueFieldSiteObjectRingEquivOfIsAffine B S hS U q.asIdeal).toMulEquiv.isField
      (Field.toIsField _)) i).trans
    (finrank_homology_baseChangeDerivedSections_residueFieldSiteMapOfIsAffine f hf hfp F hFfp hF
      q.asIdeal i)

end Affine

/-- **Locally, `β_i` is the derived-fibre Betti function of a pseudo-coherent complex of
modules.** Every point of `Y` lies in the image of an open embedding `φ : Spec R → Y` with
`β_i ∘ φ = (𝔭 ↦ dim_{κ(𝔭)} Hⁱ(M ⊗^L_R κ(𝔭)))` for some pseudo-coherent `M ∈ D(R)`. -/
theorem exists_isOpenEmbedding_fibreBetti_comp_eq (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (R : CommRingCat.{u}) (M : DerivedCategory (ModuleCat.{u} R))
      (φ : PrimeSpectrum R → (BigFppfOver.toScheme B S hS).obj U),
      Topology.IsOpenEmbedding φ ∧ x ∈ Set.range φ ∧
        StacksDraft.PseudoCoherence.IsPseudoCoherent M ∧
        fibreBettiFunction f F i ∘ φ = StacksDraft.Perfect.fibreBetti.{u, u} M i := by
  let Y := (BigFppfOver.toScheme B S hS).obj U
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let T := siteOpenObject B S hS U W
  let g : T ⟶ U := Over.homMk (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt U.left.property))
    (Y := U.left) (Scheme.Opens.ι W)) (by rfl)
  have hg : (BigFppfOver.toScheme B S hS).map g = (Scheme.Opens.ι W) :=
    B.inclusion.map_preimage
      (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt U.left.property)) (Y := U.left)
      (Scheme.Opens.ι W)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hW
  let gS := representedSpaceMap B S hS g
  let f' := pullback.snd f gS
  let F' := (modulePullback B S hS (pullback.fst f gS)).obj F
  obtain ⟨hf', hfp', hF'fp, hF'⟩ :=
    isProper_and_isFinitePresentation_and_isFlatOver_pullback f hf hfp F hFfp hF g
  let M := (representedAffineDerivedSections B S hS T).obj
    ((derivedModulePushforward B S hS f').obj ((DerivedCategory.singleFunctor _ 0).obj F'))
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M :=
    StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
      (isPerfect_representedAffineDerivedSections_obj B S hS T _
        (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f' hf' hfp' F' hF'fp
          hF').1)
  let h := Scheme.homeoOfIso ((BigFppfOver.toScheme B S hS).obj T).isoSpec
  have h1 := fibreBetti_baseChange f hf hfp F hFfp hF g i
  have h2 := fibreBetti_eq_comp_isoSpec f' hf' hfp' F' hF'fp hF' i
  refine ⟨Γ((BigFppfOver.toScheme B S hS).obj T, ⊤), M,
    ((BigFppfOver.toScheme B S hS).map g).base ∘ h.symm, ?_, ?_, hM, ?_⟩
  · rw [hg]
    exact (Scheme.Opens.ι W).isOpenEmbedding.comp h.symm.isOpenEmbedding
  · let w : (BigFppfOver.toScheme B S hS).obj T := ⟨x, hxW⟩
    refine ⟨h w, ?_⟩
    change ((BigFppfOver.toScheme B S hS).map g).base (h.symm (h w)) = x
    rw [h.symm_apply_apply, hg]
    rfl
  · funext z
    change (fibreBettiFunction f F i ∘ ((BigFppfOver.toScheme B S hS).map g).base) (h.symm z) = _
    rw [← h1, h2]
    exact congrArg (StacksDraft.Perfect.fibreBetti.{u, u} M i) (h.apply_symm_apply z)

/-- **Stacks 0E0R, part (2): the Betti numbers of the fibres are upper semicontinuous.** For
`f : X ⟶ Y` proper and of finite presentation and `𝓕` of finite presentation and flat over `Y`,
the function `y ↦ dim_{κ(y)} Hⁱ(X_y, 𝓕_y)` is upper semicontinuous on `Y`. -/
@[stacks 0E0R "(2)"]
theorem upperSemicontinuous_fibreBetti (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ) :
    UpperSemicontinuous (fibreBettiFunction f F i) := by
  intro x n hn
  obtain ⟨R, M, φ, hφ, ⟨z, rfl⟩, hM, heq⟩ :=
    exists_isOpenEmbedding_fibreBetti_comp_eq f hf hfp F hFfp hF i x
  have hz := StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent.{u, u} M hM
    i z n (by rwa [← heq])
  rw [← hφ.map_nhds_eq z, Filter.eventually_map]
  rwa [← heq] at hz

end AlgebraicGeometry.Space.ProperFlatStein
