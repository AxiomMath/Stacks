module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.LocallyConstantOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothProperHigherDirectImageLocallyConstantNoetherian
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.ModuleRingEquiv
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.AffineLineNagata
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafGenerationByQCQS
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GenericFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.GeneralConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveNoetherianReduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of a smooth proper morphism: reduction to a Noetherian base

Let `S` be affine, `f : X ⟶ S` smooth and proper, `N > 0` an integer invertible on `S` and `F` a
finite type, locally constant sheaf of `Λ`-modules on `X_étale` killed by `N`, `Λ` Noetherian.
This file proves that every `Rᵠ f_* F` is finite type and locally constant, reducing to the
Noetherian case of `SmoothProperHigherDirectImageLocallyConstantNoetherian`: the third paragraph
of the proof of [Stacks, Tag 0GLI].

`S = Spec A` is the limit of the spectra `S_t` of the finitely generated subrings of `A`
containing an inverse of `N`; `f` is the base change of a smooth proper `f_t : X_t ⟶ S_t`
([Stacks, Tags 01ZM, 081F, 0C0C]); `F` is the inverse image of a finite type, locally constant
`F_t` ([Stacks, Tag 0GL2]), still killed by `N` at a later stage (faithfulness in Tag 0GL2); `N`
is invertible on the Noetherian `S_t`, so the Noetherian case applies to `f_t` and `F_t`, and
proper base change ([Stacks, Tag 095T], with coefficients in `Λ`) identifies the inverse image of
`Rᵠ f_{t*} F_t` with `Rᵠ f_* F`.

## Main results

* `AlgebraicGeometry.smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_of_ringEquiv` and
  `AlgebraicGeometry.smallEtaleStagesFaithful_isFiniteTypeLocallyConstant_of_ringEquiv`: clause
  (3) of Tag 0GL2 for a coefficient ring isomorphic to one in `Type (u + 1)`.
* `Stacks.EtaleCohomology.nonempty_inverseImage_rightDerived_iso_of_isProper`: proper base change
  for the higher direct images of a torsion sheaf of `Λ`-modules.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_stage`.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_isAffine`.

## References

* [Stacks Project, Tag 0GLI](https://stacks.math.columbia.edu/tag/0GLI)
* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ]

attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse

variable {Λ₀ : Type (u + 1)} [CommRing Λ₀] (φ : Λ₀ ≃+* Λ)

/-- **Local constancy of finite type is carried to `Λ₀`-modules** by restriction of scalars along
a ring isomorphism `φ : Λ₀ ≃+* Λ`. -/
theorem isFiniteTypeLocallyConstant_restrictScalars_ringEquiv (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B X.1 X.property) F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ₀ (SmallEtale.topology B X.1 X.property)
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        (moduleCatSiteRingEquivalence.{u} Λ φ)).functor.obj F) :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence _
    (moduleCatSiteRingEquivalence.{u} Λ φ) (fun M => ModuleCat.isFG Λ M)
    (fun M hM => by
      have := (ModuleCat.isFG_iff _).1 hM
      exact (ModuleCat.isFG_iff _).2 (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv φ M))
    F hF _ (Iso.refl _)

/-- **Local constancy of finite type is carried back to `Λ`-modules** by restriction of scalars
along a ring isomorphism. -/
theorem isFiniteTypeLocallyConstant_of_restrictScalars_ringEquiv (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ₀))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ₀
      (SmallEtale.topology B X.1 X.property) F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.property)
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        (moduleCatSiteRingEquivalence.{u} Λ φ)).inverse.obj F) :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence _
    (moduleCatSiteRingEquivalence.{u} Λ φ).symm (fun M => ModuleCat.isFG Λ₀ M)
    (fun M hM => by
      have := (ModuleCat.isFG_iff _).1 hM
      exact (ModuleCat.isFG_iff _).2
        (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv φ.symm M))
    F hF _ (Iso.refl _)

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

include φ

/-- **Stacks 0GL2, clause (3), essential surjectivity, along a ring isomorphism.** -/
theorem smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_of_ringEquiv (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B Y.obj Y.property) F) := by
  intro F hF
  obtain ⟨i, Fi, hFi, ⟨e⟩⟩ := smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat B Dg c
    hX Λ₀ hc haff hqc hqs _ (isFiniteTypeLocallyConstant_restrictScalars_ringEquiv B Λ φ _ F hF)
  refine ⟨i, _, isFiniteTypeLocallyConstant_of_restrictScalars_ringEquiv B Λ φ _ Fi hFi, ⟨?_⟩⟩
  exact ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (coneStageHom B Dg c hX i))
      (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (SmallEtale.topology B c.pt hX) (moduleCatSiteRingEquivalence.{u} Λ φ).symm).app Fi).symm ≪≫
    (sheafCompose _ (moduleCatSiteRingEquivalence.{u} Λ φ).inverse).mapIso e ≪≫
    ((Sheaf.coefficientEquivalence (SmallEtale.topology B c.pt hX)
      (moduleCatSiteRingEquivalence.{u} Λ φ)).unitIso.app F).symm

omit [Nonempty I] in
/-- **Stacks 0GL2, clause (3), faithfulness, along a ring isomorphism.** -/
theorem smallEtaleStagesFaithful_isFiniteTypeLocallyConstant_of_ringEquiv [IsNoetherianRing Λ₀]
    (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (SmallEtale.topology B Y.obj Y.property) F) :=
  smallEtaleStagesFaithful_of_coefficientEquivalence B (moduleCatSiteRingEquivalence.{u} Λ φ) Dg c
    hX (fun X F hF => isFiniteTypeLocallyConstant_restrictScalars_ringEquiv B Λ φ X F hF)
    (smallEtaleStagesFaithful_isFiniteTypeLocallyConstant B Dg c hX Λ₀ hc haff hqc hqs)

end AlgebraicGeometry

open AlgebraicGeometry Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

attribute [local instance 2000] SmallEtale.isRightAdjointPushforward_moduleCat_siteUniverse
  SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse smallEtaleHasSheafifyModuleMax

variable (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- A torsion sheaf of `Λ`-modules placed in degree zero has torsion cohomology sheaves. -/
theorem isTorsionPlus_singleFunctor_obj {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X)
    (hF : IsTorsionEtaleModule Λ X F) :
    isTorsionPlus.{u, 0} Λ X ((DerivedCategory.Plus.singleFunctor _ 0).obj F) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact IsTorsionEtaleModule.of_iso Λ X
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso
        (C := EtaleModules.{u, 0} Λ X) 0).app F).symm hF
  · exact isTorsionEtaleModule_of_isZero Λ X
      (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj F hi)

/-- **Proper base change for the higher direct images of a torsion sheaf of `Λ`-modules**
([Stacks, Tag 095T] with coefficients in `Λ`). For a cartesian square `f' ≫ g = g' ≫ f` with `f`
proper and a torsion sheaf `F` of `Λ`-modules on `X_étale`,
`g⁻¹ Rᵠ f_* F ≅ Rᵠ f'_* ((g')⁻¹ F)`. -/
theorem nonempty_inverseImage_rightDerived_iso_of_isProper {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (F : EtaleModules.{u, 0} Λ X) (hF : IsTorsionEtaleModule Λ X F) (q : ℕ) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ g).obj
        (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) ≅
      ((etaleModuleDirectImage.{u, 0} Λ f').rightDerived q).obj
        ((etaleModuleInverseImage.{u, 0} Λ g').obj F)) := by
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj F
  have := isIso_etaleModuleDerivedBaseChange_of_isProper Λ f sq K
    (isTorsionPlus_singleFunctor_obj Λ F hF)
  obtain ⟨e₁⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ g
    ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K) q
  obtain ⟨e₂⟩ := nonempty_inverseImage_singleFunctor_iso (Λ := Λ) g' F
  exact ⟨(etaleModuleInverseImage.{u, 0} Λ g).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} Λ f) q).app F) ≪≫
    e₁.symm ≪≫ (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' sq.w.symm).app K) ≪≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f').mapIso e₂) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} Λ f') q).app
      _).symm⟩

/-! ### The stage step -/

section Stage

variable (B : BigEtaleSite.{u})

/-- `N` invertible on a scheme `Y` is prime to the characteristic of the residue field of every
geometric point of `Y`. -/
@[sga "4 IX 3.0" "partial"]
theorem ringChar_residueField_eq_zero_or_coprime_of_isUnit {Y : Scheme.{u}} (N : ℕ)
    (hN : IsUnit ((N : ℕ) : Γ(Y, ⊤))) (x : GeometricPoint Y) :
    ringChar x.residueField = 0 ∨ N.Coprime (ringChar x.residueField) := by
  have hu : IsUnit (N : x.residueField) := by
    have h1 := isUnit_natCast_of_hom x.hom hN
    rw [natCast_ΓSpec] at h1
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of x.residueField)).hom.hom
    rwa [← CategoryTheory.comp_apply, Iso.inv_hom_id, CategoryTheory.id_apply] at h2
  exact SmoothBaseChange.ringChar_eq_zero_or_coprime_of_isUnit hu

variable (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- An additive functor carries an object killed by `N` to an object killed by `N`. -/
private theorem nsmul_id_eq_zero_obj {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {N : ℕ} {X : C} (h : N • 𝟙 X = 0) :
    N • 𝟙 (G.obj X) = 0 := by
  rw [← G.map_id, ← Functor.map_nsmul, h, G.map_zero]

/-- **Tag 0GLI from a stage of a Noetherian approximation.** Let `X = lim X_p` be a directed
inverse limit in `B` with affine transition morphisms and quasi-compact quasi-separated stages,
let `φ_p : X_p ⟶ Y_p` be smooth and proper over Noetherian schemes `Y_p` on which the integer
`N > 0` is invertible, and let `f : X ⟶ S` be the base change of `φ_p` along `g_p : S ⟶ Y_p` for
every `p`. Then for every finite type, locally constant sheaf `F` of `Λ`-modules on `X` killed by
`N`, every `Rᵠ f_* F` is finite type and locally constant.

`F` comes from a finite type locally constant sheaf at some stage (Stacks 0GL2), still killed by
`N` at a later stage; there the Noetherian case applies, and proper base change (Stacks 095T)
carries the conclusion back to `S`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_stage (N : ℕ) (hN : 0 < N)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (DX DY : Iᵒᵖ ⥤ B.Scheme) (φ : DX ⟶ DY)
    (cX : Cone (DX ⋙ B.inclusion)) (hX : B.Contains cX.pt) (hcX : IsLimit cX)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (DX.map e)))
    (hqc : ∀ p : I, CompactSpace (DX.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (DX.obj (op p)).obj)
    (hNoeth : ∀ p : I, IsNoetherian (DY.obj (op p)).obj)
    (hφ : ∀ p : I, IsProper (B.inclusion.map (φ.app (op p))) ∧
      Smooth (B.inclusion.map (φ.app (op p))))
    (hunit : ∀ p : I, IsUnit ((N : ℕ) : Γ((DY.obj (op p)).obj, ⊤)))
    (S : B.Scheme) (f : cX.pt ⟶ S.obj) (g : ∀ p : I, S ⟶ DY.obj (op p))
    (hsq : ∀ p : I, IsPullback (cX.π.app (op p)) f (B.inclusion.map (φ.app (op p)))
      (B.inclusion.map (g p)))
    (F : EtaleModules.{u, 0} Λ cX.pt)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} cX.pt.smallEtaleTopology Λ F)
    (hNF : N • 𝟙 F = 0) (q : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.obj.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
  have := Stacks.ULiftTransport.isNoetherianRing_ulift (R := Λ)
  let XB := B.obj cX.pt hX
  have : HasSheafify (SmallEtale.topology B cX.pt hX) (ModuleCat.{u + 1} Λ) :=
    smallEtaleHasSheafifyModuleMax B XB Λ
  have : HasWeakSheafify (SmallEtale.topology B cX.pt hX) (ModuleCat.{u + 1} Λ) := inferInstance
  have : ∀ V : SmallEtale B cX.pt hX,
      HasWeakSheafify ((SmallEtale.topology B cX.pt hX).over V) (ModuleCat.{u + 1} Λ) :=
    SmallEtale.hasWeakSheafifyOver_moduleCat_siteUniverse B Λ XB
  have : (SmallEtale.sheafEquiv B cX.pt hX (ModuleCat.{u + 1} Λ)).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let F' := (etaleModulesToSmallEtale B XB Λ).obj F
  have hF' : IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B cX.pt hX) F' :=
    (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B XB Λ F).2 hF
  obtain ⟨p, Fp, hFp, ⟨e⟩⟩ := smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_of_ringEquiv B Λ
    ULift.ringEquiv DX cX hX hcX haff hqc hqs F' hF'
  have hNF' : N • 𝟙 F' = 0 := nsmul_id_eq_zero_obj (etaleModulesToSmallEtale B XB Λ) hNF
  have : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) DX cX hX p).Additive :=
    have := preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{0} B
      (ObjectProperty.homMk (cX.π.app (op p)) : B.obj cX.pt hX ⟶ DX.obj (op p)) Λ
    Functor.additive_of_preserves_binary_products _
  have hproj : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) DX cX hX p).map (N • 𝟙 Fp) =
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) DX cX hX p).map 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero,
      ← cancel_mono e.hom,
      Preadditive.nsmul_comp, Category.id_comp, zero_comp, ← Category.comp_id e.hom,
      ← Preadditive.comp_nsmul, hNF', comp_zero]
  obtain ⟨p', hpp', hp'⟩ := smallEtaleStagesFaithful_isFiniteTypeLocallyConstant_of_ringEquiv B Λ
    ULift.ringEquiv DX cX hX hcX haff hqc hqs p Fp Fp hFp hFp _ _ hproj
  have : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) DX hpp').Additive :=
    have := preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{0} B
      (DX.map (homOfLE hpp').op) Λ
    Functor.additive_of_preserves_binary_products _
  let Fq := (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) DX hpp').obj Fp
  have hNFq : N • 𝟙 Fq = 0 := by
    rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hp'
  have hFq : IsFiniteTypeLocallyConstant Λ _ Fq :=
    isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ _ Fp hFp
  let eq' : (smallEtaleStageProjection B _ DX cX hX p').obj Fq ≅ F' :=
    smallEtaleStageComparison B _ DX cX hX hpp' Fp ≪≫ e
  let Xp := DX.obj (op p')
  let Yp := DY.obj (op p')
  have := hNoeth p'
  have := (hφ p').1
  have := (hφ p').2
  let fp : Xp.obj ⟶ Yp.obj := B.inclusion.map (φ.app (op p'))
  let E := SmallEtale.sheafEquiv B Xp.obj Xp.property (ModuleCat.{u + 1} Λ)
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let Gq : EtaleModules.{u, 0} Λ Xp.obj := E.functor.obj Fq
  have hGq : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} Xp.obj.smallEtaleTopology Λ Gq :=
    (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B Xp Λ Fq).2 hFq
  have hNGq : N • 𝟙 Gq = 0 := nsmul_id_eq_zero_obj E.functor hNFq
  have hstalk : ∀ (x : GeometricPoint Xp.obj)
      (a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ Xp.obj).obj Gq)), N • a = 0 := by
    intro x a
    simpa using ConcreteCategory.congr_hom (nsmul_id_eq_zero_obj (smallEtaleStalkAb x.hom)
      (nsmul_id_eq_zero_obj (etaleModuleForget Λ Xp.obj) hNGq)) a
  have htors : ∀ x : GeometricPoint Xp.obj, ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) ∧
      ∀ a : (smallEtaleStalkAb x.hom).obj ((etaleModuleForget Λ Xp.obj).obj Gq), n • a = 0 :=
    fun x => ⟨N, hN, ringChar_residueField_eq_zero_or_coprime_of_isUnit N
      (isUnit_natCast_of_hom fp (hunit p')) x, hstalk x⟩
  have hGt : IsTorsionEtaleModule Λ Xp.obj Gq :=
    torsionSheafProperty_of_forall_smallEtaleStalkAb _ fun t a => ⟨N, hN, hstalk t a⟩
  have hR :=
    isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_smooth_of_isProper_of_isNoetherian
      fp Λ Gq hGq htors q
  -- the inverse image of `G_q` to `X` is `F`
  let legB : B.obj cX.pt hX ⟶ Xp := ObjectProperty.homMk (cX.π.app (op p'))
  let e₁ : (etaleModulesToSmallEtale B (B.obj cX.pt hX) Λ).obj
        ((etaleModuleInverseImage.{u, 0} Λ (cX.π.app (op p'))).obj Gq) ≅
      (etaleModulesToSmallEtale B (B.obj cX.pt hX) Λ).obj F :=
    etaleModulesToSmallEtalePullbackIso B Λ legB Gq ≪≫
      (smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) legB).mapIso (E.unitIso.app Fq).symm ≪≫ eq'
  let eF : (etaleModuleInverseImage.{u, 0} Λ (cX.π.app (op p'))).obj Gq ≅ F :=
    (SmallEtale.sheafEquiv B cX.pt hX (ModuleCat.{u + 1} Λ)).inverse.preimageIso e₁
  -- proper base change along `g_{p'}`
  obtain ⟨e₂⟩ := nonempty_inverseImage_rightDerived_iso_of_isProper Λ fp (hsq p') Gq hGt q
  have hpull := isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage Λ
    (B.inclusion.map (g p')) _ hR
  exact ObjectProperty.prop_of_iso _
    (e₂ ≪≫ ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).mapIso eF) hpull

end Stage

/-! ### The affine case -/

section Affine

variable (B : BigEtaleSite.{u}) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]

/-- `N` is invertible on the spectrum of a finitely generated subring of `R` containing an inverse
of `N`. -/
theorem isUnit_natCast_specAdjoinFinsetDiagram_obj {R : Type u} [CommRing R] (N : ℕ) (a : R)
    (ha : (N : R) * a = 1) (t : Finset R) (hat : a ∈ t) :
    IsUnit ((N : ℕ) : Γ((specAdjoinFinsetDiagram R).obj (op t), ⊤)) := by
  let A := Algebra.adjoin ℤ ((t : Finset R) : Set R)
  have hA : IsUnit ((N : ℕ) : A) := by
    refine IsUnit.of_mul_eq_one (b := ⟨a, Algebra.subset_adjoin hat⟩) ?_
    apply Subtype.ext
    simpa using ha
  have h := hA.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  rwa [map_natCast] at h

/-- **Tag 0GLI over the limit of the spectra of the finitely generated subrings of a ring, from a
proper smooth model.** -/
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_properSmooth_model
    (N : ℕ) (hN : 0 < N)
    (R : Type u) [CommRing R] (c₀ : Cone (specAdjoinFinsetDiagram R)) (hc₀ : IsLimit c₀)
    (hY : B.Contains c₀.pt) (X : B.Scheme) (f : X.obj ⟶ c₀.pt) (s : Finset R)
    (P : Over ((specAdjoinFinsetDiagram R).obj (op s))) [IsProper P.hom] [Smooth P.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom]
    (g : X.obj ⟶ P.left) (hsq : IsPullback g f P.hom (c₀.π.app (op s)))
    (a : R) (ha : (N : R) * a = 1) (has : a ∈ s)
    (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.obj.smallEtaleTopology Λ F)
    (hNF : N • 𝟙 F = 0) (q : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} c₀.pt.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
  classical
  have : IsCofiltered (Finset R)ᵒᵖ := isCofiltered_op_of_isFiltered _
  let Φ := finsetAboveToOver R s
  let DXs : (FinsetAbove R s)ᵒᵖ ⥤ Scheme.{u} :=
    Φ ⋙ Scheme.baseChangeDiagram (specAdjoinFinsetDiagram R) (op s) P
  let DYs : (FinsetAbove R s)ᵒᵖ ⥤ Scheme.{u} := Φ ⋙ Over.forget (op s) ⋙ (specAdjoinFinsetDiagram R)
  -- the stages
  have hsqt : ∀ t : (FinsetAbove R s)ᵒᵖ, IsPullback (pullback.snd ((specAdjoinFinsetDiagram R).map
      (Φ.obj t).hom) P.hom)
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom)
          P.hom) P.hom ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) := fun t =>
    (IsPullback.of_hasPullback ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom).flip
  have hlft : ∀ t : (FinsetAbove R s)ᵒᵖ,
      LocallyOfFiniteType (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom)
          P.hom) := fun t =>
    inferInstance
  have hqc : ∀ t : (FinsetAbove R s)ᵒᵖ,
      QuasiCompact (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) := fun t =>
    inferInstance
  have hpr : ∀ t : (FinsetAbove R s)ᵒᵖ,
      IsProper (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) := fun t =>
    inferInstance
  have hsm : ∀ t : (FinsetAbove R s)ᵒᵖ,
      Smooth (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) := fun t =>
    inferInstance
  have hsep : ∀ t : (FinsetAbove R s)ᵒᵖ,
      IsSeparated (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) := fun t =>
    have := hpr t
    inferInstance
  have hYB : ∀ t : (FinsetAbove R s)ᵒᵖ, B.Contains (DYs.obj t) := fun t =>
    B.contains_specAdjoinFinsetDiagram_obj _
  have hXB : ∀ t : (FinsetAbove R s)ᵒᵖ, B.Contains (DXs.obj t) := fun t => by
    have := hlft t
    have := hqc t
    have h := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) (hYB t)
    exact h
  have hXc : ∀ t : (FinsetAbove R s)ᵒᵖ, CompactSpace (DXs.obj t) := fun t => by
    have := hqc t
    have h := QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom)
    exact h
  have hXq : ∀ t : (FinsetAbove R s)ᵒᵖ, QuasiSeparatedSpace (DXs.obj t) := fun t => by
    have := hsep t
    have : QuasiSeparated (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom) :=
      IsSeparated.instQuasiSeparated _
    have h := quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom)
    exact h
  let DX : (FinsetAbove R s)ᵒᵖ ⥤ B.Scheme := ObjectProperty.lift _ DXs hXB
  let DY : (FinsetAbove R s)ᵒᵖ ⥤ B.Scheme := ObjectProperty.lift _ DYs hYB
  let φ : DX ⟶ DY :=
    { app := fun t => ObjectProperty.homMk (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj
        t).hom) P.hom)
      naturality := fun t t' e => B.inclusion.map_injective
        (by exact Scheme.baseChangeDiagram_map_fst (specAdjoinFinsetDiagram R) (op s) P (Φ.map e)) }
  -- the limit cone with vertex `X`
  let c' : Cone DXs := (Scheme.baseChangeCone (specAdjoinFinsetDiagram R) (op s) P c₀).whisker Φ
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv Φ _).symm
    (Scheme.isLimitBaseChangeCone (specAdjoinFinsetDiagram R) (op s) P c₀ hc₀)
  let eX : X.obj ≅ pullback (c₀.π.app (op s)) P.hom := hsq.flip.isoPullback
  let cX : Cone (DX ⋙ B.inclusion) := c'.extend eX.hom
  have hcX : IsLimit cX := IsLimit.ofIsoLimit hc' (Cone.extendIso c' eX.symm)
  have hleg_fst : ∀ t : (FinsetAbove R s)ᵒᵖ,
      cX.π.app t ≫ pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj
          t).hom) P.hom = f ≫ c₀.π.app (Φ.obj t).left := by
    intro t
    exact (Category.assoc _ _ _).trans
      ((congrArg (eX.hom ≫ ·) (Scheme.baseChangeCone_π_fst _ _ _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hsq.flip.isoPullback_hom_fst)))
  have hleg_snd : ∀ t : (FinsetAbove R s)ᵒᵖ,
      cX.π.app t ≫ pullback.snd ((specAdjoinFinsetDiagram R).map (Φ.obj t).hom) P.hom = g := by
    intro t
    exact (Category.assoc _ _ _).trans
      ((congrArg (eX.hom ≫ ·) (Scheme.baseChangeCone_π_snd _ _ _ _ _)).trans
        hsq.flip.isoPullback_hom_snd)
  have hsqs : ∀ t : FinsetAbove R s, IsPullback (cX.π.app (op t)) f
      (pullback.fst ((specAdjoinFinsetDiagram R).map (Φ.obj (op t)).hom) P.hom) (c₀.π.app (Φ.obj
          (op t)).left) := by
    intro t
    refine IsPullback.of_right ?_ (hleg_fst (op t)) (hsqt (op t))
    rwa [hleg_snd, c₀.w]
  have haff : ∀ {t t' : (FinsetAbove R s)ᵒᵖ} (e : t ⟶ t'),
      IsAffineHom (B.inclusion.map (DX.map e)) := fun e =>
    Scheme.isAffineHom_baseChangeDiagram_map (specAdjoinFinsetDiagram R) (op s) P (Φ.map e)
  exact isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_stage B Λ N hN DX DY φ cX X.property
    hcX haff (fun t => hXc (op t)) (fun t => hXq (op t))
    (fun t => isNoetherian_specAdjoinFinsetDiagram_obj R _) (fun t => ⟨hpr (op t), hsm (op t)⟩)
    (fun t => isUnit_natCast_specAdjoinFinsetDiagram_obj N a ha t.1 (t.2 has))
    (B.obj c₀.pt hY) f (fun t => ObjectProperty.homMk (c₀.π.app (op t.1))) hsqs F hF hNF q

/-- **Tag 0GLI over an affine base on which `N` is invertible, for a sheaf killed by `N`.** Let
`S` be affine, `f : X ⟶ S` smooth and proper, `N > 0` invertible on `S` and `F` a finite type,
locally constant sheaf of `Λ`-modules on `X` killed by `N`. Then every `Rᵠ f_* F` is finite type
and locally constant.

`S` is the limit of the spectra `S_t` of the finitely generated subrings of `Γ(S, ⊤)`; `f` is the
base change of a proper smooth `f_t` (Stacks 01ZM, 081F, 0C0C), and the stages may be taken to
contain an inverse of `N`, so that `N` is invertible on the Noetherian `S_t`. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_isAffine (N : ℕ) (hN : 0 < N)
    {X S : B.Scheme} [IsAffine S.obj] (f : X.obj ⟶ S.obj) [IsProper f] [Smooth f]
    (hunit : IsUnit ((N : ℕ) : Γ(S.obj, ⊤))) (F : EtaleModules.{u, 0} Λ X.obj)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} X.obj.smallEtaleTopology Λ F)
    (hNF : N • 𝟙 F = 0) (q : ℕ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} S.obj.smallEtaleTopology Λ
      (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
  classical
  obtain ⟨j, Y₀, h₀, q', hpr, hsm, hpb⟩ :=
    HodgeSpreadingOut.exists_isPullback_affineStageCone_properSmooth f
  let a : Γ(S.obj, ⊤) := ↑hunit.unit⁻¹
  have ha : ((N : ℕ) : Γ(S.obj, ⊤)) * a = 1 := hunit.mul_val_inv
  let s : Finset Γ(S.obj, ⊤) := insert a j.unop
  let D := specAdjoinFinsetDiagram Γ(S.obj, ⊤)
  let c₀ := affineStageCone S.obj
  let k : op s ⟶ j := (homOfLE (Finset.subset_insert a j.unop)).op
  have hsq0 : IsPullback (pullback.fst h₀ (D.map k)) (pullback.snd h₀ (D.map k)) h₀ (D.map k) :=
    IsPullback.of_hasPullback h₀ (D.map k)
  let P : Over (D.obj (op s)) := Over.mk (pullback.snd h₀ (D.map k))
  have : IsProper P.hom := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsProper) hsq0 hpr
  have : Smooth P.hom := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Smooth) hsq0 hsm
  have hw : c₀.π.app (op s) ≫ D.map k = c₀.π.app j := c₀.w k
  have hcond : q' ≫ h₀ = (f ≫ c₀.π.app (op s)) ≫ D.map k :=
    hpb.w.trans ((congrArg (f ≫ ·) hw.symm).trans (Category.assoc _ _ _).symm)
  let g : X.obj ⟶ P.left := pullback.lift q' (f ≫ c₀.π.app (op s)) hcond
  have hsq : IsPullback g f P.hom (c₀.π.app (op s)) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hsq0
    rw [pullback.lift_fst]
    exact hw.symm ▸ hpb
  exact isFiniteTypeLocallyConstantModuleSheaf_rightDerived_of_properSmooth_model B Λ N hN
    Γ(S.obj, ⊤) c₀ (isLimit_affineStageCone S.obj) S.property X f s P g hsq a ha
    (Finset.mem_insert_self a j.unop) F hF hNF q

end Affine

end Stacks.EtaleCohomology

end
