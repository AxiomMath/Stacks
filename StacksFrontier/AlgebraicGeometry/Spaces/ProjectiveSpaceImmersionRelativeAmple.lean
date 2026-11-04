module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleCompositionThreshold
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleAssociatedModulePicard
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsLocallyProjective

/-!
# The twist of a closed immersion into projective space is relatively ample

Let `Y` be an algebraic space over a scheme `S`, let `ℙⁿ_Y = Y ×_S ℙⁿ_S` and let `i : X ⟶ ℙⁿ_Y`
be a closed immersion, as recorded by `AlgebraicGeometry.Space.ProjectiveSpaceImmersion`. The
twist `L = i^* 𝒪_{ℙⁿ_Y}(1)` is an invertible `𝒪_X`-module, ample relative to `X ⟶ Y`.

## Main results

* `AlgebraicGeometry.Space.isInvertible_representedAssociatedModule`: an invertible module on a
  scheme gives an invertible module on the algebraic space it represents.
* `AlgebraicGeometry.Space.baseChangeModuleRepresentedAssociatedModuleIso`: the reading, along a
  morphism of schemes `U ⟶ P`, of the module a quasi-coherent `𝒪_P`-module defines on the
  algebraic space of `P` is its pullback to `U`.
* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.isInvertible_twist`: the twist
  `i^* 𝒪_{ℙⁿ_Y}(1)` is invertible.
* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.isRelativelyAmple_twist`: the twist
  `i^* 𝒪_{ℙⁿ_Y}(1)` is ample relative to `X ⟶ Y`.

## References

* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The module an invertible `𝒪_U`-module on a scheme `U` defines on the small étale site of the
algebraic space `U` represents is invertible. -/
theorem isInvertible_representedAssociatedModule (U : BigFppfOver B S hS)
    (F : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hF : Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj U).presheaf
      (_root_.AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf
        ((BigFppfOver.toScheme B S hS).obj U)) F) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (schemeSpace U).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace U).1
          (schemeSpace U).2).O)).property ((representedAssociatedModule B S hS U
          (isAlgebraicSpace_yoneda B S hS U)).obj F) := by
  have h₀ := _root_.AlgebraicGeometry.SmallEtale.isInvertible_associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property F hF
  have h₁ : HasWeakSheafify (SmallEtale.topology B S hS (yoneda.obj U)) AddCommGrpCat.{u} :=
    inferInstance
  have h₂ : (SmallEtale.topology B S hS (yoneda.obj U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  exact @Stacks.SheafOfModules.Picard.isInvertible_map_obj _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
    (_root_.AlgebraicGeometry.SmallEtale.structure_isSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    _ _ _ _ (SmallEtale.topology B S hS (yoneda.obj U))
    (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
    (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    h₂ h₁
    (representedSmallEtaleModuleEquivalence B S hS U).functor (Iso.refl _)
    (fun M N => representedSmallEtaleModuleTensorIso B S hS U M N) _ h₀

/-- The reading on a scheme `U` of the module of a quasi-coherent module on a scheme `P`, along
the morphism `U ⟶ P`, is its pullback. -/
def baseChangeModuleRepresentedAssociatedModuleIso (P U : BigFppfOver B S hS)
    (F : ((BigFppfOver.toScheme B S hS).obj P).Modules) (hF : F.IsQuasicoherent) (φ : U ⟶ P) :
    baseChangeModule B S hS (X := schemeSpace P)
        ((representedAssociatedModule B S hS P (isAlgebraicSpace_yoneda B S hS P)).obj F) U
          (yoneda.map φ) ≅
      Stacks.AmpleLocallyClosed.pullbackModule ((BigFppfOver.toScheme B S hS).map φ) F :=
  restrictToChartSchemeBaseChangeIso φ _
      (isQuasicoherentOnSite_representedAssociatedModule B S hS P (isAlgebraicSpace_yoneda B S hS P)
          F
        hF) ≪≫
    (RingedSpaceModuleAdjunction.modulePullback
      ((BigFppfOver.toScheme B S hS).map φ).toLRSHom.toShHom).mapIso
      (restrictToChartSchemeRepresentedAssociatedModuleIso B S hS P F hF)

namespace ProjectiveSpaceImmersion

variable {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)} {X Y : AlgebraicSpaces B S hS}

/-- The twist `L = i^* 𝒪_{ℙⁿ_Y}(1)` of a closed immersion into projective space is invertible. -/
theorem isInvertible_twist (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
          D.twist :=
  isInvertible_modulePullback B S hS D.imm _ (hL := isInvertible_modulePullback B S hS D.coord _
    (hL := isInvertible_representedAssociatedModule (projectiveSpaceSiteObj B S hS n hP) _
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
        (inferInstanceAs (Stacks.Ample.IsInvertibleModule (projectiveSpaceOver n S)
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S))))))

/-- **The twist `i^* 𝒪_{ℙⁿ_Y}(1)` is ample relative to `X ⟶ ℙⁿ_Y ⟶ Y`.** -/
theorem isRelativelyAmple_twist (D : ProjectiveSpaceImmersion B S hS n hP X Y) :
    IsRelativelyAmple B S hS D.hom D.twist := by
  refine ⟨D.relativelyRepresentable_hom, fun T U gT p q hsq => ?_⟩
  set P := projectiveSpaceSiteObj B S hS n hP
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj P)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S) :=
    inferInstanceAs (Stacks.Ample.IsInvertibleModule (projectiveSpaceOver n S)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S))
  have hT₀ : IsTerminal (baseSiteObj B S hS) := Over.mkIdTerminal
  have hterm : ∀ {W : BigFppfOver B S hS} (a b : yoneda.obj W ⟶ yoneda.obj (baseSiteObj B S hS)),
      a = b := fun a b => by
    rw [← yoneda.map_preimage a, ← yoneda.map_preimage b, hT₀.hom_ext (yoneda.preimage a)
      (yoneda.preimage b)]
  set φ : U ⟶ P := yoneda.preimage (p ≫ D.imm.hom ≫ D.coord.hom)
  have hφ : yoneda.map φ = p ≫ D.imm.hom ≫ D.coord.hom := yoneda.map_preimage _
  have hQ : IsPullback (prod.fst : P ⨯ T ⟶ P) (prod.snd : P ⨯ T ⟶ T) (hT₀.from P)
      (hT₀.from T) := IsPullback.of_is_product (prodIsProd P T) hT₀
  set g : yoneda.obj (P ⨯ T) ⟶ D.projSpace.1 :=
    D.isPullback.lift (yoneda.map prod.snd ≫ gT) (yoneda.map prod.fst) (hterm _ _)
  have hg₁ : g ≫ D.proj.hom = yoneda.map prod.snd ≫ gT := D.isPullback.lift_fst _ _ _
  have hg₂ : g ≫ D.coord.hom = yoneda.map prod.fst := D.isPullback.lift_snd _ _ _
  have hbot : IsPullback g (yoneda.map (prod.snd : P ⨯ T ⟶ T)) D.proj.hom gT := by
    refine IsPullback.of_right ?_ hg₁ D.isPullback.flip
    have h := hQ.map yoneda
    rw [hterm (yoneda.map (hT₀.from T)) (gT ≫ D.base.hom),
      hterm (yoneda.map (hT₀.from P))
        (schemeSpaceMap (projectiveSpaceSiteObjToBase B S hS n hP)).hom] at h
    rwa [hg₂]
  set i₀ : U ⟶ P ⨯ T := prod.lift φ q
  have htop : IsPullback p (yoneda.map i₀) D.imm.hom g := by
    refine IsPullback.of_bot ?_ ?_ hbot
    · rwa [← Functor.map_comp, prod.lift_snd]
    · refine D.isPullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hg₁]
        rw [← Category.assoc (yoneda.map i₀), ← Functor.map_comp, prod.lift_snd]
        exact hsq.w
      · simp only [Category.assoc, hg₂]
        rw [← hφ]
        exact ((yoneda.map_comp i₀ prod.fst).symm.trans
          (congrArg yoneda.map (prod.lift_fst φ q))).symm
  have hcl : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i₀) :=
    D.imm_isClosedImmersion.2 g p i₀ htop
  have e₁ : baseChangeModule B S hS D.twist U p ≅
      baseChangeModule B S hS (X := schemeSpace P)
        ((representedAssociatedModule B S hS P (isAlgebraicSpace_yoneda B S hS P)).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) U (yoneda.map φ) :=
    (baseChangeModuleCompIso B S hS D.imm D.twistOne U p).symm ≪≫
      (baseChangeModuleCompIso B S hS D.coord _ U (p ≫ D.imm.hom)).symm ≪≫
      eqToIso (congrArg (baseChangeModule B S hS (X := schemeSpace P)
        ((representedAssociatedModule B S hS P (isAlgebraicSpace_yoneda B S hS P)).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) U)
        (by rw [hφ, Category.assoc]))
  have e₂ := baseChangeModuleRepresentedAssociatedModuleIso P U
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _) φ
  have e₃ := Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
      (show (BigFppfOver.toScheme B S hS).map φ =
        (BigFppfOver.toScheme B S hS).map i₀ ≫ (BigFppfOver.toScheme B S hS).map prod.fst by
          rw [← Functor.map_comp, prod.lift_fst])
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S) ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ _
  have hPS : (BigFppfOver.toScheme B S hS).map (hT₀.from P) = projectiveSpaceOver n S ↘ S := by
    rw [hT₀.hom_ext (hT₀.from P) (projectiveSpaceSiteObjToBase B S hS n hP)]; rfl
  have hQ' := hQ.map (BigFppfOver.toScheme B S hS)
  rw [hPS] at hQ'
  have hMQ := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback
    hQ'
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)
    (Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf n S)
  have hsnd : QuasiCompact ((BigFppfOver.toScheme B S hS).map (prod.snd : P ⨯ T ⟶ T)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hQ'
      (inferInstanceAs (QuasiCompact (projectiveSpaceOver n S ↘ S)))
  have hiq : (BigFppfOver.toScheme B S hS).map i₀ ≫
      (BigFppfOver.toScheme B S hS).map (prod.snd : P ⨯ T ⟶ T) =
        (BigFppfOver.toScheme B S hS).map q := by rw [← Functor.map_comp, prod.lift_snd]
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q) := by
    rw [← hiq]; infer_instance
  have := isInvertibleModule_baseChangeModule D.twist D.isInvertible_twist U p
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj (P ⨯ T))
      (Stacks.AmpleLocallyClosed.pullbackModule ((BigFppfOver.toScheme B S hS).map prod.fst)
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ _
  have := Stacks.InvertiblePullback.isInvertibleModule_pullback
    ((BigFppfOver.toScheme B S hS).map i₀)
    (Stacks.AmpleLocallyClosed.pullbackModule ((BigFppfOver.toScheme B S hS).map prod.fst)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S))
  refine ⟨inferInstance, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
    (e₁ ≪≫ e₂ ≪≫ e₃)).mpr ?_⟩
  exact Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion
    Stacks.SectionExtension.amplePullbackGap _ _ hqc
    ⟨_, _, _, inferInstance, (BigFppfOver.toScheme B S hS).map i₀, inferInstance, hiq, hMQ,
      ⟨Iso.refl _⟩⟩

end ProjectiveSpaceImmersion

end AlgebraicGeometry.Space

end
