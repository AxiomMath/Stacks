module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.IsomorphismStageOfCutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsColimitOfCutoffBoundedSystem

/-!
# An affine limit of a system bounded by the cutoff has an affine stage

Stacks 07SQ: in the situation of Stacks 084R, if the limit `X = lim Xᵢ` is affine, then so is some
`Xᵢ`. This file proves it over the integers for a descent situation whose system is bounded by the
cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no condition on the cofinality of
the site's cutoff.

## Main results

* `AlgebraicGeometry.Space.isIso_pullbackMap_of_isPullback`: a base change to the limit is an
  isomorphism when source and target are fibre products over one cospan.
* `AlgebraicGeometry.Space.isAffineSpace_obj_of_isIso_pullbackMap`: a stage is affine once the
  base change of the morphism there is an isomorphism.
* `DescentSituation.exists_isAffineSpace_system_obj_of_isTerminal_of_isCutoffBoundedSystem`:
  Stacks 07SQ over a terminal base for a system bounded by the cutoff.
* `DescentSituation.exists_isAffineSpace_system_obj_of_isCutoffBoundedSystem`:
  Stacks 07SQ over the integers for a system bounded by the cutoff.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

section MapLimit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A base change to the limit is an isomorphism when source and target are exhibited as fibre
products over one cospan, for an unbundled inverse system. Let `f₀ : X₀ ⟶ Y₀` be a morphism
over the stage `D i₀`, suppose `Y₀` is the fibre product of `D i₀` with `W` over `Z`, and suppose
the base change of `X₀` to the limit is the fibre product of the limit with `W` over `Z` through
`f₀` followed by the projection to `W`. Then the base change of `f₀` to the limit is an
isomorphism. -/
theorem isIso_pullbackMap_of_isPullback {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₀ : I)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : D.obj (op i₀) ⟶ Z) (aW : W ⟶ Z)
    (q : Y₀ ⟶ W) (hq : IsPullback y q pZ aW) (cS : X₀ ⟶ W) (hcS : f₀ ≫ q = cS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {α : P ⟶ limit D} {γ : P ⟶ X₀}
    (hPstage : IsPullback α γ (limit.π D (op i₀)) x)
    (hP : IsPullback α (γ ≫ cS) (limit.π D (op i₀) ≫ pZ) aW) :
    IsIso (pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y (𝟙 _) f₀ (𝟙 _)
      (by simp) (by simp [hf₀])) := by
  have htgt : IsPullback (pullback.fst (limit.π D (op i₀)) y)
      (pullback.snd (limit.π D (op i₀)) y ≫ q) (limit.π D (op i₀) ≫ pZ) aW :=
    (((IsPullback.of_hasPullback (limit.π D (op i₀)) y).flip.paste_horiz hq.flip)).flip
  have hsrc : IsPullback (pullback.fst (limit.π D (op i₀)) x)
      (pullback.snd (limit.π D (op i₀)) x ≫ cS) (limit.π D (op i₀) ≫ pZ) aW := by
    refine hP.of_iso (hPstage.isoIsPullback _ _
      (IsPullback.of_hasPullback (limit.π D (op i₀)) x))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans
        (IsPullback.isoIsPullback_hom_fst _ _ hPstage _).symm
    · exact (Category.comp_id _).trans
        ((congrArg (fun z ↦ z ≫ cS)
          (IsPullback.isoIsPullback_hom_snd _ _ hPstage _).symm).trans
          (Category.assoc _ _ _))
    · simp
    · simp
  have hmap : pullback.map (limit.π D (op i₀)) x (limit.π D (op i₀)) y (𝟙 _) f₀ (𝟙 _)
      (by simp) (by simp [hf₀]) = (hsrc.isoIsPullback _ _ htgt).hom := by
    refine htgt.hom_ext ?_ ?_
    · rw [IsPullback.isoIsPullback_hom_fst]
      simp
    · rw [IsPullback.isoIsPullback_hom_snd, ← hcS]
      simp
  rw [hmap]
  infer_instance

/-- A stage is affine once the base change of the morphism there is an isomorphism, for an
unbundled inverse system. Suppose `Y₀` is the fibre product of the stage `D i₀` with an affine
object `W` of the site over an affine algebraic space `Z`, the morphism `h_W ⟶ Z` being surjective
and étale. If the base change of `f₀ : X₀ ⟶ Y₀` to a stage `k` is an isomorphism and the base
change of `X₀` there is affine, then `D k` is an affine algebraic space. -/
theorem isAffineSpace_obj_of_isIso_pullbackMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i))) (i₀ : I)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : D.obj (op i₀) ⟶ Z)
    {W : BigFppfOver B S hS} (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (aW : yoneda.obj W ⟶ Z) (haWsurj : IsSurjective B S hS aW)
    (haWetale : IsEtale B S hS aW) (hZalg : IsAlgebraicSpace B S hS Z)
    (hZaff : IsAffineSpace B S hS Z) (q : Y₀ ⟶ yoneda.obj W)
    (hq : IsPullback y q pZ aW) {k : I} (hk : i₀ ≤ k)
    (hsrcAff : IsAffineSpace B S hS (pullback (D.map (homOfLE hk).op) x))
    (hkiso : IsIso (pullback.map (D.map (homOfLE hk).op) x (D.map (homOfLE hk).op) y (𝟙 _) f₀
      (𝟙 _) (by simp) (by simp [hf₀]))) :
    IsAffineSpace B S hS (D.obj (op k)) := by
  have htgtAff : IsAffineSpace B S hS (pullback (D.map (homOfLE hk).op) y) :=
    hsrcAff.of_iso (@asIso _ _ _ _ _ hkiso)
  have h4 : IsPullback (pullback.fst (D.map (homOfLE hk).op) y)
      (pullback.snd (D.map (homOfLE hk).op) y ≫ q) (D.map (homOfLE hk).op ≫ pZ) aW :=
    (((IsPullback.of_hasPullback (D.map (homOfLE hk).op) y).flip.paste_horiz hq.flip)).flip
  have hpbAff : IsAffineSpace B S hS (pullback (D.map (homOfLE hk).op ≫ pZ) aW) :=
    htgtAff.of_iso (h4.isoIsPullback _ _
      (IsPullback.of_hasPullback (D.map (homOfLE hk).op ≫ pZ) aW))
  exact (isAffineHom_of_isAffineSpace_pullback_of_etaleChart B S hS (hDalg k) hZalg
    (D.map (homOfLE hk).op ≫ pZ) hW aW haWsurj haWetale hpbAff).isAffineSpace_source hZaff

/-- Stacks 07SQ around Stacks 084S, for a system bounded by the cutoff. Let `f₀ : X₀ ⟶ Y₀`
be a morphism over a stage `D i₀` of a directed system bounded by the cutoff, between
quasi-compact and quasi-separated algebraic spaces, locally of finite presentation, with `X₀`
affine. Suppose its base change to the limit is exhibited as an isomorphism by two fibre
products over one cospan (`AlgebraicGeometry.Space.isIso_pullbackMap_of_isPullback`), and `Y₀` is
the fibre product of `D i₀` with an affine object `W'` of the site, étale and surjective over an
affine algebraic space `Z`. Then some stage `D k` with `i₀ ≤ k` is an affine algebraic space. -/
theorem exists_isAffineSpace_obj_of_isPullback_of_isCutoffBoundedSystem
    (hZ : B.Contains (⊤_ Scheme.{u})) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hDc : IsCutoffBoundedSystem B S hS D)
    (hDalg : ∀ i : I, IsAlgebraicSpace B S hS (D.obj (op i)))
    (hDaff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) (i₀ : I)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X₀ ⟶ D.obj (op i₀))
    (y : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ y = x)
    (hX₀ : IsAlgebraicSpace B S hS X₀) (hY₀ : IsAlgebraicSpace B S hS Y₀)
    (hX₀aff : IsAffineSpace B S hS X₀)
    (hX₀qc : IsQuasiCompactSpace B S hS X₀) (hY₀qc : IsQuasiCompactSpace B S hS Y₀)
    (hX₀qs : IsAbsolutelyQuasiSeparated B S hS hZ X₀)
    (hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀)
    (hfp : IsLocallyOfFinitePresentation B S hS f₀)
    {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : D.obj (op i₀) ⟶ Z) (aW : W ⟶ Z)
    (q : Y₀ ⟶ W) (hq : IsPullback y q pZ aW) (cS : X₀ ⟶ W) (hcS : f₀ ≫ q = cS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {α : P ⟶ limit D} {γ : P ⟶ X₀}
    (hPstage : IsPullback α γ (limit.π D (op i₀)) x)
    (hP : IsPullback α (γ ≫ cS) (limit.π D (op i₀) ≫ pZ) aW)
    {W' : BigFppfOver B S hS} (hW' : IsAffine ((BigFppfOver.toScheme B S hS).obj W'))
    (aW' : yoneda.obj W' ⟶ Z) (haWsurj : IsSurjective B S hS aW')
    (haWetale : IsEtale B S hS aW') (hZalg : IsAlgebraicSpace B S hS Z)
    (hZaff : IsAffineSpace B S hS Z) (q' : Y₀ ⟶ yoneda.obj W') (hq' : IsPullback y q' pZ aW') :
    ∃ k, i₀ ≤ k ∧ IsAffineSpace B S hS (D.obj (op k)) := by
  obtain ⟨k, hk, hkiso⟩ := exists_isIso_pullbackMap_of_isCutoffBoundedSystem B S hS hZ D hDc
    hDalg hDaff i₀ x y f₀ hf₀ hX₀ hY₀ hX₀qc hY₀qc hX₀qs hY₀qs hfp
    (isIso_pullbackMap_of_isPullback D i₀ x y f₀ hf₀ pZ aW q hq cS hcS hPstage hP)
  refine ⟨k, hk, isAffineSpace_obj_of_isIso_pullbackMap D hDalg i₀ x y f₀ hf₀ pZ hW' aW'
    haWsurj haWetale hZalg hZaff q' hq' hk ?_ hkiso⟩
  exact (IsAffineHom.of_isPullback (IsPullback.of_hasPullback (D.map (homOfLE hk).op) x)
    (hDaff _)).isAffineSpace_source hX₀aff

end MapLimit

namespace DescentSituation

section ModelSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- Stacks 07SI for the structure sheaf, read on `u`-models, for a system bounded by the cutoff:
the global functions of the limit are the colimit of the global functions of the stages. -/
theorem isStagesColimit_globalFunctionsModel_of_isCutoffBoundedSystem
    (hDc : IsCutoffBoundedSystem B S hS D.system) :
    Stacks.IsStagesColimit
      (G := fun i : I ↦ globalFunctionsModel B S hS (D.stage i))
      (T := globalFunctionsModel B S hS D.limitSpace)
      (fun i j (h : i ≤ j) x ↦ (stageModelEquiv D j).symm
        (globalFunctionsMap B S hS (D.transition h) (stageModelEquiv D i x)))
      (fun i x ↦ (limitModelEquiv D).symm
        (globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i x))) := by
  obtain ⟨hphi, hsurj, hzero⟩ :=
    D.ringPackage_of_isGlobalFunctionsColimit
      (D.isGlobalFunctionsColimit_of_isCutoffBoundedSystem hDc)
  refine ⟨?_, ?_, ?_⟩
  · intro i j h x
    simp only [RingEquiv.apply_symm_apply]
    rw [hphi]
  · intro t
    obtain ⟨i, s, hs⟩ := hsurj (limitModelEquiv D t)
    refine ⟨i, (stageModelEquiv D i).symm s, ?_⟩
    simp only [RingEquiv.apply_symm_apply]
    rw [hs, RingEquiv.symm_apply_apply]
  · intro i s s' hss
    have h0 : globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i s)
        = globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i s') :=
      (limitModelEquiv D).symm.injective hss
    obtain ⟨j, hij, hj⟩ :=
      Stacks.IsStagesColimit.exists_trans_eq
        (D.isGlobalFunctionsColimit_of_isCutoffBoundedSystem hDc) i _ _ h0
    exact ⟨j, hij, congrArg (stageModelEquiv D j).symm hj⟩

/-- Stacks 07SI for the structure sheaf on the `u`-models, for a system bounded by the cutoff,
with both families read as ring homomorphisms. -/
theorem isStagesColimit_modelProjection_of_isCutoffBoundedSystem
    (hDc : IsCutoffBoundedSystem B S hS D.system) :
    Stacks.IsStagesColimit (fun i j (h : i ≤ j) x ↦ D.modelTransition i j h x)
      (fun i x ↦ D.modelProjection i x) :=
  D.isStagesColimit_globalFunctionsModel_of_isCutoffBoundedSystem hDc

section Charts

variable {U₀ : BigAffineFppf B S hS}
  {chart : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.system.obj (op D.base)}
  (C : AffineChartSystem B S hS (op D.base) D.system U₀ chart)
  (hchart : IsEtaleChart B S hS (D.system.obj (op D.base)) (CostructuredArrow.mk chart))

/-- Stacks 07SQ, from the square of Stacks 084U at a stage, for a system bounded by the cutoff:
given a presentation at the stage `m` whose square with the limit chart is a fibre product, some
stage at or beyond `m` is an affine algebraic space. -/
theorem exists_isAffineSpace_system_obj_of_isPullback_of_isCutoffBoundedSystem
    (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hDc : IsCutoffBoundedSystem B S hS D.system)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    {p : (D.stage m.1).obj ⟶ schemePoints B S hS
      (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))}
    (hsq : (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom ≫ p
      = yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
          (coordinateHom g' (D.stageChartHom C hchart m) y hyrel))
        ≫ schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
    (hsrcPB : IsPullback L.toLimit
      (yoneda.map (L.cone.π.app
          ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
        ≫ yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
            (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)))
      (limit.π D.system (op m.1) ≫ p)
      (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    (hCont : B.Contains (Spec (CommRingCat.of (presentationAlgebra g'))))
    (haWsurj : IsSurjective B S hS ((schemePointsIso B S hS hterminal hCont).hom ≫
      schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    (haWetale : IsEtale B S hS ((schemePointsIso B S hS hterminal hCont).hom ≫
      schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    (hfpres : RingHom.FinitePresentation (presentationStructureHom g')) :
    ∃ i, m.1 ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  have ha : IsEtale B S hS (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      (D.toLimitSituation.stagesEtaleChart C hchart m).property
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))) :=
    C.isAffine_obj _
  have hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))) :=
    Scheme.compactSpace_of_isAffine _
  have hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))) :=
    inferInstance
  have hY₀alg : IsAlgebraicSpace B S hS (pullback p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))) :=
    isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS
      (CommRingCat.ofHom (presentationStructureHom g'))
      (RingHom.FiniteType.of_finitePresentation hfpres) (D.algebraicSpace m.1) p
  have hX₀fp : IsFinitePresentation B S hS
      (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom :=
    isFinitePresentation_etaleChart B S hS hZ (D.algebraicSpace m.1)
      (D.quasiSeparated m.1) hUqc hUqs ha
  have hY₀fp : IsFinitePresentation B S hS (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))) :=
    isFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS
      (CommRingCat.ofHom (presentationStructureHom g')) hfpres (D.algebraicSpace m.1) p
  have hf₀ := pullback.lift_fst (f := p) (g := schemePointsMap B S hS
    (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) _ _ hsq
  have hfp := isLocallyOfFinitePresentation_of_comp B S hS
    (isAlgebraicSpace_yoneda B S hS _) hY₀alg (D.algebraicSpace m.1) (pullback.lift _ _ hsq)
    (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
    ((congrArg (IsLocallyOfFinitePresentation B S hS) hf₀).mpr hX₀fp.1)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hY₀fp.1)
  have hZaff : IsAffineSpace B S hS (schemePoints B S hS
      (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))) :=
    isAffineSpace_schemePoints B S hS hterminal
      (contains_spec_globalFunctionsModel B S hS (D.stage m.1))
  have hqSq : IsPullback (pullback.fst p (schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))))
      (pullback.snd p (schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
        ≫ (schemePointsIso B S hS hterminal hCont).inv) p
      ((schemePointsIso B S hS hterminal hCont).hom ≫ schemePointsMap B S hS
        (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) := by
    refine (IsPullback.of_hasPullback p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))).of_iso (Iso.refl _)
      (Iso.refl _) (schemePointsIso B S hS hterminal hCont).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · simp
  exact exists_isAffineSpace_obj_of_isPullback_of_isCutoffBoundedSystem hZ D.system hDc
    D.algebraicSpace D.transition_affine m.1 _ _ _ hf₀ (isAlgebraicSpace_yoneda B S hS _)
    hY₀alg (isAffineSpace_yoneda B S hS _ hWaff)
    (isQuasiCompactSpace_of_isFinitePresentation B S hS _ (D.algebraicSpace m.1)
      (D.quasiCompact m.1) hX₀fp)
    (isQuasiCompactSpace_of_isFinitePresentation B S hS _ (D.algebraicSpace m.1)
      (D.quasiCompact m.1) hY₀fp)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (isAlgebraicSpace_yoneda B S hS _)
      (D.quasiSeparated m.1) hX₀fp.2.2)
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hY₀alg (D.quasiSeparated m.1)
      hY₀fp.2.2)
    hfp p
    (schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
    (pullback.snd p _) (IsPullback.of_hasPullback p _)
    (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
      (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)))
    (pullback.lift_snd _ _ _)
    (L.isPullback_stage
      ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
    hsrcPB
    (show IsAffine ((BigFppfOver.toScheme B S hS).obj
        (terminalSiteObject B S hS hterminal hCont)) by
      rw [toScheme_terminalSiteObject]; infer_instance)
    ((schemePointsIso B S hS hterminal hCont).hom ≫ schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
    haWsurj haWetale hZaff.isAlgebraicSpace hZaff _ hqSq

/-- Stacks 07SQ, from a presentation at a stage, for a system bounded by the cutoff: if the limit
is affine and an étale presentation with surjective spectrum at the stage `m` becomes, over the
limit, a presentation of the global functions of the limit chart, then some stage at or beyond `m`
is an affine algebraic space. -/
theorem exists_isAffineSpace_system_obj_of_presentation_of_isCutoffBoundedSystem
    (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hchartSurj : IsSurjective B S hS chart)
    (hDc : IsCutoffBoundedSystem B S hS D.system) (hX : IsAffineSpace B S hS D.limitSpace.obj)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hyt : ∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
      (op m)).appTop).hom (y k) = t k)
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      ((fun k ↦ MvPolynomial.map (D.modelProjection m.1) (g' k)) l) = 0)
    (hbij : Function.Bijective
      (coordinateHom (fun k ↦ MvPolynomial.map (D.modelProjection m.1) (g' k))
        (D.limitChartHom C hchart L) t hrel))
    (hg'E : Algebra.Etale (globalFunctionsModel B S hS (D.stage m.1))
      (presentationAlgebra g'))
    (hg'S : Function.Surjective (PrimeSpectrum.comap (presentationStructureHom g'))) :
    ∃ i, m.1 ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  obtain ⟨p, hp⟩ := exists_specMap_of_globalHom B S hS (D.stage m.1)
    (globalFunctionsModel B S hS (D.stage m.1))
    (globalFunctionsModelEquiv B S hS (D.stage m.1)).toRingHom
  obtain ⟨pA, hpAiso, hpA⟩ := exists_isIso_specMapOfGlobalHom_of_isAffineSpace B S hS hterminal
    D.limitSpace (globalFunctionsModel B S hS D.limitSpace)
    (contains_spec_globalFunctionsModel B S hS D.limitSpace)
    (globalFunctionsModelEquiv B S hS D.limitSpace) hX
  have hfpres : RingHom.FinitePresentation (presentationStructureHom g') :=
    finitePresentation_presentationStructureHom g'
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})).mpr
      (RingHom.FiniteType.of_finitePresentation hfpres)
  have hetaleSpec : AlgebraicGeometry.Etale
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale.{u})).mpr
      (RingHom.etale_algebraMap.mpr hg'E)
  have hsurjSpec : AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))) := ⟨hg'S⟩
  have haaEtale : IsEtale B S hS (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) :=
    isEtale_of_presheaf_etale B S hS (presheaf_inverseImage_schemePointsMap B S hS
      (@AlgebraicGeometry.Etale.{u}) _ hetaleSpec)
  have haaSurj : IsSurjective B S hS (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g')))) :=
    isSurjective_of_presheafSurjective B S hS _ (presheaf_inverseImage_schemePointsMap B S hS
      (@AlgebraicGeometry.Surjective.{u}) _ hsurjSpec)
  have : Algebra.FinitePresentation (globalFunctionsModel B S hS (D.stage m.1))
      (presentationAlgebra g') := Algebra.FinitePresentation.quotient (fg_span_range g')
  have : Algebra.FiniteType (globalFunctionsModel B S hS (D.stage m.1))
      (presentationAlgebra g') := inferInstance
  have hCont : B.Contains (Spec (CommRingCat.of (presentationAlgebra g'))) :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (globalFunctionsModel B S hS (D.stage m.1)) (presentationAlgebra g')
      (contains_spec_globalFunctionsModel B S hS (D.stage m.1))
  exact D.exists_isAffineSpace_system_obj_of_isPullback_of_isCutoffBoundedSystem C hchart L
    hterminal hDc m g' y hyrel
    (commSq_chart_specOfGlobalFunctions B S hS (D.stage m.1)
      (D.toLimitSituation.stagesEtaleChart C hchart m)
      (globalFunctionsModel B S hS (D.stage m.1))
      (globalFunctionsModelEquiv B S hS (D.stage m.1)) g' y hyrel p
      (hp (D.toLimitSituation.stagesEtaleChart C hchart m)))
    (D.isPullback_toLimit_coordinateHom C hchart L hterminal hchartSurj m g' y hyrel t hyt
      hrel hbij hpAiso (hpA (D.toLimitSituation.limitEtaleChart C L hchart))
      (hp (D.toLimitSituation.stagesEtaleChart C hchart m)))
    hCont
    (isSurjective_comp B S hS
      (isSurjective_of_isIso B S hS (schemePointsIso B S hS hterminal hCont).hom) haaSurj)
    (isEtale_comp B S hS
      (isEtale_of_isIso B S hS (schemePointsIso B S hS hterminal hCont).hom) haaEtale)
    hfpres

/-- The coordinates and the relations of a presentation over the limit descend to a single
stage, for a system bounded by the cutoff. -/
theorem exists_ge_eval₂_map_eq_zero_of_isCutoffBoundedSystem
    (L : AffineChartSystem.LimitBridge C)
    (hDc : IsCutoffBoundedSystem B S hS D.system) (j₀ : D.toLimitSituation.Stages) {n : ℕ}
    (q : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage j₀.1)))
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      (MvPolynomial.map (D.modelProjection j₀.1) (q l)) = 0) :
    ∃ (m : D.toLimitSituation.Stages) (hm : j₀ ≤ m)
      (y : Fin n →
        Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤)),
      (∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
          (op m)).appTop).hom (y k) = t k) ∧
      ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l)) = 0 := by
  have : IsDirectedOrder I := inferInstance
  have hds := D.directedSystem_appTop_stagesSchemeDiagram C
  have hdsm := D.directedSystem_modelTransition
  have hcol := LimitSituation.isStagesColimit_chartAppTop D.toLimitSituation C L
  have hmodel := D.isStagesColimit_modelProjection_of_isCutoffBoundedSystem hDc
  obtain ⟨m, hm, y, hy⟩ := Ring.exists_ge_forall_eq_of_directed hcol.hφ hcol.hsurj t j₀
  have hvanish : ∀ l,
      ((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app (op m)).appTop).hom)
        (MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
          (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))) = 0 := by
    intro l
    rw [MvPolynomial.hom_eval₂]
    have h2 : ((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
            (op m)).appTop).hom).comp (D.stageChartHom C hchart m)
        = (D.limitChartHom C hchart L).comp (D.modelProjection m.1) :=
      RingHom.ext fun z ↦ D.appTop_stagesSchemeCone_π_stageChartHom C hchart L m z
    have h3 : (fun k ↦ (((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
        (op m)).appTop).hom)) (y k)) = t := funext hy
    rw [h2, h3]
    have h4 := MvPolynomial.eval₂_map (D.modelProjection m.1) t
      (D.limitChartHom C hchart L)
      (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
    have h5 : MvPolynomial.map (D.modelProjection m.1)
          (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
        = MvPolynomial.map (D.modelProjection j₀.1) (q l) :=
      MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q l)
    rw [← h4, h5]
    exact hrel l
  obtain ⟨m', hmm', hm'⟩ :=
    Ring.exists_ge_forall_eq_zero_of_directed hcol.hzero
      (fun l ↦ MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))) hvanish
  refine ⟨m', hm.trans hmm', fun k ↦
    ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
      (homOfLE hmm').op).appTop).hom) (y k),
    fun k ↦ (hcol.hφ m m' hmm' (y k)).trans (hy k), fun l ↦ ?_⟩
  have hmap : MvPolynomial.map (D.modelTransition j₀.1 m'.1 (hm.trans hmm')) (q l)
      = MvPolynomial.map (D.modelTransition m.1 m'.1 hmm')
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l)) :=
    (MvPolynomial.map_map_eq_map_of_directedSystem
      (f := fun i j (h : i ≤ j) ↦ D.modelTransition i j h)
      (show j₀.1 ≤ m.1 from hm) (show m.1 ≤ m'.1 from hmm') (q l)).symm
  have hcomp : ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
          (homOfLE hmm').op).appTop).hom).comp (D.stageChartHom C hchart m)
      = (D.stageChartHom C hchart m').comp (D.modelTransition m.1 m'.1 hmm') :=
    RingHom.ext fun z ↦ D.appTop_stagesSchemeDiagram_map_stageChartHom C hchart hmm' z
  have h6 := MvPolynomial.eval₂_map (D.modelTransition m.1 m'.1 hmm')
    (fun k ↦ ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
      (homOfLE hmm').op).appTop).hom) (y k))
    (D.stageChartHom C hchart m')
    (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
  rw [hmap, h6, ← hcomp, ← MvPolynomial.hom_eval₂]
  exact hm' l

end Charts

/-- Stacks 07SQ over a terminal base, for a system bounded by the cutoff: in the situation of
Stacks 084R over a terminal base scheme, with the system bounded by the cutoff, if the limit is an
affine algebraic space then so is some stage at or beyond the distinguished one. -/
theorem exists_isAffineSpace_system_obj_of_isTerminal_of_isCutoffBoundedSystem
    (hterminal : IsTerminal S) (hDc : IsCutoffBoundedSystem B S hS D.system)
    (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  classical
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (D.system.obj (op D.base)) (D.algebraicSpace D.base)).mp (D.quasiCompact D.base)
  have hchart : IsEtaleChart B S hS (D.system.obj (op D.base)) (CostructuredArrow.mk chart) :=
    (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
  have hchartSurj : IsSurjective B S hS chart :=
    isSurjective_of_presheafSurjective B S hS chart hchartS
  set C := D.toLimitSituation.chartSystem ⟨U₀, hU₀⟩ chart with hCdef
  set L := C.limitBridgeOfBaseChangeSizeBounded hDc.1 hDc.2.1.choose_spec.1
    hDc.2.1.choose_spec.2 hDc.2.2 with hLdef
  obtain ⟨hEt, hSu⟩ := etale_globalFunctionsChartRestriction B S hS hterminal
    D.limitSpace (canonicalGlobalFunctionsModel B S hS D.limitSpace) hX
    (D.toLimitSituation.limitEtaleChart C L hchart) L.isAffine_pt
    (D.toLimitSituation.isSurjective_limitEtaleChart C L hchart hchartSurj)
  have hEt' : RingHom.Etale (D.limitChartHom C hchart L) := hEt
  have hSu' : Function.Surjective (PrimeSpectrum.comap (D.limitChartHom C hchart L)) := hSu
  let : Algebra (globalFunctionsModel B S hS D.limitSpace)
      (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u) :=
    (D.limitChartHom C hchart L).toAlgebra
  have : Algebra.Etale (globalFunctionsModel B S hS D.limitSpace)
      (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u) := hEt'
  have hds := D.directedSystem_modelTransition
  have hmodel := D.isStagesColimit_modelProjection_of_isCutoffBoundedSystem hDc
  obtain ⟨n, j, hj, q, hqE, hqS, ⟨ealg⟩⟩ :=
    MvPolynomial.exists_ge_etale_surjective_quotient_of_directed hmodel.hφ hmodel.hsurj
      hmodel.hzero (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u)
      hSu' D.base
  have hrelLim : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L)
      (fun k ↦ ealg.symm (Ideal.Quotient.mk
        (Ideal.span (Set.range fun k ↦ MvPolynomial.map (D.modelProjection j) (q k)))
        (MvPolynomial.X k)))
      (MvPolynomial.map (D.modelProjection j) (q l)) = 0 := fun l ↦
    eval₂_mk_X_eq_zero _ ealg l
  obtain ⟨m, hm, y, hyt, hyrel⟩ :=
    D.exists_ge_eval₂_map_eq_zero_of_isCutoffBoundedSystem C hchart L hDc ⟨j, hj⟩ q
    (fun k ↦ ealg.symm (Ideal.Quotient.mk
      (Ideal.span (Set.range fun k ↦ MvPolynomial.map (D.modelProjection j) (q k)))
      (MvPolynomial.X k))) hrelLim
  have hrelGlim : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L)
      (fun k ↦ ealg.symm (Ideal.Quotient.mk
        (Ideal.span (Set.range fun k ↦ MvPolynomial.map (D.modelProjection j) (q k)))
        (MvPolynomial.X k)))
      ((fun k ↦ MvPolynomial.map (D.modelProjection m.1)
        (MvPolynomial.map (D.modelTransition j m.1 hm) (q k))) l) = 0 := by
    intro l
    change MvPolynomial.eval₂ _ _ (MvPolynomial.map (D.modelProjection m.1)
      (MvPolynomial.map (D.modelTransition j m.1 hm) (q l))) = 0
    rw [MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q l)]
    exact hrelLim l
  obtain ⟨i, hi, hiaff⟩ :=
    D.exists_isAffineSpace_system_obj_of_presentation_of_isCutoffBoundedSystem C hchart L
    hterminal hchartSurj hDc hX m
    (fun k ↦ MvPolynomial.map (D.modelTransition j m.1 hm) (q k)) y hyrel
    (fun k ↦ ealg.symm (Ideal.Quotient.mk
      (Ideal.span (Set.range fun k ↦ MvPolynomial.map (D.modelProjection j) (q k)))
      (MvPolynomial.X k))) hyt hrelGlim
    (bijective_coordinateHom_of_algEquiv ealg
      (funext fun k ↦ (MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q k)).symm) _
      (fun _ ↦ rfl) hrelGlim)
    (etale_presentationAlgebra_map_of_le
      (f := fun a b (h : a ≤ b) ↦ D.modelTransition a b h) (show j ≤ m.1 from hm) q hqE)
    (surjective_comap_presentationStructureHom_map (D.modelTransition j m.1 hm) q hqS)
  exact ⟨i, m.2.trans hi, hiaff⟩

end ModelSystem

/-- Stacks 07SQ over the integers, for a descent situation bounded by the cutoff: in the
situation of Stacks 084R over `Spec ℤ`, if the system is bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`) and the limit is an affine algebraic space, then
some stage at or beyond the distinguished one is an affine algebraic space. -/
theorem exists_isAffineSpace_system_obj_of_isCutoffBoundedSystem {B : BigFppfSite.{u}}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I)
    (hDc : IsCutoffBoundedSystem B _ hZ D.system)
    (hX : IsAffineSpace B _ hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B _ hZ (D.system.obj (op i)) :=
  D.exists_isAffineSpace_system_obj_of_isTerminal_of_isCutoffBoundedSystem terminalIsTerminal hDc hX

end DescentSituation

end AlgebraicGeometry.Space

end
