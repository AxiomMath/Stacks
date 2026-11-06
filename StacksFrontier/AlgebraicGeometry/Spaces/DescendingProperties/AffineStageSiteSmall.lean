module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineOverBaseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartGlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEqualizerPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationGlobalFunctionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimitSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsTerminalIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.RingTheory.Etale.DirectedColimitEtaleStage
public import StacksFrontier.RingTheory.MvPolynomial.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescent

/-!
# Affineness descends to a finite stage, under the site-containment hypothesis

Stacks 07SQ in the form whose hypothesis is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`:
if the limit of a directed system of quasi-compact and quasi-separated algebraic spaces with affine
transition maps is affine, then so is some stage. The proof is that of
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStage.lean`, carried through
`AlgebraicGeometry.Space.MorphismDescentSituation`.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `DescentSituation.exists_isAffineHom_system_app` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/AffineStage.lean`) is registered
  here as **Stacks 0A0R**.
* `isStagesColimit_globalFunctionsModel_of_siteContainsBaseChangeLimits`
* `MorphismDescentSituation.isIso_mapLimit_of_isPullback`
* `MorphismDescentSituation.isAffineSpace_base_obj_of_isIso_mapAt`
* In the namespace `DescentSituation`:
  * `isStagesColimit_modelProjection_of_siteContainsBaseChangeLimits`
  * `exists_isAffineSpace_system_obj_of_isPullback_of_siteContainsBaseChangeLimits`
  * `exists_isAffineSpace_system_obj_of_presentation_of_siteContainsBaseChangeLimits`
  * `exists_ge_eval₂_map_eq_zero_of_siteContainsBaseChangeLimits`
  * `exists_isAffineSpace_system_obj_of_isTerminal_of_siteContainsBaseChangeLimits`
  * `exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits`
  * `exists_isAffineSpace_system_obj_of_isSiteSmall`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_AffineStageSiteSmall :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasLimit_cospan_presheaf_AffineStageSiteSmall
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The `u`-models of the rings of global functions of a descent situation -/

section ModelSystem

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **Stacks 07SI for the structure sheaf, read on `u`-models.** The ring of global regular
functions of the limit of a descent situation is the filtered colimit of those of the stages,
and so is its `u`-model the filtered colimit of theirs.

`AlgebraicGeometry.Space.globalFunctions` lives in `Type (u + 1)`, while the proof of Stacks
07SQ must take `Spec` of the colimit ring and of the stage rings and so needs them in the
universe of the site. `AlgebraicGeometry.Space.globalFunctionsModel` is the `u`-model, available
because the ring is `u`-small, and this is the colimit assertion transported to it: the three
clauses of `Stacks.IsStagesColimit` are the hypothesis package of the commutative-algebra core
`MvPolynomial.exists_ge_etale_surjective_quotient_of_directed`, through
`Stacks.IsStagesColimit.hφ`, `.hsurj` and `.hzero`.

The hypothesis is the chapter's convention, through
`DescentSituation.isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits`; it is consumed
there and nowhere else here. -/
theorem isStagesColimit_globalFunctionsModel_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    Stacks.IsStagesColimit
      (G := fun i : I => globalFunctionsModel B S hS (D.stage i))
      (T := globalFunctionsModel B S hS D.limitSpace)
      (fun i j (h : i ≤ j) x => (stageModelEquiv D j).symm
        (globalFunctionsMap B S hS (D.transition h) (stageModelEquiv D i x)))
      (fun i x => (limitModelEquiv D).symm
        (globalFunctionsMap B S hS (D.projection i) (stageModelEquiv D i x))) := by
  obtain ⟨hphi, hsurj, hzero⟩ :=
    D.ringPackage_of_isGlobalFunctionsColimit
      (D.isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits hconv)
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
        (D.isGlobalFunctionsColimit_of_siteContainsBaseChangeLimits hconv) i _ _ h0
    exact ⟨j, hij, congrArg (stageModelEquiv D j).symm hj⟩

end ModelSystem

/-! ### Chart restriction against pullback of global functions -/

section ChartRestrictionCoherence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end ChartRestrictionCoherence

/-! ### The identification of an affine algebraic space with the spectrum of its functions -/

section SpecIdentification

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end SpecIdentification

/-! ### A polynomial presentation at a later stage of a directed system of rings -/

section PresentationStage

variable {ι : Type*} [Preorder ι] {G : ι → Type u} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j}

end PresentationStage

/-! ### The coordinates of a presentation read through an algebra isomorphism -/

section Coordinates

end Coordinates

/-! ### Morphisms out of an algebraic space are determined on a surjective étale chart -/

section HomExt

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end HomExt

/-! ### Invertibility of a base change to the limit from two Cartesian squares -/

section MapLimit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- Pulling back the left leg of a Cartesian square along any map into its base corner gives a
Cartesian square over the composite. -/
private theorem isPullback_pullback_fst_snd_comp
    {C : Type*} [Category C] [HasPullbacks C] {A X W Z P : C} (a : P ⟶ A) {f : X ⟶ A} {q : X ⟶ W}
    {pZ : A ⟶ Z} {aW : W ⟶ Z} (hq : IsPullback f q pZ aW) :
    IsPullback (pullback.fst a f) (pullback.snd a f ≫ q) (a ≫ pZ) aW :=
  (((IsPullback.of_hasPullback a f).flip.paste_horiz hq.flip)).flip

/-- **A base change to the limit is an isomorphism when source and target are exhibited as fibre
products over one cospan.** In the situation of Stacks 084W, suppose the target `Y₀` of the
morphism to be descended is the fibre product of the distinguished stage with a presheaf `W` over
a presheaf `Z`, and suppose the source over the limit is the fibre product of the limit with `W`
over `Z` through the composite of the morphism to be descended with the projection to `W`. Then
the base change `f : X ⟶ Y` of `f₀` to the limit is an isomorphism, since both `X` and `Y` are
fibre products of the same cospan and `f` respects the two projections.

This is the step of the proof of Stacks 07SQ at which the square of Stacks 084U, Cartesian over
the limit, makes the morphism of display 70.5.10.1 invertible there, so that Stacks 084S
applies. -/
theorem MorphismDescentSituation.isIso_mapLimit_of_isPullback
    (M : MorphismDescentSituation B S hS hZ I)
    {W Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : M.base.obj (op M.initial) ⟶ Z) (aW : W ⟶ Z)
    (q : M.target₀ ⟶ W) (hq : IsPullback M.targetToBase q pZ aW)
    (cS : M.source₀ ⟶ W) (hcS : M.map₀ ≫ q = cS)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {α : P ⟶ limit M.base} {γ : P ⟶ M.source₀}
    (hPstage : IsPullback α γ (limit.π M.base (op M.initial)) M.sourceToBase)
    (hP : IsPullback α (γ ≫ cS) (limit.π M.base (op M.initial) ≫ pZ) aW) :
    IsIso M.mapLimit := by
  have htgt := isPullback_pullback_fst_snd_comp (limit.π M.base (op M.initial)) hq
  have hsrc : IsPullback (pullback.fst (limit.π M.base (op M.initial)) M.sourceToBase)
      (pullback.snd (limit.π M.base (op M.initial)) M.sourceToBase ≫ cS)
      (limit.π M.base (op M.initial) ≫ pZ) aW := by
    refine hP.of_iso (hPstage.isoIsPullback _ _
      (IsPullback.of_hasPullback (limit.π M.base (op M.initial)) M.sourceToBase))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans
        (IsPullback.isoIsPullback_hom_fst _ _ hPstage _).symm
    · exact (Category.comp_id _).trans
        ((congrArg (fun z => z ≫ cS)
          (IsPullback.isoIsPullback_hom_snd _ _ hPstage _).symm).trans
          (Category.assoc _ _ _))
    · simp
    · simp
  have hmap : M.mapLimit = (hsrc.isoIsPullback _ _ htgt).hom := by
    refine htgt.hom_ext ?_ ?_
    · exact M.mapLimit_fst.trans
        (IsPullback.isoIsPullback_hom_fst _ _ hsrc htgt).symm
    · refine (Category.assoc _ _ _).symm.trans ?_
      refine ((congrArg (fun z => z ≫ q) M.mapLimit_snd).trans
        (Category.assoc _ _ _)).trans ?_
      refine (congrArg (fun z => pullback.snd (limit.π M.base (op M.initial))
        M.sourceToBase ≫ z) hcS).trans ?_
      exact (IsPullback.isoIsPullback_hom_snd _ _ hsrc htgt).symm
  rw [hmap]
  exact (inferInstance : IsIso (hsrc.isoIsPullback (limit M.base) W htgt).hom)

/-- **A stage of a morphism descent system is affine once the base change of the morphism there
is an isomorphism.** In the situation of Stacks 084W, suppose the target `Y₀` of the morphism to
be descended is the fibre product of the distinguished stage with an affine object `W` of the
site over an affine algebraic space `Z`, the morphism `h_W ⟶ Z` being surjective and étale.
If the base change `f_k` of `f₀` to a stage `k` is an isomorphism and the base change `X_k` of
`X₀` there is affine, then the stage `B_k` of the system is an affine algebraic space.

This is the last step of the proof of Stacks 07SQ: the étale covering `Spec B_i ⟶ Spec A_i`
descends affineness of `X_i ⟶ Spec A_i` by the implication (4) ⇒ (2) of Stacks 03WG, and the
source of an affine morphism with affine target is affine. -/
theorem MorphismDescentSituation.isAffineSpace_base_obj_of_isIso_mapAt
    (M : MorphismDescentSituation B S hS hZ I)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (pZ : M.base.obj (op M.initial) ⟶ Z)
    {W : BigFppfOver B S hS} (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (aW : yoneda.obj W ⟶ Z) (haWsurj : IsSurjective B S hS aW)
    (haWetale : IsEtale B S hS aW) (hZalg : IsAlgebraicSpace B S hS Z)
    (hZaff : IsAffineSpace B S hS Z) (q : M.target₀ ⟶ yoneda.obj W)
    (hq : IsPullback M.targetToBase q pZ aW) {k : I} (hk : M.initial ≤ k)
    (hsrcAff : IsAffineSpace B S hS (M.sourceAt k hk)) (hkiso : IsIso (M.mapAt k hk)) :
    IsAffineSpace B S hS (M.base.obj (op k)) := by
  have := hkiso
  have htgtAff : IsAffineSpace B S hS (M.targetAt k hk) :=
    hsrcAff.of_iso (asIso (M.mapAt k hk))
  have h4 := isPullback_pullback_fst_snd_comp (M.baseAtToInitial k hk) hq
  have hpbAff : IsAffineSpace B S hS (pullback (M.baseAtToInitial k hk ≫ pZ) aW) :=
    htgtAff.of_iso (h4.isoIsPullback _ _
      (IsPullback.of_hasPullback (M.baseAtToInitial k hk ≫ pZ) aW))
  exact (isAffineHom_of_isAffineSpace_pullback_of_etaleChart B S hS
    (M.base_isAlgebraicSpace k) hZalg (M.baseAtToInitial k hk ≫ pZ) hW aW haWsurj haWetale
    hpbAff).isAffineSpace_source hZaff

end MapLimit

/-! ### The models of the global functions and the charts of a descent situation -/

namespace DescentSituation

section ChartModels

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **Stacks 07SI for the structure sheaf on the `u`-models**, with both families read as ring
homomorphisms. -/
theorem isStagesColimit_modelProjection_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) :
    Stacks.IsStagesColimit (fun i j (h : i ≤ j) x => D.modelTransition i j h x)
      (fun i x => D.modelProjection i x) :=
  isStagesColimit_globalFunctionsModel_of_siteContainsBaseChangeLimits D hconv

section Charts

variable {U₀ : BigAffineFppf B S hS}
  {chart : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.system.obj (op D.base)}
  (C : AffineChartSystem B S hS (op D.base) D.system U₀ chart)
  (hchart : IsEtaleChart B S hS (D.system.obj (op D.base)) (CostructuredArrow.mk chart))

/-- **The descent of display 70.5.10.1 and its conclusion.** Over a terminal base, given at a
stage `m` the square of Stacks 084U for a family `g` of `n` polynomials in `n` variables over the
`u`-model of the global functions of `m`, and given that over the limit that square is Cartesian,
some stage at or beyond `m` is an affine algebraic space.

The morphism of the display is a morphism descent system in the sense of Stacks 084W; it is an
isomorphism over the limit by `MorphismDescentSituation.isIso_mapLimit_of_isPullback`, so
Stacks 084S makes it an isomorphism at some later stage `k`; and there the étale covering
`Spec A_m[x]/(g) ⟶ Spec A_m` descends affineness by
`MorphismDescentSituation.isAffineSpace_base_obj_of_isIso_mapAt`. -/
theorem exists_isAffineSpace_system_obj_of_isPullback_of_siteContainsBaseChangeLimits
    (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hconv : SiteContainsBaseChangeLimits B S hS D.system)
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
  set D' : DescentSituation B S hS hZ I := { D with base := m.1 } with hD'def
  set X₀ : Over (D'.system.obj (op D'.base)) :=
    Over.mk (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom with hX₀def
  set Y₀ : Over (D'.system.obj (op D'.base)) :=
    Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))) with hY₀def
  set f₀ : X₀ ⟶ Y₀ := Over.homMk (pullback.lift
      (D.toLimitSituation.stagesEtaleChart C hchart m).obj.hom
      (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
        (coordinateHom g' (D.stageChartHom C hchart m) y hyrel))) hsq)
      (pullback.lift_fst _ _ _) with hf₀def
  have hfp : IsLocallyOfFinitePresentation B S hS (Over.Hom.left f₀) := by
    refine isLocallyOfFinitePresentation_of_comp B S hS
      (isAlgebraicSpace_yoneda B S hS _) hY₀alg (D.algebraicSpace m.1)
      (Over.Hom.left f₀) Y₀.hom ?_
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hY₀fp.1)
    rw [Over.w f₀]
    exact hX₀fp.1
  set M := D'.morphismDescentSituation X₀ Y₀ (isAlgebraicSpace_yoneda B S hS _) hY₀alg
    hX₀fp hY₀fp f₀ with hMdef
  have hisoML : IsIso M.mapLimit :=
    MorphismDescentSituation.isIso_mapLimit_of_isPullback M p
      (schemePointsMap B S hS (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
      (pullback.snd p _) (IsPullback.of_hasPullback p _)
      (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g')
        (coordinateHom g' (D.stageChartHom C hchart m) y hyrel)))
      (pullback.lift_snd _ _ _)
      (L.isPullback_stage
        ((LimitSituation.stagesOverEquivalence D.toLimitSituation).functor.obj (op m)))
      hsrcPB
  obtain ⟨k, hk, hkiso⟩ := D'.exists_isIso_mapAt_of_isIso_mapLimit_of_siteContainsBaseChangeLimits
    hconv X₀ Y₀
    (isAlgebraicSpace_yoneda B S hS _) hY₀alg hX₀fp hY₀fp f₀ hfp hisoML
  refine ⟨k, hk, ?_⟩
  have hsrcAff : IsAffineSpace B S hS (M.sourceAt k hk) :=
    (IsAffineHom.of_isPullback (M.sourceAt_isPullback k hk)
      (M.transition_affine _)).isAffineSpace_source
      (isAffineSpace_yoneda B S hS _ hWaff)
  have hZaff : IsAffineSpace B S hS (schemePoints B S hS
      (Spec (CommRingCat.of (globalFunctionsModel B S hS (D.stage m.1))))) :=
    isAffineSpace_schemePoints B S hS hterminal
      (contains_spec_globalFunctionsModel B S hS (D.stage m.1))
  have hqSq : IsPullback M.targetToBase
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
  exact MorphismDescentSituation.isAffineSpace_base_obj_of_isIso_mapAt M p
    (show IsAffine ((BigFppfOver.toScheme B S hS).obj
        (terminalSiteObject B S hS hterminal hCont)) by
      rw [toScheme_terminalSiteObject]; infer_instance)
    ((schemePointsIso B S hS hterminal hCont).hom ≫ schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g'))))
    haWsurj haWetale hZaff.isAlgebraicSpace hZaff _ hqSq hk hsrcAff hkiso

/-- **Stacks 07SQ, from a presentation at a stage.** Over a terminal base, suppose the limit of a
descent situation is affine, and suppose at a stage `m` there is a family of `n` polynomials in
`n` variables over the `u`-model of the global functions of that stage which presents an étale
algebra with surjective spectrum, together with regular functions on the chart of `m`
annihilating it and agreeing at the limit with coordinates presenting the global functions of the
limit chart. Then some stage at or beyond `m` is an affine algebraic space.

The canonical morphisms to the spectra of the models are Stacks 05Z1, the square they sit in is
Stacks 084U, and that square is Cartesian over the limit by `isPullback_toLimit_coordinateHom`;
the descent is then
`exists_isAffineSpace_system_obj_of_isPullback_of_siteContainsBaseChangeLimits`. -/
theorem exists_isAffineSpace_system_obj_of_presentation_of_siteContainsBaseChangeLimits
    (L : AffineChartSystem.LimitBridge C)
    (hterminal : IsTerminal S) (hchartSurj : IsSurjective B S hS chart)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hX : IsAffineSpace B S hS D.limitSpace.obj)
    (m : D.toLimitSituation.Stages) {n : ℕ}
    (g' : Fin n → MvPolynomial (Fin n) (globalFunctionsModel B S hS (D.stage m.1)))
    (y : Fin n → Γ((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).obj (op m), ⊤))
    (hyrel : ∀ l, MvPolynomial.eval₂ (D.stageChartHom C hchart m) y (g' l) = 0)
    (t : Fin n → Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤))
    (hyt : ∀ k, (((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
      (op m)).appTop).hom (y k) = t k)
    (hrel : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L) t
      ((fun k => MvPolynomial.map (D.modelProjection m.1) (g' k)) l) = 0)
    (hbij : Function.Bijective
      (coordinateHom (fun k => MvPolynomial.map (D.modelProjection m.1) (g' k))
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
  exact D.exists_isAffineSpace_system_obj_of_isPullback_of_siteContainsBaseChangeLimits C hchart L
    hterminal hconv m g' y hyrel
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

/-- **The coordinates and the relations of a presentation over the limit descend to a single
stage.** Let `q` be a family of `n` polynomials in `n` variables over the `u`-model of the ring
of global functions of a stage `j₀`, and let `t₁, …, tₙ` be regular functions on the limit chart
annihilating the family read over the limit. Then at some stage `m ≥ j₀` there are regular
functions on the chart of `m` annihilating the family read over `m`.

The coordinates are lifted to a stage by `Ring.exists_ge_forall_eq_of_directed` applied to the
colimit description of the regular functions on the charts, Stacks 01Z0 for the structure sheaf;
the relations, which then vanish at the limit, are forced to vanish at a later stage by
`Ring.exists_ge_forall_eq_zero_of_directed`. The two coherences
`AlgebraicGeometry.Space.DescentSituation.appTop_stagesSchemeCone_π_stageChartHom` and
`AlgebraicGeometry.Space.DescentSituation.appTop_stagesSchemeDiagram_map_stageChartHom` are what
carry the relations across the two squares: the first to see them vanish at the limit, the
second to read them at the later stage. -/
theorem exists_ge_eval₂_map_eq_zero_of_siteContainsBaseChangeLimits
    (L : AffineChartSystem.LimitBridge C)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system) (j₀ : D.toLimitSituation.Stages)
    {n : ℕ}
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
  have hmodel := D.isStagesColimit_modelProjection_of_siteContainsBaseChangeLimits hconv
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
      RingHom.ext fun z => D.appTop_stagesSchemeCone_π_stageChartHom C hchart L m z
    have h3 : (fun k => (((((LimitSituation.stagesSchemeCone D.toLimitSituation C L).π.app
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
      (fun l => MvPolynomial.eval₂ (D.stageChartHom C hchart m) y
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))) hvanish
  refine ⟨m', hm.trans hmm', fun k =>
    ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
      (homOfLE hmm').op).appTop).hom) (y k),
    fun k => (hcol.hφ m m' hmm' (y k)).trans (hy k), fun l => ?_⟩
  have hmap : MvPolynomial.map (D.modelTransition j₀.1 m'.1 (hm.trans hmm')) (q l)
      = MvPolynomial.map (D.modelTransition m.1 m'.1 hmm')
        (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l)) :=
    (MvPolynomial.map_map_eq_map_of_directedSystem
      (f := fun i j (h : i ≤ j) => D.modelTransition i j h)
      (show j₀.1 ≤ m.1 from hm) (show m.1 ≤ m'.1 from hmm') (q l)).symm
  have hcomp : ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
          (homOfLE hmm').op).appTop).hom).comp (D.stageChartHom C hchart m)
      = (D.stageChartHom C hchart m').comp (D.modelTransition m.1 m'.1 hmm') :=
    RingHom.ext fun z =>
      D.appTop_stagesSchemeDiagram_map_stageChartHom C hchart hmm' z
  have h6 := MvPolynomial.eval₂_map (D.modelTransition m.1 m'.1 hmm')
    (fun k => ((((LimitSituation.stagesSchemeDiagram D.toLimitSituation C).map
      (homOfLE hmm').op).appTop).hom) (y k))
    (D.stageChartHom C hchart m')
    (MvPolynomial.map (D.modelTransition j₀.1 m.1 hm) (q l))
  rw [hmap, h6, ← hcomp, ← MvPolynomial.hom_eval₂]
  exact hm' l

end Charts

/-! ### Stacks 07SQ -/

/-- **Stacks 07SQ over a terminal base scheme.** In the situation of Stacks 084R over a terminal
base, if the limit `X` of the inverse system is an affine algebraic space then so is some stage
`X_i` with `i` at or beyond the distinguished index. The hypothesis on the base is removed in
`exists_isAffineSpace_system_obj_of_isSiteSmall`, the form the source states and the one
carrying the tag.

The proof follows the source. An affine étale surjective chart `U₀ ⟶ X₀` of the distinguished
stage base changes to a system of affine charts `U_i` with limit `U`, which is an affine étale
surjective chart of `X`; so `Γ(U, 𝒪_U)` is an étale algebra with surjective spectrum over a
`u`-model `A` of `Γ(X, 𝒪_X)`
(`AlgebraicGeometry.Space.etale_globalFunctionsChartRestriction`). The ring of global functions
of the limit is the filtered colimit of those of the stages — Stacks 07SI for the structure
sheaf — so the commutative-algebra core
`MvPolynomial.exists_ge_etale_surjective_quotient_of_directed` presents that algebra by a square
family `q` of polynomials over the model `A_j` of a stage, étale and surjective there, whose base
change to `A` presents `Γ(U, 𝒪_U)`. Its coordinates are regular functions on `U`, and they and
the relations they satisfy descend to a stage `m ≥ j`
(`exists_ge_eval₂_map_eq_zero_of_siteContainsBaseChangeLimits`). That is the data of display
70.5.10.1 at `m`, and
`exists_isAffineSpace_system_obj_of_presentation_of_siteContainsBaseChangeLimits` concludes. -/
theorem exists_isAffineSpace_system_obj_of_isTerminal_of_siteContainsBaseChangeLimits
    (hterminal : IsTerminal S)
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
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
  have : IsCofiltered Iᵒᵖ := inferInstance
  set L := C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hconv)
    with hLdef
  -- the global functions of the limit chart are an étale algebra with surjective spectrum
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
  have hmodel := D.isStagesColimit_modelProjection_of_siteContainsBaseChangeLimits hconv
  -- the commutative-algebra core presents it over a stage
  obtain ⟨n, j, hj, q, hqE, hqS, ⟨ealg⟩⟩ :=
    MvPolynomial.exists_ge_etale_surjective_quotient_of_directed hmodel.hφ hmodel.hsurj
      hmodel.hzero (Γ((LimitSituation.stagesSchemeCone D.toLimitSituation C L).pt, ⊤) : Type u)
      hSu' D.base
  have hrelLim : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L)
      (fun k => ealg.symm (Ideal.Quotient.mk
        (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection j) (q k)))
        (MvPolynomial.X k)))
      (MvPolynomial.map (D.modelProjection j) (q l)) = 0 := fun l =>
    eval₂_mk_X_eq_zero _ ealg l
  -- the coordinates and the relations descend to a stage
  obtain ⟨m, hm, y, hyt, hyrel⟩ :=
    D.exists_ge_eval₂_map_eq_zero_of_siteContainsBaseChangeLimits C hchart L hconv ⟨j, hj⟩ q
    (fun k => ealg.symm (Ideal.Quotient.mk
      (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection j) (q k)))
      (MvPolynomial.X k))) hrelLim
  have hrelGlim : ∀ l, MvPolynomial.eval₂ (D.limitChartHom C hchart L)
      (fun k => ealg.symm (Ideal.Quotient.mk
        (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection j) (q k)))
        (MvPolynomial.X k)))
      ((fun k => MvPolynomial.map (D.modelProjection m.1)
        (MvPolynomial.map (D.modelTransition j m.1 hm) (q k))) l) = 0 := by
    intro l
    show MvPolynomial.eval₂ _ _ (MvPolynomial.map (D.modelProjection m.1)
      (MvPolynomial.map (D.modelTransition j m.1 hm) (q l))) = 0
    rw [MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q l)]
    exact hrelLim l
  obtain ⟨i, hi, hiaff⟩ :=
    D.exists_isAffineSpace_system_obj_of_presentation_of_siteContainsBaseChangeLimits C hchart L
    hterminal hchartSurj hconv hX m
    (fun k => MvPolynomial.map (D.modelTransition j m.1 hm) (q k)) y hyrel
    (fun k => ealg.symm (Ideal.Quotient.mk
      (Ideal.span (Set.range fun k => MvPolynomial.map (D.modelProjection j) (q k)))
      (MvPolynomial.X k))) hyt hrelGlim
    (bijective_coordinateHom_of_algEquiv ealg
      (funext fun k => (MvPolynomial.map_map_eq_of_comp hmodel.hφ hm (q k)).symm) _
      (fun _ => rfl) hrelGlim)
    (etale_presentationAlgebra_map_of_le
      (f := fun a b (h : a ≤ b) => D.modelTransition a b h) (show j ≤ m.1 from hm) q hqE)
    (surjective_comap_presentationStructureHom_map (D.modelTransition j m.1 hm) q hqS)
  exact ⟨i, m.2.trans hi, hiaff⟩

/-- **Stacks 07SQ.** In the situation of Stacks 084R, over an arbitrary base scheme, if the limit
`X` of the inverse system is an affine algebraic space then so is some stage `X_i` with `i` at or
beyond the distinguished index.

The only hypothesis beyond Situation 084R is the chapter's standing convention of Section 70.2
(tag 07SD), that every ring considered has its spectrum in the big fppf site; for this system it
is `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: for every stage, every affine
scheme-valued point of it and the base changes to that point of the later stages, the limit of
those affine schemes — the spectrum of the colimit of their rings — lies in the site. Nothing is
asked of the index. The convention is used three times: to make the limit of the affine charts
of the system an object of the site (Stacks 07SF), to make the ring of global functions of the
limit the filtered colimit of those of the stages (Stacks 07SI for the structure sheaf), and in
Stacks 084S.

It cannot be dropped. Index the stages by the finite subsets of a field `F` of cardinality at
least the cutoff of the site, the stage at a subset being the punctured affine plane over the
subring of `F` it generates: a directed system of quasi-compact separated schemes with affine
transition morphisms, none of them affine. A nonempty object of the site has too small a ring of
functions to receive `F`, so the limit of the system in the site is empty, hence affine. See
`AlgebraicGeometry.Space.DescentSituation.not_forall_exists_isAffineSpace_system_obj`; that the
system violates the convention is
`AlgebraicGeometry.Space.SiteConventionCounterexample.not_siteContainsBaseChangeLimits`.

Affineness of an algebraic space is the absolute notion, taken over the terminal scheme, so the
whole descent is read there: the relocalization along `S ⟶ Spec ℤ` carries the descent situation
over `S` to one over the terminal scheme, which is where the identification of an affine
algebraic space with the spectrum of its global functions is available, and the convention
survives that passage,
`AlgebraicGeometry.Space.DescentSituation.siteContainsBaseChangeLimits_viewOverIntegers`. -/
@[stacks 07SQ]
theorem exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D.system)
    (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ :=
    exists_isAffineSpace_system_obj_of_isTerminal_of_siteContainsBaseChangeLimits
      (D := D.viewOverIntegers B S hS hZ)
      terminalIsTerminal (D.siteContainsBaseChangeLimits_viewOverIntegers hZ hconv)
      ((isAffineSpace_viewOverIntegers_iff B S hS hZ (F := D.limitCone.pt)).2 hX)
  exact ⟨i, hi,
    (isAffineSpace_viewOverIntegers_iff B S hS hZ (F := D.system.obj (op i))).1 hres⟩

/-- **Stacks 07SQ for a system small for the site.** This is
`exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits` under the stronger hypothesis
`AlgebraicGeometry.Space.IsSiteSmall`, which implies the chapter's convention
(`AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`). -/
theorem exists_isAffineSpace_system_obj_of_isSiteSmall (hb : IsSiteSmall B S hS D.system)
    (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (op i)) :=
  have : Nonempty I := ⟨D.base⟩
  D.exists_isAffineSpace_system_obj_of_siteContainsBaseChangeLimits
    (hb.siteContainsBaseChangeLimits B S hS D.system) hX

end ChartModels

end DescentSituation

/-! ### Stacks 0A0R -/

section AffineOverBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u})) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/- Stacks 0A0R: for `X = lim X_i` a directed limit over `Y`, with affine transition morphisms,
of quasi-compact and quasi-separated algebraic spaces, if `X ⟶ Y` is affine then so is
`X_i ⟶ Y` for all `i` large enough. -/
add_to_stacks 0A0R AlgebraicGeometry.Space.DescentSituation.exists_isAffineHom_system_app

end AffineOverBase

end AlgebraicGeometry.Space

end
