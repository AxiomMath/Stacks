module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleStageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RepresentableStage
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineFinitePresentationFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion

/-!
# Étale morphisms from a scheme to the limit of a presented system descend to schemes

Let `U = lim U_i` be the limit of a cofiltered system of algebraic spaces over `Spec ℤ`,
presented by systems of étale atlases and of their kernel pairs with realised limits, the
stages being locally of finite presentation over `Spec ℤ` with affine transition morphisms.
An étale morphism `W ⟶ U` from a quasi-compact separated scheme `W`, whose base change to the
limit atlas is quasi-compact and quasi-separated, is the base change of an étale morphism
`W_i ⟶ U_i` from a scheme at some stage.

The stage model `W₀ ⟶ U_{i₀}` given by
`AlgebraicGeometry.Space.LimitPresentation.exists_etaleStageModel` is an algebraic space; its
base changes form a presented system with limit `W`. Writing the separated scheme `W` as the
limit of separated schemes of finite type over `Spec ℤ` (Stacks 01ZA), Stacks 0CP4 makes some
base change of `W₀` affine over a scheme, hence a scheme.

## Main results

* `AlgebraicGeometry.Space.exists_isLimit_separated_siteSystem`: a quasi-compact separated
  object of the big fppf site of `Spec ℤ` is the realised limit of a cofiltered system of
  separated objects of finite type over `Spec ℤ` with affine transition morphisms.
* `AlgebraicGeometry.Space.LimitPresentation.exists_representable_etale_system`: the descent
  statement above, together with the system of base changes of the model to later stages, which
  are schemes with `W` as realised limit.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}

/-- The terminal scheme is locally Noetherian, being isomorphic to `Spec ℤ`. -/
private theorem isLocallyNoetherian_terminal_scheme : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
  have e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).symm
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  exact LocallyOfFiniteType.isLocallyNoetherian e.hom

/-- **A quasi-compact separated scheme of the big fppf site of `Spec ℤ` is the realised limit of
a cofiltered system of separated schemes of finite type over `Spec ℤ` with affine transition
morphisms** (Stacks 01ZA). -/
theorem exists_isLimit_separated_siteSystem (Y : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    [CompactSpace ((BigFppfOver.toScheme B _ hZ).obj Y)]
    [Scheme.IsSeparated ((BigFppfOver.toScheme B _ hZ).obj Y)] :
    ∃ (M : Type u) (_ : Category.{u} M) (_ : IsCofiltered M)
      (T : M ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ) (π : (Functor.const M).obj Y ⟶ T),
      Nonempty (IsLimit ((BigFppfOver.toScheme B _ hZ).mapCone (Cone.mk Y π))) ∧
      (∀ {m m' : M} (e : m ⟶ m'), _root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B _ hZ).map (T.map e))) ∧
      (∀ m, CompactSpace ((BigFppfOver.toScheme B _ hZ).obj (T.obj m))) ∧
      (∀ m, Scheme.IsSeparated ((BigFppfOver.toScheme B _ hZ).obj (T.obj m))) ∧
      (∀ m, LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B _ hZ).obj (T.obj m)))) := by
  classical
  let G := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  obtain ⟨I, _, _, _, F, c, hFaff, hFlft, hFqc, ⟨hc⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType (G.obj Y)
  have : ∀ i, CompactSpace (F.obj i) := fun i =>
    QuasiCompact.compactSpace_of_compactSpace (terminal.from (F.obj i))
  have : ∀ i, QuasiSeparatedSpace (F.obj i) := fun i => by
    have := hFlft i
    have := isLocallyNoetherian_terminal_scheme.{u}
    have : IsLocallyNoetherian (F.obj i) :=
      LocallyOfFiniteType.isLocallyNoetherian (terminal.from (F.obj i))
    infer_instance
  let e : Iᵒᵖ ≌ Iᵒᵈ := (orderDualEquivalence I).symm
  let F' : Iᵒᵖ ⥤ Scheme.{u} := e.functor ⋙ F
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (F'.map g) :=
    fun g => hFaff _
  have : ∀ i, CompactSpace (F'.obj i) := fun i => inferInstanceAs (CompactSpace (F.obj _))
  have : ∀ i, QuasiSeparatedSpace (F'.obj i) := fun i =>
    inferInstanceAs (QuasiSeparatedSpace (F.obj _))
  have : QuasiSeparatedSpace (⊤_ Scheme.{u}) := by
    have := isLocallyNoetherian_terminal_scheme.{u}
    infer_instance
  let t : F' ⟶ (Functor.const Iᵒᵖ).obj (⊤_ Scheme.{u}) :=
    { app := fun i => terminal.from _, naturality := fun _ _ _ => terminal.hom_ext _ _ }
  let c' : Cone F' := (Cone.mk _ c).whisker e.functor
  have hc' : IsLimit c' := (IsLimit.whiskerEquivalenceEquiv e) hc
  have : _root_.AlgebraicGeometry.IsSeparated (terminal.from (G.obj Y)) :=
    Scheme.IsSeparated.isSeparated_terminal_from
  obtain ⟨i₀, hi₀⟩ := eventually_isSeparated_of_isLimit F' t c' hc' (terminal.from (G.obj Y))
    (by ext; exact terminal.hom_ext _ _)
  let M := Over (OrderDual.toDual i₀)
  have hsep : ∀ m : M, Scheme.IsSeparated (F.obj m.left) := fun m =>
    ⟨hi₀ (OrderDual.ofDual m.left) (leOfHom m.hom)⟩
  let T₀ := BigFppfOver.terminalObj B (⊤_ Scheme.{u}) hZ
  have hcY : ∀ m : M, CompactSpace (F.obj m.left) := fun m => inferInstance
  let Tobj : M → BigFppfOver B (⊤_ Scheme.{u}) hZ := fun m =>
    siteObjectOfLocallyOfFiniteType T₀ (terminal.from (F.obj m.left))
  let T : M ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ :=
    { obj := Tobj
      map := fun {m m'} g => siteObjectOfLocallyOfFiniteType.lift T₀ _ (F.map g.left)
        (terminal.hom_ext _ _)
      map_id := fun m => (BigFppfOver.toScheme B _ hZ).map_injective (by
        rw [siteObjectOfLocallyOfFiniteType.toScheme_map_lift, CategoryTheory.Functor.map_id,
          Over.id_left, CategoryTheory.Functor.map_id]
        rfl)
      map_comp := fun g g' => (BigFppfOver.toScheme B _ hZ).map_injective (by
        rw [siteObjectOfLocallyOfFiniteType.toScheme_map_lift, Functor.map_comp,
          siteObjectOfLocallyOfFiniteType.toScheme_map_lift,
          siteObjectOfLocallyOfFiniteType.toScheme_map_lift, Over.comp_left, Functor.map_comp]) }
  let π : (Functor.const M).obj Y ⟶ T :=
    { app := fun m => siteObjectOfLocallyOfFiniteType.lift T₀ _ (c.app m.left)
        (terminal.hom_ext _ _)
      naturality := fun m m' g => (BigFppfOver.toScheme B _ hZ).map_injective (by
        rw [Functor.map_comp, Functor.map_comp]
        exact c.naturality g.left) }
  have hlim : IsLimit (G.mapCone (Cone.mk Y π)) :=
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget (OrderDual.toDual i₀)) _).symm hc).ofIsoLimit
      (Cones.ext (Iso.refl _) (fun m => (Category.id_comp _).symm))
  exact ⟨M, inferInstance, inferInstance, T, π, ⟨hlim⟩,
    fun g => hFaff g.left, fun m => hcY m, hsep, fun m => hFlft _⟩

section Lift

variable {C : Type*} [Category.{u} C] {K : Type*} [Category* K]

/-- A diagram of presheaves whose values are represented, lifted to the represented objects. -/
noncomputable abbrev liftRepresented (F : K ⥤ Cᵒᵖ ⥤ Type u) (Y : K → C)
    (e : ∀ k, yoneda.obj (Y k) ≅ F.obj k) : K ⥤ C where
  obj := Y
  map {k l} f := yoneda.preimage ((e k).hom ≫ F.map f ≫ (e l).inv)
  map_id k := yoneda.map_injective (by simp)
  map_comp f g := yoneda.map_injective (by simp)

/-- The Yoneda image of `(liftRepresented F Y e).map f` is `F.map f` conjugated by the
representing isomorphisms `e k` and `e l`. -/
theorem yoneda_map_liftRepresented (F : K ⥤ Cᵒᵖ ⥤ Type u) (Y : K → C)
    (e : ∀ k, yoneda.obj (Y k) ≅ F.obj k) {k l : K} (f : k ⟶ l) :
    yoneda.map ((liftRepresented F Y e).map f) = (e k).hom ≫ F.map f ≫ (e l).inv :=
  Functor.map_preimage _ _

end Lift

/-- An object of the site of `Spec ℤ` of finite type over `Spec ℤ` is locally of finite
presentation over the terminal presheaf. -/
theorem isLocallyOfFinitePresentation_terminal_from_yoneda_of_lft
    (Y : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hY : LocallyOfFiniteType (terminal.from ((BigFppfOver.toScheme B _ hZ).obj Y))) :
    IsLocallyOfFinitePresentation B _ hZ (terminal.from (yoneda.obj Y)) := by
  refine isLocallyOfFinitePresentation_terminal_from_yoneda B _ hZ Y ?_
  have := isLocallyNoetherian_terminal_scheme.{u}
  have h : B.inclusion.map Y.hom = terminal.from ((BigFppfOver.toScheme B _ hZ).obj Y) :=
    terminal.hom_ext _ _
  rw [h]
  exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType (Y := ⊤_ Scheme.{u})).mpr hY

namespace LimitPresentation

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
  {D : J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} {c : Cone D}
  (P : LimitPresentation B (⊤_ Scheme.{u}) hZ D c)

include P in
/-- **An étale morphism from a separated scheme to the limit of a presented system is the base
change of an étale morphism from a scheme to a stage** (Stacks 07SK, 07SL and 07SR). Let
`U = lim U_j` be presented, with stages locally of finite presentation over `Spec ℤ`, and let
`w : W ⟶ U` be a morphism from a quasi-compact separated scheme whose base change `W'` to the
limit atlas is étale, quasi-compact and quasi-separated. Then there are a stage `j` and a system
`Y` of schemes over the stages `U_l`, `l` over `j`, étale and cartesian over the transition
morphisms, whose base changes to `U` are `w` and whose realised limit is `W`; the stages are
quasi-compact. -/
theorem exists_representable_etale_system (hc : IsLimit c)
    (hD : ∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) (hU : IsAlgebraicSpace B _ hZ c.pt)
    (hDfp : ∀ j, IsLocallyOfFinitePresentation B _ hZ (terminal.from (D.obj j)))
    {W : BigFppfOver B (⊤_ Scheme.{u}) hZ} [CompactSpace ((BigFppfOver.toScheme B _ hZ).obj W)]
    [Scheme.IsSeparated ((BigFppfOver.toScheme B _ hZ).obj W)] (w : yoneda.obj W ⟶ c.pt)
    {W' : BigFppfOver B (⊤_ Scheme.{u}) hZ} (w' : W' ⟶ P.atlasCone.pt)
    (g : yoneda.obj W' ⟶ yoneda.obj W) (hg : IsPullback g (yoneda.map w') w P.limitAtlas)
    (het : Etale ((BigFppfOver.toScheme B _ hZ).map w'))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B _ hZ).map w'))
    (hqs : QuasiSeparated ((BigFppfOver.toScheme B _ hZ).map w')) :
    ∃ (j : J) (Y : Over j ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ)
      (πY : (Functor.const (Over j)).obj W ⟶ Y) (y : Y ⋙ yoneda ⟶ Over.forget j ⋙ D),
      Nonempty (IsLimit ((BigFppfOver.toScheme B _ hZ).mapCone (Cone.mk W πY))) ∧
      (∀ l, IsEtale B _ hZ (y.app l)) ∧
      (∀ l, IsPullback (yoneda.map (πY.app l)) w (y.app l) (c.π.app l.left)) ∧
      (∀ {l l' : Over j} (φ : l ⟶ l'),
        IsPullback (yoneda.map (Y.map φ)) (y.app l) (y.app l') (D.map φ.left)) ∧
      (∀ l, CompactSpace ((BigFppfOver.toScheme B _ hZ).obj (Y.obj l))) := by
  have hWalg := isAlgebraicSpace_yoneda B _ hZ W
  have : Nonempty J := IsCofiltered.nonempty
  obtain ⟨j₀, ⟨E⟩⟩ := P.exists_etaleStageModel hc hD hU hWalg hg het hqc hqs
  have hg_surj := presheaf_of_isPullback B _ hZ hg.flip P.surjective_limitAtlas
  have hg_et := presheaf_of_isPullback B _ hZ hg.flip P.etale_limitAtlas
  let PW := E.presentation hD hWalg hg hg_surj hg_et
  let A := E.atlasFamily hD
  have hX : ∀ k, IsAlgebraicSpace B _ hZ (A.X k) := A.isAlgebraicSpace
  have hTerm := isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ
  have hfstet : ∀ k : Over j₀, IsEtale B _ hZ (pullback.fst (D.map k.hom) E.w₀) := fun k =>
    isEtale_pullback_fst B _ hZ (hD _) (hD _) E.isAlgebraicSpace _ _ E.isEtale_w₀
  have hXfp : ∀ k, IsLocallyOfFinitePresentation B _ hZ (terminal.from (A.diagram.obj k)) :=
    fun k => by
      have h : terminal.from (A.diagram.obj k) =
          pullback.fst (D.map k.hom) E.w₀ ≫ terminal.from (D.obj k.left) := terminal.hom_ext _ _
      rw [h]
      exact isLocallyOfFinitePresentation_comp B _ hZ (hX k) (hD _) hTerm _ _
        (isLocallyOfFinitePresentation_of_isEtale B _ hZ (hfstet k)) (hDfp _)
  have hXaff : ∀ {k k' : Over j₀} (e : k ⟶ k'), IsAffineHom B _ hZ (A.diagram.map e) :=
    fun e => A.isAffineHom_diagram_map E.hcart e (E.isAffineHom_atlasSystem_map e)
  obtain ⟨M, _, _, T, π, ⟨hlimT⟩, hTaff, hTc, hTsep, hTlft⟩ :=
    exists_isLimit_separated_siteSystem (B := B) (hZ := hZ) W
  have hTqc := fun m => isQuasiCompactSpace_yoneda_obj B _ hZ (hTc m)
  have hTqs := fun m => isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ
    (yoneda.obj (T.obj m)) (BigFppfSite.contains_terminal B)
    ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩
  obtain ⟨k, Y, ⟨eY⟩⟩ := PW.exists_iso_yoneda_stage (E.isLimit_cone hD hWalg hg hg_surj hg_et hc)
    hX hXfp hXaff T hTaff hlimT hTqc hTqs hTsep
    (fun m => isLocallyOfFinitePresentation_terminal_from_yoneda_of_lft _ (hTlft m))
    (Iso.refl _)
  let ι : Over k.left ⥤ Over j₀ := Over.map k.hom
  let toK : ∀ l : Over k.left, ι.obj l ⟶ k := fun l => Over.homMk l.hom rfl
  have hrep : ∀ l : Over k.left, ∃ Yl : BigFppfOver B (⊤_ Scheme.{u}) hZ,
      Nonempty (yoneda.obj Yl ≅ A.diagram.obj (ι.obj l)) := fun l =>
    exists_iso_yoneda_of_isAffineHom (hX _) (A.diagram.map (toK l) ≫ eY.inv)
      (isAffineHom_comp B _ hZ _ _ (hXaff _) (isAffineHom_of_isIso _))
  choose Yo he using hrep
  let e : ∀ l, yoneda.obj (Yo l) ≅ A.diagram.obj (ι.obj l) := fun l => (he l).some
  have hfac : ∀ (l : Over k.left) (k' : Over j₀) (a : k' ⟶ ι.obj l),
      ∃ (l' : Over k.left) (φ : l' ⟶ l) (i : ι.obj l' ⟶ k'), ι.map φ = i ≫ a := fun l k' a =>
    ⟨Over.mk (a.left ≫ l.hom), Over.homMk a.left rfl,
      Over.homMk (𝟙 _) (by
        rw [Category.id_comp]; exact (Over.w a).symm.trans (Category.assoc _ _ _).symm),
      Over.OverMorphism.ext (by simp [ι])⟩
  let Ys := liftRepresented (ι ⋙ A.diagram) Yo e
  let cw := E.cone hD hWalg hg_surj hg_et
  have hcw : IsLimit cw := E.isLimit_cone hD hWalg hg hg_surj hg_et hc
  let πY : (Functor.const (Over k.left)).obj W ⟶ Ys :=
    { app := fun l => yoneda.preimage (cw.π.app (ι.obj l) ≫ (e l).inv)
      naturality := fun l l' φ => yoneda.map_injective (by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Functor.map_comp, Functor.map_preimage, Ys, Category.assoc, Iso.inv_hom_id_assoc,
          Functor.comp_map]
        rw [← Category.assoc (cw.π.app _), cw.w]) }
  have hπY : ∀ l, yoneda.map (πY.app l) = cw.π.app (ι.obj l) ≫ (e l).inv := fun l =>
    Functor.map_preimage _ _
  let y : Ys ⋙ yoneda ⟶ Over.forget k.left ⋙ D :=
    { app := fun l => (e l).hom ≫ pullback.fst (D.map (ι.obj l).hom) E.w₀
      naturality := fun l l' φ => by
        show yoneda.map (Ys.map φ) ≫ (e l').hom ≫ pullback.fst _ _ =
          ((e l).hom ≫ pullback.fst _ _) ≫ D.map φ.left
        rw [yoneda_map_liftRepresented]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        show (e l).hom ≫ A.diagram.map (ι.map φ) ≫ pullback.fst _ _ = _
        rw [AtlasFamily.diagram_map, E.atlasFamily_map hD, overStageBaseChange_map_fst]
        rfl }
  have hlimY : IsLimit ((BigFppfOver.toScheme B _ hZ).mapCone (Cone.mk W πY)) := by
    refine isLimitOfInterleaved _ Ys T (Cone.mk W πY) π hlimT (fun m => ?_) (fun l => ?_)
      (fun {l m} u v huv => ?_) (fun {l l₂} u v huv => ?_)
    · obtain ⟨k₁, z, hz⟩ := PW.exists_stage_hom hcw hX (isAlgebraicSpace_yoneda B _ hZ (T.obj m))
        (isLocallyOfFinitePresentation_terminal_from_yoneda_of_lft _ (hTlft m))
        (yoneda.map (π.app m))
      let a := IsCofiltered.minToLeft k₁ k
      let b := IsCofiltered.minToRight k₁ k
      let l : Over k.left := Over.mk b.left
      let i : ι.obj l ⟶ IsCofiltered.min k₁ k := Over.homMk (𝟙 _) (by
        rw [Category.id_comp]; exact (Over.w b).symm)
      refine ⟨l, yoneda.preimage ((e l).hom ≫ A.diagram.map (i ≫ a) ≫ z),
        yoneda.map_injective ?_⟩
      show yoneda.map (πY.app l ≫ _) = _
      rwa [Functor.map_comp, hπY, Functor.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        ← Category.assoc, cw.w]
    · obtain ⟨m, h', hh'⟩ := exists_stage_hom_of_isLimit_toScheme B _ hZ hTaff hlimT
        hTqc hTqs (hX (ι.obj l)) (hXfp _) (cw.π.app (ι.obj l))
      refine ⟨m, yoneda.preimage (h' ≫ (e l).inv), yoneda.map_injective ?_⟩
      show yoneda.map (π.app m ≫ _) = yoneda.map (πY.app l)
      rw [Functor.map_comp, Functor.map_preimage, ← Category.assoc, hh', hπY]
    · obtain ⟨k', a, ha⟩ := PW.exists_stage_eq hX (isAlgebraicSpace_yoneda B _ hZ (T.obj m))
        (isLocallyOfFinitePresentation_terminal_from_yoneda_of_lft _ (hTlft m))
        ((e l).inv ≫ yoneda.map u) ((e l).inv ≫ yoneda.map v) (by
          simpa only [Functor.map_comp, hπY, Category.assoc] using congrArg yoneda.map huv)
      obtain ⟨l', φ, i, hφ⟩ := hfac l k' a
      refine ⟨l', φ, yoneda.map_injective ?_⟩
      rw [Functor.map_comp, Functor.map_comp, yoneda_map_liftRepresented]
      show ((e l').hom ≫ A.diagram.map (ι.map φ) ≫ (e l).inv) ≫ _ =
        ((e l').hom ≫ A.diagram.map (ι.map φ) ≫ (e l).inv) ≫ _
      rw [hφ, A.diagram.map_comp]
      simp only [Category.assoc]
      rw [ha]
    · obtain ⟨k', a, ha⟩ := PW.exists_stage_eq hX (hX (ι.obj l₂)) (hXfp _)
        ((e l).inv ≫ yoneda.map u ≫ (e l₂).hom) ((e l).inv ≫ yoneda.map v ≫ (e l₂).hom) (by
          have h := congrArg (fun x => yoneda.map x ≫ (e l₂).hom) huv
          simp only [Functor.map_comp, hπY, Category.assoc] at h
          exact h)
      obtain ⟨l', φ, i, hφ⟩ := hfac l k' a
      refine ⟨l', φ, yoneda.map_injective ?_⟩
      have ha' := congrArg (fun x => (e l').hom ≫ A.diagram.map i ≫ x ≫ (e l₂).inv) ha
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at ha'
      rw [Functor.map_comp, Functor.map_comp, yoneda_map_liftRepresented]
      show ((e l').hom ≫ A.diagram.map (ι.map φ) ≫ (e l).inv) ≫ _ =
        ((e l').hom ≫ A.diagram.map (ι.map φ) ≫ (e l).inv) ≫ _
      rw [hφ, A.diagram.map_comp]
      simp only [Category.assoc]
      exact ha'
  have hS1 : ∀ l : Over k.left, IsPullback (cw.π.app (ι.obj l)) w
      (pullback.fst (D.map (ι.obj l).hom) E.w₀) (c.π.app l.left) := fun l => by
    refine IsPullback.of_right ?_ (E.cone_π_fst hD hWalg hg hg_surj hg_et (ι.obj l))
      (IsPullback.of_hasPullback (D.map (ι.obj l).hom) E.w₀).flip
    rw [E.cone_π_snd hD hWalg hg_surj hg_et (ι.obj l)]
    exact (c.w (ι.obj l).hom).symm ▸ E.isPullback_v
  refine ⟨k.left, Ys, πY, y, ⟨hlimY⟩, fun l => isEtale_comp B _ hZ (isEtale_of_isIso B _ hZ _)
    (hfstet (ι.obj l)), fun l => ?_, fun {l l'} φ => ?_, fun l => ?_⟩
  · refine (hS1 l).of_iso (Iso.refl _) (e l).symm (Iso.refl _) (Iso.refl _) ?_ (by simp)
      (by simp [y]) (by simp)
    simp [hπY]
  · refine (isPullback_overStageBaseChange_map (ι.map φ)).of_iso (e l).symm (e l').symm (Iso.refl _)
      (Iso.refl _) ?_ (by simp [y]) (by simp [y]) (by simp; rfl)
    simpa [Ys] using (E.atlasFamily_map hD _).symm
  · have := E.compactSpace_atlasSystem (ι.obj l)
    exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B _ hZ
      (isQuasiCompactSpace_of_iso B _ hZ (e l).symm
        ⟨A.V.obj (ι.obj l), A.v (ι.obj l), inferInstance, A.surjective _,
          (isEtale_iff_presheaf_of_yoneda B _ hZ _).mpr (A.etale _)⟩)

end LimitPresentation

end AlgebraicGeometry.Space

end
