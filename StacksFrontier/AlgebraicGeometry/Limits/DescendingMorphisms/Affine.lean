module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative

/-!
# Affine morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of quasi-compact and quasi-separated schemes
with affine transition morphisms. If a morphism between two such schemes over one stage becomes
affine after base change to the limit, then it is already affine after base change to some later
stage.

## Main results

* `AlgebraicGeometry.exists_isAffineHom_of_isLimit` descends affineness of a morphism from the
  inverse limit to a finite stage.

## Implementation notes

The indexing category for descent is essentially small relative to the scheme universe,
expressing the set-sized inverse systems in the source.

Schemes over the chosen initial stage are represented as objects of its over category. Base change
is the functor `CategoryTheory.Over.pullback`. The condition that a stage is later than the chosen
one is represented, for a cofiltered indexing category, by a morphism from that stage to the chosen
stage. The index objects, index morphisms, and schemes have independent universes.

## References

* [Stacks Project, Tag 01ZN](https://stacks.math.columbia.edu/tag/01ZN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local simp] AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE

universe w v u

namespace AlgebraicGeometry

/-! ### The diagram of inverse images of a quasi-compact open -/

section Opens

variable {J : Type v} [Category.{w} J]

/-- Pulling back an open of the base along a stage of the system and then along a transition
morphism over the base is pulling it back along the source stage. -/
private lemma preimage_map_left_preimage_map_hom (E : J ⥤ Scheme.{u}) {j₀ : J}
    (U : (E.obj j₀).Opens) {j k : Over j₀} (f : j ⟶ k) :
    E.map f.left ⁻¹ᵁ (E.map k.hom ⁻¹ᵁ U) = E.map j.hom ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, ← E.map_comp, Over.w f]

/-- The diagram of inverse images of an open subscheme of one stage along the transition
morphisms of the inverse system. -/
private noncomputable def preimageStageDiagram (E : J ⥤ Scheme.{u}) (j₀ : J)
    (U : (E.obj j₀).Opens) : Over j₀ ⥤ Scheme.{u} where
  obj j := E.map j.hom ⁻¹ᵁ U
  map {j k} f := (E.map f.left).resLE _ _
    (preimage_map_left_preimage_map_hom E U f).ge
  map_id j := by
    apply (cancel_mono (E.map j.hom ⁻¹ᵁ U).ι).mp
    simp
  map_comp f g := by simp [Scheme.Hom.resLE_comp_resLE]

/-- The cone on `AlgebraicGeometry.preimageStageDiagram` whose point is the inverse image of `U`
in the limit. -/
private noncomputable def preimageStageCone (E : J ⥤ Scheme.{u}) (d : Cone E) (j₀ : J)
    (U : (E.obj j₀).Opens) : Cone (preimageStageDiagram E j₀ U) where
  pt := d.π.app j₀ ⁻¹ᵁ U
  π.app j := (d.π.app j.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, d.w])
  π.naturality := by
    intro j k f
    dsimp [preimageStageDiagram]
    simp [Scheme.Hom.resLE_comp_resLE, d.w f.left]

/-- The inverse image of an open subscheme of one stage in the limit is the limit of its inverse
images at the later stages. -/
private noncomputable def preimageStageConeIsLimit [IsCofiltered J] (E : J ⥤ Scheme.{u})
    (d : Cone E) (hd : IsLimit d) (j₀ : J) (U : (E.obj j₀).Opens) :
    IsLimit (preimageStageCone E d j₀ U) := by
  let α : preimageStageDiagram E j₀ U ⟶ Over.forget j₀ ⋙ E :=
    { app j := Scheme.Opens.ι _
      naturality := by
        intro j k f
        simp [preimageStageDiagram, Scheme.Hom.resLE_comp_ι] }
  let cF := preimageStageCone E d j₀ U
  let cG := Cone.whisker (Over.forget j₀) d
  have : IsConnected (Over j₀) := CategoryTheory.isConnected_of_hasTerminal (C := Over j₀)
  have hcG : IsLimit cG := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j₀) d).symm hd
  have (j : Over j₀) : IsOpenImmersion (α.app j) := by
    dsimp [α, preimageStageDiagram]
    infer_instance
  let φ : (Cone.postcompose α).obj cF ⟶ cG :=
    { hom := (d.π.app j₀ ⁻¹ᵁ U).ι
      w := by
        intro j
        dsimp [cF, preimageStageCone, cG, α, preimageStageDiagram]
        rw [Scheme.Hom.resLE_comp_ι] }
  have : IsOpenImmersion φ.hom := by
    change IsOpenImmersion (d.π.app j₀ ⁻¹ᵁ U).ι
    infer_instance
  exact isLimitOfIsPullbackOfIsConnected α cF cG φ
    (fun j ↦ by
      apply IsOpenImmersion.isPullback _ _ _ _ (φ.w j)
      simp [φ, cF, cG, α, preimageStageCone, preimageStageDiagram,
        ← Scheme.Hom.comp_preimage]) hcG

/-- Restricting a morphism to opens of its source and target does not move the underlying
points. -/
private lemma val_resLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {S : Y.Opens} {T : X.Opens}
    (e : T ≤ f ⁻¹ᵁ S) (x : T.toScheme) : ((f.resLE S T e) x).1 = f x.1 := by
  have h := congrArg (fun q : T.toScheme ⟶ Y => q x) (Scheme.Hom.resLE_comp_ι f e)
  simp only [Scheme.Hom.comp_apply] at h
  exact h

/-- A point of the restricted source lies in an open of the restricted target exactly when its
image under the unrestricted morphism does. -/
private lemma mem_resLE_apply_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {S : Y.Opens} {T : X.Opens}
    (e : T ≤ f ⁻¹ᵁ S) (x : T.toScheme) (hx : f x.1 ∈ S) (W : S.toScheme.Opens) :
    (f.resLE S T e) x ∈ W ↔ (⟨f x.1, hx⟩ : S.toScheme) ∈ W := by
  rw [show (f.resLE S T e) x = (⟨f x.1, hx⟩ : S.toScheme) from
    Subtype.ext (val_resLE_apply f e x)]
  exact Iff.rfl

/-- If the inverse image in the limit of a quasi-compact open of one stage is affine, then its
inverse image at some later stage is already affine. -/
private lemma exists_isAffine_preimage [IsCofiltered J] [EssentiallySmall.{u} J]
    (E : J ⥤ Scheme.{u}) (d : Cone E) (hd : IsLimit d)
    [∀ {j k : J} (g : j ⟶ k), IsAffineHom (E.map g)]
    [∀ j, CompactSpace (E.obj j)] [∀ j, QuasiSeparatedSpace (E.obj j)]
    (j₀ : J) (U : (E.obj j₀).Opens) (hU : IsCompact (U : Set (E.obj j₀)))
    (hlim : IsAffine ((d.π.app j₀) ⁻¹ᵁ U)) :
    ∃ (j : J) (h : j ⟶ j₀), IsAffine (E.map h ⁻¹ᵁ U) := by
  let E' := preimageStageDiagram E j₀ U
  let d' := preimageStageCone E d j₀ U
  have hd' : IsLimit d' := preimageStageConeIsLimit E d hd j₀ U
  have : InitiallySmall.{u} (Over j₀) := initiallySmall_of_essentiallySmall _
  have (j : Over j₀) : CompactSpace (E'.obj j) := by
    dsimp [E', preimageStageDiagram]
    exact isCompact_iff_compactSpace.mp <| QuasiCompact.isCompact_preimage
      (f := E.map j.hom) _ U.2 hU
  have (j : Over j₀) : QuasiSeparatedSpace (E'.obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (E.map j.hom ⁻¹ᵁ U).2).mp
      (.of_quasiSeparatedSpace _)
  have : ∀ {j k : Over j₀} (g : j ⟶ k), IsAffineHom (E'.map g) := by
    intro j k g
    dsimp [E', preimageStageDiagram]
    refine ⟨fun V hV ↦ ?_⟩
    convert! ((hV.image_of_isOpenImmersion (E.map k.hom ⁻¹ᵁ U).ι).preimage
      (E.map g.left)).preimage_of_isOpenImmersion (E.map j.hom ⁻¹ᵁ U).ι ?_
    · ext x
      show _ ∈ V ↔ _
      refine ⟨fun hx ↦ ⟨⟨(E.map g.left).base x.1, ?_⟩, ?_, rfl⟩, ?_⟩
      · exact (preimage_map_left_preimage_map_hom E U g).ge x.2
      · exact (mem_resLE_apply_iff (E.map g.left) _ x _ V).mp hx
      · rintro ⟨⟨_, hU⟩, hV, rfl⟩
        exact (mem_resLE_apply_iff (E.map g.left) _ x hU V).mpr hV
    · simp only [Scheme.Opens.opensRange_ι]
      rintro x ⟨⟨y, hy : (E.map k.hom).base y ∈ U⟩, hV, heq⟩
      obtain rfl : y = (E.map g.left).base x := congr($heq)
      exact (preimage_map_left_preimage_map_hom E U g).le hy
  have : IsAffine d'.pt := hlim
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit_of_initiallySmall E' d' hd'
  exact ⟨j.left, j.hom, hj⟩

end Opens

/-! ### Descending affineness -/

/-- If a morphism over one stage of a cofiltered inverse system becomes affine
after base change to the limit, it becomes affine at some later stage. -/
@[stacks 01ZN]
theorem exists_isAffineHom_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [IsAffineHom ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (hi : i ⟶ i₀),
      IsAffineHom ((Over.pullback (D.map hi)).map f₀).left := by
  classical
  let A₀ : Over i₀ := Over.mk (𝟙 i₀)
  let FX := baseChangeDiagram D i₀ X₀
  let FY := baseChangeDiagram D i₀ Y₀
  let cX := baseChangeCone D c i₀ X₀
  let cY := baseChangeCone D c i₀ Y₀
  have hcX : IsLimit cX := baseChangeConeIsLimit D hc i₀ X₀
  have : ∀ {A B : Over i₀} (g : A ⟶ B), IsAffineHom (FX.map g) :=
    fun g ↦ isAffineHom_baseChangeDiagram_map D i₀ X₀ g
  have (A : Over i₀) : CompactSpace (FX.obj A) := compactSpace_baseChangeDiagram_obj D i₀ X₀ A
  have (A : Over i₀) : QuasiSeparatedSpace (FX.obj A) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ X₀ A
  have : ∀ {A B : Over i₀} (g : A ⟶ B), IsAffineHom (FY.map g) :=
    fun g ↦ isAffineHom_baseChangeDiagram_map D i₀ Y₀ g
  have (A : Over i₀) : CompactSpace (FY.obj A) := compactSpace_baseChangeDiagram_obj D i₀ Y₀ A
  have (A : Over i₀) : QuasiSeparatedSpace (FY.obj A) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ Y₀ A
  let h : FX ⟶ FY := baseChangeDiagramMap D i₀ f₀
  let eX : cX.pt ≅ ((Over.pullback (c.π.app i₀)).obj X₀).left :=
    pullbackSymmetry (c.π.app i₀) X₀.hom
  let eY : cY.pt ≅ ((Over.pullback (c.π.app i₀)).obj Y₀).left :=
    pullbackSymmetry (c.π.app i₀) Y₀.hom
  let fLimit : cX.pt ⟶ cY.pt :=
    eX.hom ≫ ((Over.pullback (c.π.app i₀)).map f₀).left ≫ eY.inv
  let τY : FY.obj A₀ ⟶ Y₀.left := pullback.snd (D.map (𝟙 i₀)) Y₀.hom
  have : IsIso (D.map (𝟙 i₀)) := by
    rw [D.map_id]
    infer_instance
  have : IsIso τY := by
    dsimp [τY]
    exact (IsPullback.of_hasPullback (D.map (𝟙 i₀)) Y₀.hom).isIso_snd_of_isIso
  let C := Y₀.left.affineCover.finiteSubcover
  let V (j : C.I₀) : Y₀.left.Opens := (C.f j).opensRange
  have hV (j : C.I₀) : IsAffineOpen (V j) := isAffineOpen_opensRange (C.f j)
  let V₀ (j : C.I₀) : (FY.obj A₀).Opens := τY ⁻¹ᵁ V j
  have hV₀ (j : C.I₀) : IsAffineOpen (V₀ j) := (hV j).preimage τY
  let U₀ (j : C.I₀) : (FX.obj A₀).Opens := h.app A₀ ⁻¹ᵁ V₀ j
  have hU₀compact (j : C.I₀) : IsCompact (U₀ j : Set (FX.obj A₀)) :=
    (h.app A₀).isCompact_preimage (hV₀ j).isCompact
  let qY : cY.pt ⟶ Y₀.left := pullback.snd (c.π.app i₀) Y₀.hom
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have : IsAffineHom qY := by
    dsimp [qY]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (c.π.app i₀) Y₀.hom)
      (isAffineHom_π_app_of_initiallySmall D c hc i₀)
  have hlimU₀ (j : C.I₀) : IsAffine (cX.π.app A₀ ⁻¹ᵁ U₀ j) := by
    let WLimit : cY.pt.Opens := qY ⁻¹ᵁ V j
    have hWLimit : IsAffineOpen WLimit := (hV j).preimage qY
    have hfLimitW : IsAffineOpen (fLimit ⁻¹ᵁ WLimit) := hWLimit.preimage fLimit
    have hfac : fLimit ≫ qY = cX.π.app A₀ ≫ h.app A₀ ≫ τY := by
      show ((pullbackSymmetry (c.π.app i₀) X₀.hom).hom ≫
            ((Over.pullback (c.π.app i₀)).map f₀).left ≫
              (pullbackSymmetry (c.π.app i₀) Y₀.hom).inv) ≫
            pullback.snd (c.π.app i₀) Y₀.hom =
          baseChangeTransition (D.map A₀.hom) (c.π.app i₀) (c.π.app A₀.left) (by simp) X₀ ≫
            baseChangeMap (D.map A₀.hom) X₀ Y₀ f₀ ≫ pullback.snd (D.map A₀.hom) Y₀.hom
      simp only [Category.assoc, pullbackSymmetry_inv_comp_snd, overPullback_map_left_fst,
        pullbackSymmetry_hom_comp_fst_assoc, baseChangeMap_snd, baseChangeTransition_snd_assoc]
    have heq : cX.π.app A₀ ⁻¹ᵁ U₀ j = fLimit ⁻¹ᵁ WLimit := by
      show (cX.π.app A₀ ≫ h.app A₀ ≫ τY) ⁻¹ᵁ V j = (fLimit ≫ qY) ⁻¹ᵁ V j
      rw [hfac]
    rwa [← heq] at hfLimitW
  choose A' hA' hA'U using fun j : C.I₀ =>
    exists_isAffine_preimage FX cX hcX A₀ (U₀ j) (hU₀compact j) (hlimU₀ j)
  have : Fintype C.I₀ := Fintype.ofFinite C.I₀
  obtain ⟨A, hA⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image A')
  let m (j : C.I₀) : A ⟶ A' j := (hA (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  let h₀ : A ⟶ A₀ := Over.homMk A.hom
  have hm₀ (j : C.I₀) : m j ≫ hA' j = h₀ := Over.mkIdTerminal.hom_ext _ _
  have hCover (z : FY.obj A) : ∃ j : C.I₀, z ∈ FY.map h₀ ⁻¹ᵁ V₀ j := by
    let y : Y₀.left := τY (FY.map h₀ z)
    exact ⟨C.idx y, C.covers y⟩
  have hAff : IsAffineHom (h.app A) := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro z
    obtain ⟨j, hz⟩ := hCover z
    let W : (FY.obj A).Opens := FY.map h₀ ⁻¹ᵁ V₀ j
    let Z : (FX.obj A).Opens := FX.map h₀ ⁻¹ᵁ U₀ j
    have hW : IsAffineOpen W := (hV₀ j).preimage (FY.map h₀)
    have hZeq : h.app A ⁻¹ᵁ W = Z := by
      show (h.app A ≫ FY.map h₀) ⁻¹ᵁ V₀ j = (FX.map h₀ ≫ h.app A₀) ⁻¹ᵁ V₀ j
      rw [h.naturality h₀]
    have hZ : IsAffineOpen Z := by
      dsimp [Z]
      rw [← hm₀ j, Functor.map_comp, Scheme.Hom.comp_preimage]
      have hZj : IsAffineOpen (FX.map (hA' j) ⁻¹ᵁ U₀ j) := hA'U j
      exact hZj.preimage (FX.map (m j))
    exact ⟨W, hz, hW, hZeq ▸ hZ⟩
  have : MorphismProperty.RespectsIso @IsAffineHom :=
    MorphismProperty.RespectsIso.mk @IsAffineHom
      (fun _ f hf => by have : IsAffineHom f := hf; infer_instance)
      (fun _ f hf => by have : IsAffineHom f := hf; infer_instance)
  exact ⟨A.left, A.hom,
    (baseChangeMap_prop_iff (@IsAffineHom) (D.map A.hom) X₀ Y₀ f₀).1 hAff⟩

/-! ### Global sections of a cofiltered limit

These are shared by the descent arguments for the individual morphism properties, which read the
descended property off the global sections of the base-change diagram over an affine chart.
-/

/-- Global sections of the diagram of base changes of an affine scheme over a stage form a
filtered colimit, whose colimit is the sections of the base change to the limit. -/
lemma nonempty_isColimit_sections_baseChange {I : Type v} [Category.{w} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (X₀ : Over (D.obj i₀))
    [IsAffine X₀.left] :
    Nonempty (IsColimit (Scheme.Γ.mapCocone (baseChangeCone D c i₀ X₀).op)) := by
  have : ∀ {A B : Over i₀} (g : A ⟶ B), IsAffineHom ((baseChangeDiagram D i₀ X₀).map g) :=
    fun g ↦ isAffineHom_baseChangeDiagram_map D i₀ X₀ g
  have (A : Over i₀) : IsAffine ((baseChangeDiagram D i₀ X₀).obj A) :=
    isAffine_baseChangeDiagram_obj D i₀ X₀ A
  have : ∀ A : (Over i₀)ᵒᵖ, IsAffine ((baseChangeDiagram D i₀ X₀).op.obj A).unop :=
    fun A ↦ isAffine_baseChangeDiagram_obj D i₀ X₀ A.unop
  exact ⟨isColimitOfPreserves Scheme.Γ (baseChangeConeIsLimit D hc i₀ X₀).op⟩

/-- Elements of a filtered colimit of rings come from a stage. -/
lemma ring_colimit_surjective {ι : Type v} [PartialOrder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (F : ι ⥤ CommRingCat.{u})
    [PreservesColimit F (forget CommRingCat)] (c : Cocone F) (hc : IsColimit c) :
    ∀ r : c.pt, ∃ i, ∃ x : F.obj i, (c.ι.app i).hom x = r := fun r =>
  Types.jointly_surjective _ (isColimitOfPreserves (forget CommRingCat) hc) r

/-- An element that vanishes in a filtered colimit of rings vanishes at a later stage. -/
lemma ring_colimit_eventually_zero {ι : Type v} [PartialOrder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (F : ι ⥤ CommRingCat.{u})
    [PreservesColimit F (forget CommRingCat)] (c : Cocone F) (hc : IsColimit c) :
    ∀ i (x : F.obj i), (c.ι.app i).hom x = 0 →
      ∃ j, ∃ h : i ≤ j, (F.map (homOfLE h)).hom x = 0 := by
  intro i x hx
  have hc' := isColimitOfPreserves (forget CommRingCat) hc
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x 0).mp (by simpa using hx)
  refine ⟨j, leOfHom f, ?_⟩
  change (F.map f).hom x = (F.map f).hom 0 at hf
  have hfe : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
  simpa only [← hfe, map_zero] using hf

/-- In a pushout square of commutative rings, a finite generating set of the left algebra maps to
a generating set of the right one. -/
lemma adjoin_image_eq_top_of_isPushout {R A B X : CommRingCat.{u}} {f : R ⟶ A}
    {g : R ⟶ B} {a : A ⟶ X} {b : B ⟶ X} (H : IsPushout f g a b) (s : Finset A)
    (hs : letI := f.hom.toAlgebra; Algebra.adjoin R (s : Set A) = ⊤) :
    letI := b.hom.toAlgebra
    Algebra.adjoin B (a.hom '' (s : Set A)) = ⊤ := by
  classical
  let : Algebra R A := f.hom.toAlgebra
  let : Algebra R B := g.hom.toAlgebra
  let : Algebra R X := (a.hom.comp f.hom).toAlgebra
  let : Algebra B X := b.hom.toAlgebra
  have hcomm : a.hom.comp f.hom = b.hom.comp g.hom := congrArg (fun h : R ⟶ X => h.hom) H.w
  let : IsScalarTower R B X := IsScalarTower.of_algebraMap_eq fun r => by
    show (a.hom.comp f.hom) r = (b.hom.comp g.hom) r
    exact DFunLike.congr_fun hcomm r
  let C := Algebra.adjoin B (a.hom '' (s : Set A))
  have ha : Set.range a.hom ⊆ C := by
    rintro x ⟨y, rfl⟩
    have hy : y ∈ Algebra.adjoin R (s : Set A) := hs ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    | algebraMap r =>
        show (a.hom.comp f.hom) r ∈ C
        rw [hcomm]
        exact C.algebraMap_mem (g.hom r)
    | add x y hx hy ihx ihy => simpa only [map_add, SetLike.mem_coe] using C.add_mem ihx ihy
    | mul x y hx hy ihx ihy => simpa only [map_mul, SetLike.mem_coe] using C.mul_mem ihx ihy
  have hb : Set.range b.hom ⊆ C := Set.range_subset_iff.2 C.algebraMap_mem
  have hle : Subring.closure (Set.range a.hom ∪ Set.range b.hom) ≤ C.toSubring :=
    Subring.closure_le.2 (Set.union_subset ha hb)
  rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout H] at hle
  exact top_le_iff.mp hle

end AlgebraicGeometry
