module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion

/-!
# Immersions descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. If
a morphism over one stage is locally of finite type and becomes an immersion after base change to
the limit, then it is an immersion after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_isImmersion_baseChange_of_isLimit` descends an immersion from the
  limit to a finite stage.
* `AlgebraicGeometry.exists_compactOpen_covering_range` shrinks an open containing the image of a
  quasi-compact scheme to a quasi-compact one.

## Implementation notes

Schemes over a stage are represented by objects of its over category, and base change by
`CategoryTheory.Over.pullback`. A morphism `i ⟶ i₀` represents a later stage in the cofiltered
indexing category, generalizing the directed system of the source. The index category is
essentially small relative to the scheme universe, as required for descent along this limit.

An immersion factors as a closed immersion into an open subscheme. The proof chooses a
quasi-compact open of the limit containing the image, descends it to a quasi-compact open of a
stage, and applies the descent of closed immersions to the resulting factorisation.

## References

* [Stacks Project, Tag 0GTB](https://stacks.math.columbia.edu/tag/0GTB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Topology

universe w v u

namespace AlgebraicGeometry

/-! ### Factoring an immersion through a quasi-compact open -/

/-- The image of a morphism with quasi-compact source inside an open subscheme is contained in a
quasi-compact open subscheme of that open.

This is the step "since `Spec A` is quasi-compact we may replace `W` by a quasi-compact open
still containing the image" that opens several of the limit arguments of Stacks 32.13 and 32.14:
the descent of an open subscheme to a finite stage ([Stacks, Tag 01Z4] (1), Mathlib's
`AlgebraicGeometry.exists_preimage_eq`) applies only to a *quasi-compact* open, while the
statements being proved quantify over an arbitrary one. -/
lemma exists_compactOpen_covering_range {X Y : Scheme.{u}} (f : Y ⟶ X) [CompactSpace Y]
    {W : X.Opens} (hW : Set.range f.base ⊆ W) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ U ≤ W ∧ Set.range f.base ⊆ U := by
  classical
  let A : Type _ := {V : X.affineOpens // (V : X.Opens) ≤ W}
  have hcover : Set.range f.base ⊆ ⋃ a : A, (a.1.1 : Set X) := by
    rintro x ⟨y, rfl⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hW ⟨y, rfl⟩) W.isOpen
    exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  have hcompact : IsCompact (Set.range f.base) := isCompact_range f.continuous
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover (fun a : A => (a.1.1 : Set X))
    (fun a => (a.1.1).isOpen) hcover
  let J := {a : A // a ∈ s}
  let U : X.Opens := ⨆ a : J, (a.1.1 : X.Opens)
  have hcoe : (U : Set X) = ⋃ a : J, (a.1.1 : Set X) := by
    ext x
    simp [U, J, Set.mem_iUnion]
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact isCompact_iUnion fun a => (a.1.1).2.isCompact
  · exact iSup_le fun a => a.1.2
  · intro x hx
    rw [hcoe]
    obtain ⟨a, hat, hax⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨a, hat⟩, hax⟩

/-- A closed immersion whose source maps into an open subscheme restricts to a closed immersion
into that open subscheme. -/
private lemma closedImmersion_resLE_of_preimage_top {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (U : X.Opens) (hU : f ⁻¹ᵁ U = ⊤) :
    IsClosedImmersion (Y.topIso.inv ≫ f.resLE U ⊤ (by simp [hU])) := by
  have hres : IsClosedImmersion (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip inferInstance
  have hres' : IsClosedImmersion (f.resLE U ⊤ (by simp [hU])) :=
    (f.resLE_congr le_rfl rfl hU @IsClosedImmersion).mp hres
  have : IsIso Y.topIso.inv := inferInstance
  exact IsClosedImmersion.comp _ _

/-- An immersion with quasi-compact source factors as a closed immersion into a quasi-compact
open subscheme of its target. -/
private lemma exists_compactOpen_closed_factor {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    [IsImmersion f] :
    ∃ (U : Y.Opens), IsCompact (U : Set Y) ∧ Set.range f.base ⊆ U ∧
      ∃ (g : X ⟶ U.toScheme), IsClosedImmersion g ∧ g ≫ U.ι = f := by
  classical
  obtain ⟨Z, g, k, hg, hk, hgf⟩ := (IsImmersion.isImmersion_iff_exists (f := f)).mp inferInstance
  have : IsClosedImmersion g := hg
  have : IsOpenImmersion k := hk
  let W := k.opensRange
  have hRangeW : Set.range f.base ⊆ W := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g.base y, by
      simpa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using
        congrArg (fun q : X ⟶ Y => q.base y) hgf⟩
  obtain ⟨U, hUcompact, hUW, hRangeU⟩ := exists_compactOpen_covering_range f hRangeW
  let UW := W.ι ⁻¹ᵁ U
  let gW : X ⟶ W.toScheme := g ≫ (Scheme.Hom.isoOpensRange k).hom
  have hfactorW : gW ≫ W.ι = f := by
    dsimp [gW]
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hgf]
  have hpre : gW ⁻¹ᵁ UW = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hfactorW]
    exact top_unique fun x _ => hRangeU ⟨x, rfl⟩
  let gU0 := X.topIso.inv ≫ gW.resLE UW ⊤ (by simp [hpre])
  have hgU0 : IsClosedImmersion gU0 := closedImmersion_resLE_of_preimage_top gW UW hpre
  let j := UW.ι ≫ W.ι
  have : IsOpenImmersion j := inferInstance
  have hrangeJ : j.opensRange = U := by
    dsimp [j, UW]
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUW
  let eU := j.isoOpensRange ≪≫ Scheme.isoOfEq Y hrangeJ
  have heU : eU.hom ≫ U.ι = j := by
    dsimp [eU]
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]
  let fU := gU0 ≫ eU.hom
  have hfUclosed : IsClosedImmersion fU := by
    dsimp [fU]
    infer_instance
  have hfU : fU ≫ U.ι = f := by
    dsimp [fU]
    have hresComp : gW.resLE UW ⊤ (by simp [hpre]) ≫ UW.ι = (⊤ : X.Opens).ι ≫ gW :=
      Scheme.Hom.resLE_comp_ι gW (U := UW) (V := ⊤) (by simp [hpre])
    calc
      _ = gU0 ≫ j := by rw [Category.assoc, heU]
      _ = (X.topIso.inv ≫ ((⊤ : X.Opens).ι ≫ gW)) ≫ W.ι := by
        dsimp [gU0, j]
        exact congrArg (fun q => X.topIso.inv ≫ q ≫ W.ι) hresComp
      _ = f := by simp [hfactorW]
  exact ⟨U, hUcompact, hRangeU, fU, hfUclosed, hfU⟩

/-- If the base change of a closed-immersion factorisation through an open subscheme is compared
with a factorisation at the base, the base-changed factor is again a closed immersion. -/
private lemma closedImmersion_baseChange_of_open_factor {X Y X₀ Y₀ : Scheme.{u}} {a : X ⟶ X₀}
    {f : X ⟶ Y} {f₀ : X₀ ⟶ Y₀} {b : Y ⟶ Y₀} (h : IsPullback a f f₀ b) (U : Y.Opens)
    (U₀ : Y₀.Opens) (hU : b ⁻¹ᵁ U₀ = U) (g : X ⟶ U.toScheme) [IsClosedImmersion g]
    (hg : g ≫ U.ι = f) (g₀ : X₀ ⟶ U₀.toScheme) (hg₀ : g₀ ≫ U₀.ι = f₀) :
    IsClosedImmersion ((Over.pullback b).map
      (Over.homMk g₀ hg₀ : Over.mk f₀ ⟶ Over.mk U₀.ι)).left := by
  let v := b.resLE U₀ U hU.ge
  have hv : v ≫ U₀.ι = U.ι ≫ b := Scheme.Hom.resLE_comp_ι _ _
  have hpb : IsPullback v U.ι U₀.ι b :=
    IsOpenImmersion.isPullback _ _ _ _ hv.symm (by
      simpa only [Scheme.Opens.opensRange_ι] using hU)
  have hgv : a ≫ g₀ = g ≫ v := by
    apply (cancel_mono U₀.ι).mp
    rw [Category.assoc, Category.assoc, hg₀, hv, ← Category.assoc, hg]
    exact h.w
  let e : Arrow.mk g ≅ Arrow.mk ((Over.pullback b).map
      (Over.homMk g₀ hg₀ : Over.mk f₀ ⟶ Over.mk U₀.ι)).left :=
    Arrow.isoMk h.isoPullback hpb.isoPullback (by
      apply pullback.hom_ext
      · simp only [Arrow.mk_hom, Category.assoc]
        rw [overPullback_map_left_fst]
        simpa using hgv
      · simp only [Arrow.mk_hom, Category.assoc]
        rw [overPullback_map_left_snd]
        simpa using hg.symm)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mp inferInstance

/-! ### Descending an immersion in a cartesian diagram -/

/-- If a cartesian morphism of cofiltered diagrams of quasi-compact quasi-separated schemes with
affine transition morphisms is locally of finite type at every stage and an immersion in the
limit, then it is an immersion at some stage. -/
private lemma exists_isImmersion_of_cartesian {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (DX DY : I ⥤ Scheme.{u}) (n : DX ⟶ DY) (cX : Cone DX)
    (cY : Cone DY) (hX : IsLimit cX) (hY : IsLimit cY) (f : cX.pt ⟶ cY.pt)
    (hlim : ∀ i, IsPullback (cX.π.app i) f (n.app i) (cY.π.app i))
    (hcart : ∀ {i j} (e : i ⟶ j), IsPullback (DX.map e) (n.app i) (n.app j) (DY.map e))
    [∀ {i j} (e : i ⟶ j), IsAffineHom (DX.map e)]
    [∀ {i j} (e : i ⟶ j), IsAffineHom (DY.map e)]
    [∀ i, CompactSpace (DX.obj i)] [∀ i, QuasiSeparatedSpace (DX.obj i)]
    [∀ i, CompactSpace (DY.obj i)] [∀ i, QuasiSeparatedSpace (DY.obj i)]
    [∀ i, LocallyOfFiniteType (n.app i)] [IsImmersion f] :
    ∃ i, IsImmersion (n.app i) := by
  classical
  have : InitiallySmall.{u} I := initiallySmall_of_essentiallySmall I
  have : CompactSpace cX.pt := Scheme.compactSpace_of_isLimit_of_initiallySmall DX cX hX
  obtain ⟨V, hV, hRange, g, hg, hgf⟩ := exists_compactOpen_closed_factor f
  have : IsClosedImmersion g := hg
  obtain ⟨i, U, hU, hpre⟩ := exists_preimage_eq_of_initiallySmall DY cY hY V hV
  have htop : cX.π.app i ⁻¹ᵁ (n.app i ⁻¹ᵁ U) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, (hlim i).w, Scheme.Hom.comp_preimage, hpre]
    exact top_unique (fun x _ => hRange ⟨x, rfl⟩)
  obtain ⟨j, e, he⟩ := exists_map_eq_top_of_initiallySmall DX cX hX (n.app i ⁻¹ᵁ U) htop
  let Uj := DY.map e ⁻¹ᵁ U
  have hUj : IsCompact (Uj : Set (DY.obj j)) := QuasiCompact.isCompact_preimage _ U.isOpen hU
  have hprej : cY.π.app j ⁻¹ᵁ Uj = V := by
    dsimp [Uj]
    rw [← Scheme.Hom.comp_preimage, cY.w, hpre]
  have htopj : n.app j ⁻¹ᵁ Uj = ⊤ := by
    dsimp [Uj]
    rw [← Scheme.Hom.comp_preimage, ← n.naturality, Scheme.Hom.comp_preimage, he]
  let gj := IsOpenImmersion.lift Uj.ι (n.app j) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact htopj.ge (Set.mem_univ x))
  have hgj : gj ≫ Uj.ι = n.app j := IsOpenImmersion.lift_fac _ _ _
  have : CompactSpace Uj.toScheme := isCompact_iff_compactSpace.mp hUj
  have : QuasiSeparatedSpace Uj.toScheme := quasiSeparatedSpace_of_quasiSeparated Uj.ι
  have : LocallyOfFiniteType gj := by
    have : LocallyOfFiniteType (gj ≫ Uj.ι) := hgj.symm ▸ inferInstance
    exact locallyOfFiniteType_of_comp gj Uj.ι
  let gjOver : Over.mk (n.app j) ⟶ Over.mk Uj.ι := Over.homMk gj hgj
  have : IsClosedImmersion ((Over.pullback (cY.π.app j)).map gjOver).left :=
    closedImmersion_baseChange_of_open_factor (hlim j) V Uj hprej g hgf gj hgj
  have : CompactSpace (Over.mk (n.app j)).left := inferInstanceAs (CompactSpace (DX.obj j))
  have : QuasiSeparatedSpace (Over.mk (n.app j)).left :=
    inferInstanceAs (QuasiSeparatedSpace (DX.obj j))
  have : CompactSpace (Over.mk Uj.ι).left := inferInstanceAs (CompactSpace Uj.toScheme)
  have : QuasiSeparatedSpace (Over.mk Uj.ι).left :=
    inferInstanceAs (QuasiSeparatedSpace Uj.toScheme)
  have : LocallyOfFiniteType gjOver.left := inferInstanceAs (LocallyOfFiniteType gj)
  obtain ⟨k, t, ht⟩ := exists_isClosedImmersion_baseChange_of_isLimit DY cY hY j
    (Over.mk (n.app j)) (Over.mk Uj.ι) gjOver
  have : IsClosedImmersion ((Over.pullback (DY.map t)).map gjOver).left := ht
  have hcomp : ((Over.pullback (DY.map t)).map gjOver).left ≫
      pullback.snd Uj.ι (DY.map t) = pullback.snd (n.app j) (DY.map t) :=
    ((Over.pullback (DY.map t)).map gjOver).w
  have : IsImmersion (pullback.snd (n.app j) (DY.map t)) := by
    rw [← hcomp]
    infer_instance
  refine ⟨k, ?_⟩
  rw [← (hcart t).isoPullback_hom_snd]
  infer_instance

/-! ### Descending immersions -/

/-- If a locally finite type morphism becomes an immersion over the inverse limit,
it becomes an immersion at a later stage. -/
@[stacks 0GTB]
theorem exists_isImmersion_baseChange_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [IsImmersion ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (hi : i ⟶ i₀),
      IsImmersion ((Over.pullback (D.map hi)).map f₀).left := by
  classical
  have : MorphismProperty.RespectsIso @IsImmersion :=
    MorphismProperty.RespectsIso.mk @IsImmersion
      (fun _ f hf => by have : IsImmersion f := hf; infer_instance)
      (fun _ f hf => by have : IsImmersion f := hf; infer_instance)
  let DX := baseChangeDiagram D i₀ X₀
  let DY := baseChangeDiagram D i₀ Y₀
  let n := baseChangeDiagramMap D i₀ f₀
  let cX := baseChangeCone D c i₀ X₀
  let cY := baseChangeCone D c i₀ Y₀
  have hX : IsLimit cX := baseChangeConeIsLimit D hc i₀ X₀
  have hY : IsLimit cY := baseChangeConeIsLimit D hc i₀ Y₀
  have {i j : Over i₀} (e : i ⟶ j) : IsAffineHom (DX.map e) :=
    isAffineHom_baseChangeDiagram_map D i₀ X₀ e
  have {i j : Over i₀} (e : i ⟶ j) : IsAffineHom (DY.map e) :=
    isAffineHom_baseChangeDiagram_map D i₀ Y₀ e
  have (i : Over i₀) : CompactSpace (DX.obj i) := compactSpace_baseChangeDiagram_obj D i₀ X₀ i
  have (i : Over i₀) : QuasiSeparatedSpace (DX.obj i) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ X₀ i
  have (i : Over i₀) : CompactSpace (DY.obj i) := compactSpace_baseChangeDiagram_obj D i₀ Y₀ i
  have (i : Over i₀) : QuasiSeparatedSpace (DY.obj i) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ Y₀ i
  have (i : Over i₀) : LocallyOfFiniteType (n.app i) :=
    MorphismProperty.of_isPullback (baseChangeMap_isPullback (D.map i.hom) X₀ Y₀ f₀).flip
      inferInstance
  have : @IsImmersion cX.pt cY.pt (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) :=
    (baseChangeMap_prop_iff (@IsImmersion) (c.π.app i₀) X₀ Y₀ f₀).2 inferInstance
  obtain ⟨i, hi⟩ := exists_isImmersion_of_cartesian DX DY n cX cY hX hY
    (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀)
    (fun a ↦ baseChangeCone_π_isPullback D i₀ f₀ c a)
    (fun e ↦ baseChangeDiagramMap_isPullback D i₀ f₀ e)
  exact ⟨i.left, i.hom,
    (baseChangeMap_prop_iff (@IsImmersion) (D.map i.hom) X₀ Y₀ f₀).1 hi⟩

end AlgebraicGeometry
