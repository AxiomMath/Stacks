module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantChartLimit

/-!
# Limit bridges of chart systems along arbitrary affine points

`AlgebraicGeometry.Space.HasChartLimitBridges D` asks that every chart system of a stage of `D`
along an *étale* affine point have a limit bridge: a limit in the big fppf site which is also
the limit of the underlying affine schemes. The arguments of Stacks 07SK need limit bridges of
chart systems along *arbitrary* affine points `U₀ ⟶ D i₀`, which is
`AlgebraicGeometry.Space.HasAllChartLimitBridges D`.

The étale case implies the general one. Choose an affine étale surjective chart `V₀ ⟶ D i₀` and
an affine `W` étale and surjective over `U₀` mapping to `V₀` over `D i₀`. Let `L ⊆ lim U_j` be
the limit of the charts `U_j = U₀ ×_{D i₀} D_j` in the site, a closed subscheme of the limit of
the schemes. The fibre product `T = W ×_{V₀} lim V_j` lies in the site, since `lim V_j` does by
the étale case, and it is the limit of the schemes `W ×_{V₀} V_j = W ×_{U₀} U_j`. A function on
`U_k` vanishing on `L` vanishes on `T`, hence on some `W ×_{U₀} U_{k'}`, hence on `U_{k'}`, the
morphism `W ×_{U₀} U_{k'} ⟶ U_{k'}` being faithfully flat. So `L` is all of `lim U_j`.

## Main results

* `AlgebraicGeometry.Space.HasAllChartLimitBridges`: every chart system of a stage along an
  affine point has a limit bridge.
* `AlgebraicGeometry.Space.hasAllChartLimitBridges_of_hasChartLimitBridges`: for an inverse
  system of quasi-compact and quasi-separated algebraic spaces with affine transition morphisms
  and algebraic limit, limit bridges along étale points give limit bridges along all points.
* `AlgebraicGeometry.Space.hasAllChartLimitBridges_of_dominant`: hence so do scheme-theoretically
  dominant limit projections, with no bound on the index category.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A function on a member of a cofiltered system of affine schemes which vanishes on the limit
already vanishes on a later member. -/
theorem exists_map_appTop_eq_zero_of_isLimit {J : Type u} [Category.{u} J] [IsCofiltered J]
    (F : J ⥤ Scheme.{u}) [∀ j, IsAffine (F.obj j)] {c : Cone F} (hc : IsLimit c) (k : J)
    (t : Γ(F.obj k, ⊤)) (ht : (c.π.app k).appTop t = 0) :
    ∃ (k' : J) (g : k' ⟶ k), (F.map g).appTop t = 0 := by
  have haff : ∀ b : Jᵒᵖ, IsAffine ((F.op.obj b).unop) := fun b => ‹∀ j, IsAffine (F.obj j)› b.unop
  have hcol := isColimitOfPreserves Scheme.Γ hc.op
  have hcolT := isColimitOfPreserves (forget CommRingCat.{u}) hcol
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcolT
    (i := op k) t 0).mp (by
      show (c.π.app k).appTop t = (c.π.app k).appTop 0
      rw [ht, map_zero])
  refine ⟨j.unop, f.unop, ?_⟩
  change (F.map f.unop).appTop t = (F.map f.unop).appTop 0 at hf
  rwa [map_zero] at hf

/-- An étale surjective morphism of affine schemes is injective on global functions, being
faithfully flat. -/
theorem injective_appTop_of_etale_of_surjective {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Etale f] [Surjective f] : Function.Injective f.appTop :=
  ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
    ⟨inferInstance, inferInstance⟩).injective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every chart system of a stage of `D` along an affine scheme-valued point of that stage has a
limit bridge: a limit in the site which is also the limit of the underlying affine schemes. -/
abbrev HasAllChartLimitBridges {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (C : AffineChartSystem B S hS i₀ D U₀ f₀), Nonempty C.LimitBridge

/-- Limit bridges along all affine points are in particular limit bridges along étale ones. -/
theorem HasAllChartLimitBridges.hasChartLimitBridges {I : Type u} [Category.{u} I]
    {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : HasAllChartLimitBridges D) :
    HasChartLimitBridges D :=
  fun i₀ U₀ f₀ _ C => h i₀ U₀ f₀ C

/-- An inverse system indexed by a category small for the site has limit bridges along all
affine points (Stacks 07SF). -/
theorem hasAllChartLimitBridges_of_small {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, Cardinal.mk (i ⟶ j) < B.cutoff.ord.cof) :
    HasAllChartLimitBridges D :=
  fun _ _ _ C => ⟨C.limitBridge hSize hHomSize⟩

namespace AffineChartSystem

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- **A criterion for a limit bridge.** If, for every limit `L` of a chart system in the site,
every function on a chart vanishing on `L` already vanishes on a later chart, the chart system
has a limit bridge: the limit in the site is a closed subscheme of the limit of the schemes
whose ideal is zero. -/
theorem nonempty_limitBridge_of_forall_appTop_eq_zero (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hlim : IsAlgebraicSpace B S hS (limit D)) (hD₀ : IsAlgebraicSpace B S hS (D.obj i₀))
    (h : ∀ (L : ChartLimit C) (k : Over i₀) (t : Γ(C.schemeDiagram.obj k, ⊤)),
      ((BigFppfOver.toScheme B S hS).map (L.cone.π.app k)).appTop t = 0 →
      ∃ (k' : Over i₀) (g : k' ⟶ k), (C.schemeDiagram.map g).appTop t = 0) :
    Nonempty C.LimitBridge := by
  obtain ⟨L, e, he, ι, hι, hπ⟩ :=
    C.exists_chartLimit_isClosedImmersion_of_isAlgebraicSpace B S hS hlim hD₀
  have _ : ∀ k, IsAffine (C.schemeDiagram.obj k) := C.isAffine_obj
  have _ : IsAffine e.pt := Scheme.isAffine_of_isLimit _ he
  have hinj : Function.Injective ι.appTop := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨k, t, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit C.schemeDiagram _ he s
    have ht : ((BigFppfOver.toScheme B S hS).map (L.cone.π.app k)).appTop t = 0 := by
      rw [hπ, Scheme.Hom.comp_appTop]; exact hs
    obtain ⟨k', g, hg⟩ := h L k t ht
    rw [← e.w g, Scheme.Hom.comp_appTop]
    show (e.π.app k').appTop ((C.schemeDiagram.map g).appTop t) = 0
    rw [hg, map_zero]
  have : IsIso ι := IsClosedImmersion.isIso_of_injective_of_isAffine (f := ι) hinj
  exact ⟨{ L with
    schemeIsLimit := he.ofIsoLimit (Cones.ext (asIso ι).symm fun j => by
      rw [Iso.symm_hom, asIso_inv, Functor.mapCone_π_app, hπ, IsIso.inv_hom_id_assoc]) }⟩

end AffineChartSystem

namespace AffineChartSystem

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- **Limit bridges along étale points give limit bridges along all points.** Let `D` be a
cofiltered inverse system of algebraic spaces with affine transition morphisms whose limit is an
algebraic space, and whose stage `i₀` is quasi-compact and quasi-separated. If every chart system
of `D` along an étale affine point has a limit bridge, so does every chart system at `i₀`. -/
theorem nonempty_limitBridge_of_hasChartLimitBridges {hZ : B.Contains (⊤_ Scheme.{u})}
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hqc : IsQuasiCompactSpace B S hS (D.obj i₀))
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i₀))
    (hbr : HasChartLimitBridges D) : Nonempty C.LimitBridge := by
  classical
  have : HasPullbacks (BigFppfOver B S hS) := by
    let := B.hasPullbacks_schemes; infer_instance
  let Q := BigFppfOver.toScheme B S hS
  -- an affine étale surjective chart `a : V₀ ⟶ D i₀`, and its chart system with a limit bridge
  obtain ⟨V₀', a, hV₀aff, haS, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ (hD i₀)).mp hqc
  let V₀ : BigAffineFppf B S hS := ⟨V₀', hV₀aff⟩
  have haE := etale_presheaf_of_isEtale' B S hS V₀' a haet
  let CV := affineChartSystem B S hS i₀ D V₀ a hAffine
  let LV : CV.LimitBridge := (hbr i₀ V₀ a haE CV).some
  -- an affine `W` étale and surjective over `U₀`, mapping to `V₀` over `D i₀`
  have hU₀qc := isQuasiCompactSpace_yoneda_of_isAffine B S hS
    ((BigAffineFppf.inclusion B S hS).obj U₀) U₀.property
  have hV₀qc := isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀' hV₀aff
  have hPalg := isAlgebraicSpace_pullback B S hS f₀ a (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) (hD i₀)
  obtain ⟨W', p, hWaff, hpS, hpet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hPalg).mp
      (isQuasiCompactSpace_pullback B S hS hZ f₀ a (isAlgebraicSpace_yoneda B S hS _) (hD i₀)
        hU₀qc hV₀qc hqs)
  have hpE := etale_presheaf_of_isEtale' B S hS W' p hpet
  let w' : W' ⟶ (BigAffineFppf.inclusion B S hS).obj U₀ :=
    yoneda.preimage (p ≫ pullback.fst f₀ a)
  let v' : W' ⟶ V₀' := yoneda.preimage (p ≫ pullback.snd f₀ a)
  have hwv : yoneda.map w' ≫ f₀ = yoneda.map v' ≫ a := by
    simp only [w', v', Functor.map_preimage, Category.assoc, pullback.condition]
  -- the charts `W_j = W ×_{V₀} V_j` of the base change of `D` along `W ⟶ V₀`
  let bV : ∀ j, CV.siteDiagram.obj j ⟶ V₀' := fun j => yoneda.preimage (CV.baseMap j)
  have hbV : ∀ j, yoneda.map (bV j) = CV.baseMap j := fun j => Functor.map_preimage _ _
  have hbVn : ∀ {j k : Over i₀} (g : j ⟶ k), CV.siteDiagram.map g ≫ bV k = bV j := fun g =>
    yoneda.map_injective <| by rw [Functor.map_comp, hbV, hbV]; exact CV.baseMap_naturality g
  let Wd : Over i₀ ⥤ BigFppfOver B S hS :=
    { obj j := pullback v' (bV j)
      map {j k} g := pullback.map v' (bV j) v' (bV k) (𝟙 _) (CV.siteDiagram.map g) (𝟙 _)
        (by simp) (by rw [Category.comp_id, hbVn g])
      map_id j := by apply pullback.hom_ext <;> simp
      map_comp f g := by apply pullback.hom_ext <;> simp }
  have hWdfst : ∀ {j k : Over i₀} (g : j ⟶ k),
      Wd.map g ≫ pullback.fst v' (bV k) = pullback.fst v' (bV j) := fun g => by
    simp [Wd]
  have hWdsnd : ∀ {j k : Over i₀} (g : j ⟶ k),
      Wd.map g ≫ pullback.snd v' (bV k) = pullback.snd v' (bV j) ≫ CV.siteDiagram.map g :=
    fun g => by simp [Wd]
  have hWsq : ∀ j, IsPullback (yoneda.map (pullback.snd v' (bV j)))
      (yoneda.map (pullback.fst v' (bV j))) (CV.baseMap j) (yoneda.map v') := fun j => by
    have := (IsPullback.of_hasPullback v' (bV j)).flip.map yoneda
    rwa [hbV] at this
  -- their maps to the charts `U_j`, base changes of `W ⟶ U₀`
  have hcond : ∀ j, (yoneda.map (pullback.snd v' (bV j)) ≫ CV.stageMap j) ≫ D.map j.hom =
      yoneda.map (pullback.fst v' (bV j) ≫ w') ≫ f₀ := fun j => by
    rw [Category.assoc, (CV.isPullback j).w, ← Category.assoc, (hWsq j).w, Category.assoc,
      ← hwv, Functor.map_comp, Category.assoc]
  let r : ∀ j, Wd.obj j ⟶ C.siteDiagram.obj j := fun j => yoneda.preimage
    ((C.isPullback j).lift _ _ (hcond j))
  have hrst : ∀ j, yoneda.map (r j) ≫ C.stageMap j =
      yoneda.map (pullback.snd v' (bV j)) ≫ CV.stageMap j := fun j => by
    simp only [r, Functor.map_preimage, IsPullback.lift_fst]
  have hrba : ∀ j, yoneda.map (r j) ≫ C.baseMap j =
      yoneda.map (pullback.fst v' (bV j) ≫ w') := fun j => by
    simp only [r, Functor.map_preimage, IsPullback.lift_snd]
  have hrsq : ∀ j, IsPullback (yoneda.map (r j)) (yoneda.map (pullback.fst v' (bV j)))
      (C.baseMap j) (yoneda.map w') := fun j => by
    refine IsPullback.of_right ?_ (by rw [hrba, Functor.map_comp]) (C.isPullback j)
    rw [hrst, hwv]
    exact (hWsq j).paste_horiz (CV.isPullback j)
  -- a property stable under base change and composition passes from `p`, `a` to all `r j`
  have hPr : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsStableUnderComposition], (P.inverseImage Q).presheaf p → (P.inverseImage Q).presheaf a →
      ∀ j, P (Q.map (r j)) := by
    intro P _ _ hp ha
    have : (P.inverseImage Q).presheaf.IsStableUnderBaseChange :=
      (P.inverseImage Q).relative_isStableUnderBaseChange (F := yoneda)
    have : (P.inverseImage Q).IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage Q
    have : (P.inverseImage Q).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    have hw : P (Q.map w') := by
      rw [← BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P, Functor.map_preimage]
      exact MorphismProperty.comp_mem _ _ _ hp
        ((P.inverseImage Q).presheaf.of_isPullback (IsPullback.of_hasPullback f₀ a).flip ha)
    exact fun j => (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P (r j)).mp
      ((P.inverseImage Q).presheaf.of_isPullback (hrsq j).flip
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P w').mpr hw))
  have hrE := hPr (@Etale.{u}) hpE haE
  have _ := AlgebraicGeometry.surjective_isStableUnderComposition.{u}
  have hrS := hPr (@Surjective.{u}) hpS haS
  have hrn : ∀ {j k : Over i₀} (g : j ⟶ k), Wd.map g ≫ r k = r j ≫ C.siteDiagram.map g := by
    intro j k g
    apply yoneda.map_injective
    refine (C.isPullback k).hom_ext ?_ ?_
    · calc yoneda.map (Wd.map g ≫ r k) ≫ C.stageMap k
          = yoneda.map (Wd.map g ≫ pullback.snd v' (bV k)) ≫ CV.stageMap k := by
            rw [Functor.map_comp, Category.assoc, hrst, Functor.map_comp, Category.assoc]
        _ = yoneda.map (pullback.snd v' (bV j)) ≫ yoneda.map (CV.siteDiagram.map g) ≫
            CV.stageMap k := by
            rw [hWdsnd, Functor.map_comp, Category.assoc]
        _ = yoneda.map (r j ≫ C.siteDiagram.map g) ≫ C.stageMap k := by
            rw [CV.stageMap_naturality, Functor.map_comp, Category.assoc,
              C.stageMap_naturality, ← Category.assoc (yoneda.map (r j)), hrst, Category.assoc]
    · calc yoneda.map (Wd.map g ≫ r k) ≫ C.baseMap k
          = yoneda.map (Wd.map g ≫ pullback.fst v' (bV k) ≫ w') := by
            rw [Functor.map_comp, Category.assoc, hrba, ← Functor.map_comp]
        _ = yoneda.map (r j ≫ C.siteDiagram.map g) ≫ C.baseMap k := by
            rw [← Category.assoc, hWdfst, yoneda.map_comp (r j), Category.assoc,
              C.baseMap_naturality, hrba]
  -- the space `T = W ×_{V₀} lim V_j`, and its maps to the `W_j`
  let bL : LV.cone.pt ⟶ V₀' := yoneda.preimage LV.toBase
  have hbL : ∀ j, LV.cone.π.app j ≫ bV j = bL := fun j =>
    yoneda.map_injective <| by
      rw [Functor.map_comp, hbV, Functor.map_preimage]; exact LV.baseMap_comp j
  let tW : ∀ j, pullback v' bL ⟶ Wd.obj j := fun j =>
    pullback.map v' bL v' (bV j) (𝟙 _) (LV.cone.π.app j) (𝟙 _) (by simp)
      (by rw [Category.comp_id, hbL])
  have htWfst : ∀ j, tW j ≫ pullback.fst v' (bV j) = pullback.fst v' bL := fun j => by
    simp [tW]
  have htWsnd : ∀ j, tW j ≫ pullback.snd v' (bV j) = pullback.snd v' bL ≫ LV.cone.π.app j :=
    fun j => by simp [tW]
  let cT : Cone Wd :=
    { pt := pullback v' bL
      π := { app := tW
             naturality := fun j k g => by
               apply pullback.hom_ext
               · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                   Category.assoc, hWdfst, htWfst]
               · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
                 rw [htWsnd, Category.assoc, hWdsnd, ← Category.assoc, htWsnd, Category.assoc,
                   LV.cone.w g] } }
  have hQpb : ∀ {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z),
      IsPullback (Q.map (pullback.fst f g)) (Q.map (pullback.snd f g)) (Q.map f) (Q.map g) :=
    fun f g => (IsPullback.of_hasPullback f g).map Q
  have hWaff' : ∀ j, IsAffine (Q.obj (Wd.obj j)) := fun j => by
    have _ : IsAffine (Q.obj W') := hWaff
    have _ : IsAffine (Q.obj V₀') := hV₀aff
    have _ : IsAffine (Q.obj (CV.siteDiagram.obj j)) := CV.isAffine_obj j
    exact IsAffine.of_isIso (hQpb v' (bV j)).isoPullback.hom
  -- the scheme `T` is the limit of the schemes `W_j`
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := Over i₀)
  have hconst : ∀ (s : Cone (Wd ⋙ Q)) (j : Over i₀),
      s.π.app j ≫ Q.map (pullback.fst v' (bV j)) =
        s.π.app j₀ ≫ Q.map (pullback.fst v' (bV j₀)) := by
    intro s j
    have key : ∀ {m k : Over i₀} (g : m ⟶ k), s.π.app k ≫ Q.map (pullback.fst v' (bV k)) =
        s.π.app m ≫ Q.map (pullback.fst v' (bV m)) := fun {m k} g => by
      rw [← s.w g, Category.assoc, Functor.comp_map, ← Q.map_comp, hWdfst]
    rw [key (IsCofiltered.minToLeft j j₀), key (IsCofiltered.minToRight j j₀)]
  let Vc : ∀ s : Cone (Wd ⋙ Q), Cone CV.schemeDiagram := fun s =>
    { pt := s.pt
      π := { app := fun j => s.π.app j ≫ Q.map (pullback.snd v' (bV j))
             naturality := fun j k g => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
               rw [← s.w g, Category.assoc, Functor.comp_map, ← Q.map_comp, hWdsnd,
                 Q.map_comp, Category.assoc]
               rfl } }
  have hlift : ∀ s : Cone (Wd ⋙ Q), (s.π.app j₀ ≫ Q.map (pullback.fst v' (bV j₀))) ≫ Q.map v' =
      LV.schemeIsLimit.lift (Vc s) ≫ Q.map bL := fun s => by
    rw [← hbL j₀, Q.map_comp, ← Category.assoc,
      show LV.schemeIsLimit.lift (Vc s) ≫ Q.map (LV.cone.π.app j₀) =
        s.π.app j₀ ≫ Q.map (pullback.snd v' (bV j₀)) from LV.schemeIsLimit.fac (Vc s) j₀]
    simp only [Category.assoc, ← Q.map_comp, pullback.condition]
  let hT := hQpb v' bL
  have hTlim : IsLimit (Q.mapCone cT) :=
    { lift := fun s => hT.lift (s.π.app j₀ ≫ Q.map (pullback.fst v' (bV j₀)))
        (LV.schemeIsLimit.lift (Vc s)) (hlift s)
      fac := fun s j => by
        refine (hQpb v' (bV j)).hom_ext ?_ ?_
        · show (hT.lift _ _ (hlift s) ≫ Q.map (tW j)) ≫ Q.map (pullback.fst v' (bV j)) = _
          rw [Category.assoc, ← Q.map_comp, htWfst, hT.lift_fst, hconst s j]
        · show (hT.lift _ _ (hlift s) ≫ Q.map (tW j)) ≫ Q.map (pullback.snd v' (bV j)) = _
          rw [Category.assoc, ← Q.map_comp, htWsnd, Q.map_comp, ← Category.assoc, hT.lift_snd]
          exact LV.schemeIsLimit.fac (Vc s) j
      uniq := fun s m hm => by
        refine hT.hom_ext ?_ ?_
        · rw [hT.lift_fst, ← hm j₀]
          show m ≫ Q.map (pullback.fst v' bL) = (m ≫ Q.map (tW j₀)) ≫ _
          rw [Category.assoc, ← Q.map_comp, htWfst]
        · rw [hT.lift_snd]
          refine LV.schemeIsLimit.hom_ext fun j => ?_
          rw [LV.schemeIsLimit.fac]
          show (m ≫ Q.map (pullback.snd v' bL)) ≫ Q.map (LV.cone.π.app j) =
            s.π.app j ≫ Q.map (pullback.snd v' (bV j))
          rw [← hm j]
          show _ = (m ≫ Q.map (tW j)) ≫ _
          rw [Category.assoc, Category.assoc, ← Q.map_comp, ← Q.map_comp, htWsnd] }
  -- a function on a chart vanishing on the limit vanishes on a later chart
  refine C.nonempty_limitBridge_of_forall_appTop_eq_zero hlim (hD i₀) fun L k t ht => ?_
  have hbL' : yoneda.map bL = LV.toBase := Functor.map_preimage _ _
  have hxc : (yoneda.map (pullback.snd v' bL) ≫ LV.toLimit) ≫ limit.π D i₀ =
      yoneda.map (pullback.fst v' bL ≫ w') ≫ f₀ := by
    rw [Category.assoc, LV.isPullback.w, ← Category.assoc, ← hbL', ← Functor.map_comp,
      ← pullback.condition, Functor.map_comp, Category.assoc, ← hwv, ← Category.assoc,
      ← Functor.map_comp]
  let xs : pullback v' bL ⟶ L.cone.pt := yoneda.preimage (L.isPullback.lift _ _ hxc)
  have hxsy : yoneda.map xs = L.isPullback.lift _ _ hxc := Functor.map_preimage _ _
  have hxs : xs ≫ L.cone.π.app k = tW k ≫ r k := by
    apply yoneda.map_injective
    refine (C.isPullback k).hom_ext ?_ ?_
    · calc yoneda.map (xs ≫ L.cone.π.app k) ≫ C.stageMap k
          = (yoneda.map xs ≫ L.toLimit) ≫ limit.π D k.left := by
            rw [Functor.map_comp, Category.assoc, ← L.toLimit_comp_limitπ, Category.assoc]
        _ = yoneda.map (pullback.snd v' bL) ≫ yoneda.map (LV.cone.π.app k) ≫
            CV.stageMap k := by
            rw [hxsy, IsPullback.lift_fst, Category.assoc, LV.toLimit_comp_limitπ]
        _ = yoneda.map (tW k ≫ r k) ≫ C.stageMap k := by
            rw [yoneda.map_comp (tW k), Category.assoc, hrst,
              ← Category.assoc (yoneda.map (tW k)), ← yoneda.map_comp (tW k), htWsnd,
              Functor.map_comp, Category.assoc]
    · calc yoneda.map (xs ≫ L.cone.π.app k) ≫ C.baseMap k = yoneda.map xs ≫ L.toBase := by
            rw [Functor.map_comp, Category.assoc, L.baseMap_comp]
        _ = yoneda.map (tW k ≫ r k) ≫ C.baseMap k := by
            rw [hxsy, IsPullback.lift_snd, yoneda.map_comp (tW k), Category.assoc, hrba,
              ← yoneda.map_comp (tW k), ← Category.assoc, htWfst]
  have hτ : (Q.map (tW k)).appTop ((Q.map (r k)).appTop t) = 0 := by
    have e1 : (Q.map (tW k)).appTop ((Q.map (r k)).appTop t) =
        (Q.map (tW k ≫ r k)).appTop t := by
      rw [Q.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [e1, ← hxs, Q.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ht, map_zero]
  have : ∀ j, IsAffine ((Wd ⋙ Q).obj j) := hWaff'
  obtain ⟨k', g, hg⟩ := exists_map_appTop_eq_zero_of_isLimit (Wd ⋙ Q) hTlim k _ hτ
  refine ⟨k', g, ?_⟩
  have := hrE k'
  have := hrS k'
  have : IsAffine (Q.obj (Wd.obj k')) := hWaff' k'
  have : IsAffine (Q.obj (C.siteDiagram.obj k')) := C.isAffine_obj k'
  apply injective_appTop_of_etale_of_surjective (Q.map (r k'))
  rw [map_zero]
  have e2 : (Q.map (r k')).appTop ((C.schemeDiagram.map g).appTop t) =
      (Q.map (Wd.map g ≫ r k)).appTop t := by
    rw [hrn g, Q.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rfl
  rwa [e2, Q.map_comp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

end AffineChartSystem

/-- **Limit bridges along étale points give limit bridges along all points**, for a cofiltered
inverse system of quasi-compact and quasi-separated algebraic spaces with affine transition
morphisms whose limit is an algebraic space. -/
theorem hasAllChartLimitBridges_of_hasChartLimitBridges {hZ : B.Contains (⊤_ Scheme.{u})}
    {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hbr : HasChartLimitBridges D) : HasAllChartLimitBridges D :=
  fun i₀ _ _ C => C.nonempty_limitBridge_of_hasChartLimitBridges hD hAffine hlim (hqc i₀)
    (hqs i₀) hbr

/-- **Scheme-theoretically dominant projections give limit bridges along all points**, with no
condition on the size of the index category, for a cofiltered inverse system of quasi-compact and
quasi-separated algebraic spaces with affine transition morphisms whose limit is an algebraic
space. -/
theorem hasAllChartLimitBridges_of_dominant {hZ : B.Contains (⊤_ Scheme.{u})}
    {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hqc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hqs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hdom : ∀ i, schemeTheoreticImageSubfunctor B S hS (limit.π D i) = ⊤) :
    HasAllChartLimitBridges D :=
  hasAllChartLimitBridges_of_hasChartLimitBridges hD hAffine hlim hqc hqs
    (hasChartLimitBridges_of_dominant hD hAffine hlim hdom)

end AlgebraicGeometry.Space

end
