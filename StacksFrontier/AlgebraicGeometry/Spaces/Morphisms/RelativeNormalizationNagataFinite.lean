module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalizationNagata
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The relative normalization over a Nagata algebraic space is finite

Let `f : Y ⟶ X` be a quasi-separated morphism of finite type of algebraic spaces over a scheme
`S`, with `X` Nagata and `Y` reduced. Then the normalization `ν : X' ⟶ X` of `X` in `Y`, in the
sense of `AlgebraicGeometry.Space.IsRelativeNormalization`, is finite.

## Main results

* `AlgebraicGeometry.Space.isFinite_of_isFinite_of_isPullback_affine_etale`: a representable
  morphism of algebraic spaces is finite as soon as it is so over every affine étale chart of
  its target.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isIso_ι_schemeTheoreticImage`: the
  scheme-theoretic image of `f' : Y ⟶ X'` in the normalization of `X` in `Y` is all of `X'`.
* `AlgebraicGeometry.Space.IsRelativeNormalization.dense_range_pointsMap`: the image of the
  point map of `f' : Y ⟶ X'` is dense in the normalization of `X` in a reduced `Y`.
* `AlgebraicGeometry.Space.IsRelativeNormalization.injective_appTop_of_isPullback`: over an
  affine étale chart of `X`, the functions on the base change of the normalization embed into
  the functions on an affine surjective étale cover of the part of `Y` over the chart.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isFinite_of_isNagata_of_isReduced`: the
  normalization of a Nagata algebraic space in a reduced algebraic space, along a
  quasi-separated morphism of finite type, is finite.

## References

* [Stacks Project, Tag 0BB0](https://stacks.math.columbia.edu/tag/0BB0)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0830](https://stacks.math.columbia.edu/tag/0830)
* [Stacks Project, Tag 0AYF](https://stacks.math.columbia.edu/tag/0AYF)
* [Stacks Project, Tag 03GR](https://stacks.math.columbia.edu/tag/03GR)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site times out at the default limit
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_RelativeNormalizationNagataFinite :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for a single pullback of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_RelativeNormalizationNagataFinite
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Reduction to affine étale charts of the target -/

/-- A representable morphism of algebraic spaces over `S` is finite as soon as, over every
affine étale chart `q : V ⟶ Y` of its target, every morphism of schemes representing its base
change along `q` is finite. -/
theorem isFinite_of_isFinite_of_isPullback_affine_etale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hf : ∀ (V N : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y) (p : N ⟶ V)
      (i : yoneda.obj N ⟶ X), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q →
        IsPullback i (yoneda.map p) f q →
        _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p)) :
    IsFinite B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      T).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u})
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      T).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS (@AlgebraicGeometry.Etale.{u})
  obtain ⟨V, q, hsurj, hetale⟩ := hY.exists_atlas
  refine (isFinite_iff_etaleLocal B S hS f hX hY).mpr ⟨V, q, hsurj, hetale, ?_⟩
  have hpb := hrep.isPullback q
  have hfin : _root_.AlgebraicGeometry.IsFinite (T.map (hrep.snd q)) := by
    have _ := isZariskiLocalAtTarget_isFinite.{u}
    let cover := (T.obj V).affineCover
    refine IsZariskiLocalAtTarget.of_openCover
      (P := @_root_.AlgebraicGeometry.IsFinite.{u}) cover fun j => ?_
    let T₀ : B.Schemes := B.obj (Scheme.size_lt_of_isOpenImmersion (cover.f j) V.left.property)
    let a₀ : T₀ ⟶ V.left :=
      B.inclusion.preimage (show B.inclusion.obj T₀ ⟶ B.inclusion.obj V.left from cover.f j)
    let Tj : BigFppfOver B S hS := Over.mk (a₀ ≫ V.hom)
    let a : Tj ⟶ V := Over.homMk a₀
    have ha : T.map a = cover.f j := B.inclusion.map_preimage _
    have hTaff : IsAffine (T.obj Tj) := by
      change IsAffine (cover.X j); infer_instance
    have haEtale : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) a := by
      change AlgebraicGeometry.Etale (T.map a)
      rw [ha]; infer_instance
    have hqa : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
        (yoneda.map a ≫ q) :=
      (isEtale_of_presheaf_etale B S hS hetale) Tj (yoneda.map a)
        (MorphismProperty.relative_map haEtale)
    let q' := yoneda.map a ≫ q
    have _ : _root_.AlgebraicGeometry.IsFinite (T.map (hrep.snd q')) :=
      hf Tj _ q' (hrep.snd q') (hrep.fst q') hTaff hqa (hrep.isPullback q')
    let t : hrep.pullback q' ⟶ hrep.pullback q :=
      hrep.lift (hrep.fst q') (hrep.snd q' ≫ a) (by
        simpa only [Functor.map_comp, Category.assoc] using (hrep.isPullback q').w)
    have ht : yoneda.map t ≫ hrep.fst q = hrep.fst q' := hrep.lift_fst _ _ _
    have hs : yoneda.map t ≫ yoneda.map (hrep.snd q) =
        yoneda.map (hrep.snd q') ≫ yoneda.map a := by
      rw [← yoneda.map_comp, hrep.lift_snd, yoneda.map_comp]
    have hsq : IsPullback (yoneda.map t) (yoneda.map (hrep.snd q'))
        (yoneda.map (hrep.snd q)) (yoneda.map a) :=
      (ht.symm ▸ hrep.isPullback q').of_right hs (hrep.isPullback q)
    have hscheme := (hsq.of_map_of_faithful yoneda).map T
    rw [ha] at hscheme
    change _root_.AlgebraicGeometry.IsFinite (Limits.pullback.snd (T.map (hrep.snd q)) (cover.f j))
    rw [← hscheme.isoPullback_inv_snd]
    infer_instance
  have hVspace : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hPull : IsAlgebraicSpace B S hS (Limits.pullback f q) :=
    isAlgebraicSpace_pullback B S hS f q hX hVspace hY
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      T).relative yoneda (Limits.pullback.snd f q) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      T).relative yoneda).cancel_left_of_respectsIso
      hpb.isoPullback.hom (Limits.pullback.snd f q)).mp ?_
    rw [hpb.isoPullback_hom_snd]
    exact MorphismProperty.relative_map hfin
  exact (isFinite_iff_representable B S hS (Limits.pullback.snd f q) hPull hVspace).2
    ⟨hrelq.1, hrelq⟩

variable {B S hS} {X Y X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X} {ν : X' ⟶ X}
  {f' : Y ⟶ X'}

/-! ### The source dominates the normalization -/

section Dominance

attribute [local instance] pointTopology

/-- The scheme-theoretic image of `f' : Y ⟶ X'` in the normalization `X'` of `X` in `Y` is all
of `X'`: its inclusion is an isomorphism. -/
theorem IsRelativeNormalization.isIso_ι_schemeTheoreticImage
    (hnorm : IsRelativeNormalization B S hS f ν f')
    (hX' : IsAlgebraicSpace B S hS X') :
    IsIso (schemeTheoreticImageSubfunctor B S hS f').ι := by
  set Z := schemeTheoreticImageSubfunctor B S hS f'
  have hZcs : IsClosedSubspace B S hS Z :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f' hX'
  have hZint : IsIntegralHom B S hS (Z.ι ≫ ν) :=
    isIntegralHom_comp B S hS (isIntegralHom_of_isClosedImmersion B S hS Z.ι hZcs.2)
      hnorm.isIntegralHom
  obtain ⟨h, ⟨hhg, hhν⟩, -⟩ := hnorm.existsUnique_lift hZcs.1 (Z.ι ≫ ν) hZint
    (toSchemeTheoreticImage B S hS f')
    (by rw [← Category.assoc, toSchemeTheoreticImage_ι, hnorm.fac])
  have hsection : h ≫ Z.ι = 𝟙 X' := by
    refine (hnorm.existsUnique_lift hX' ν hnorm.isIntegralHom f' hnorm.fac).unique
      ⟨?_, ?_⟩ ⟨Category.comp_id f', Category.id_comp ν⟩
    · rw [← Category.assoc, hhg]; exact toSchemeTheoreticImage_ι B S hS f'
    · rw [Category.assoc]; exact hhν
  have hretract : Z.ι ≫ h = 𝟙 Z.toFunctor := by
    refine (cancel_mono Z.ι).1 ?_
    rw [Category.assoc, hsection, Category.comp_id, Category.id_comp]
  exact ⟨h, hretract, hsection⟩

/-- The image of the point map of `f' : Y ⟶ X'` is dense in the normalization `X'` of `X` in a
reduced algebraic space `Y`. -/
theorem IsRelativeNormalization.dense_range_pointsMap
    (hnorm : IsRelativeNormalization B S hS f ν f')
    (hY : IsAlgebraicSpace B S hS Y) (hX' : IsAlgebraicSpace B S hS X')
    (hYred : HasEtaleLocalProperty B S hS Y fun Z : Scheme.{u} => IsReduced Z) :
    Dense (Set.range (pointsMap B S hS Y f')) := by
  have _ := hnorm.isIso_ι_schemeTheoreticImage hX'
  have heq := range_pointsMap_ι_schemeTheoreticImage_eq_closure B S hS f' hY hX'
    fun V g hV hg =>
      schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale B S hS f' g hY hX' hV hYred hg
  rw [Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS
    (schemeTheoreticImageSubfunctor B S hS f').ι)] at heq
  exact dense_iff_closure_eq.2 heq.symm

/-- Over an étale chart `q : V ⟶ X`, with `N` representing the base change of the
normalization, the comparison morphism `c : W ⟶ N` from an affine surjective étale cover `W` of
`V ×_X Y` is injective on functions when `N` is affine. -/
theorem IsRelativeNormalization.injective_appTop_of_isPullback
    (hnorm : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hX' : IsAlgebraicSpace B S hS X')
    (hYred : HasEtaleLocalProperty B S hS Y fun Z : Scheme.{u} => IsReduced Z)
    {V N W : BigFppfOver B S hS} {q : yoneda.obj V ⟶ X} {n : N ⟶ V}
    {i : yoneda.obj N ⟶ X'} {w : yoneda.obj W ⟶ Limits.pullback q f} {c : W ⟶ N}
    (hNaff : IsAffine ((BigFppfOver.toScheme B S hS).obj N))
    (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hq : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hpb : IsPullback i (yoneda.map n) ν q)
    (hwSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w)
    (hci : yoneda.map c ≫ i = w ≫ Limits.pullback.snd q f ≫ f')
    (hcn : yoneda.map c ≫ yoneda.map n = w ≫ Limits.pullback.fst q f) :
    Function.Injective (((BigFppfOver.toScheme B S hS).map c).appTop.hom) := by
  have hVspace : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hNspace : IsAlgebraicSpace B S hS (yoneda.obj N) := isAlgebraicSpace_yoneda B S hS N
  have hPspace : IsAlgebraicSpace B S hS (Limits.pullback q f) :=
    isAlgebraicSpace_pullback B S hS q f hVspace hY hX
  have hiEt : IsEtale B S hS i :=
    isEtale_of_isPullback_yoneda B S hS hpb.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS q).mpr hq)
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj N) :=
    (exists_atlas_iff_forall_etale B S hS X' (fun Z : Scheme.{u} => IsReduced Z) hX').mp
      (hnorm.hasEtaleLocalProperty_isReduced hX' hY hYred) N i
      (presheaf_of_isPullback B S hS hpb.flip hq)
  have hwfac : (Limits.pullback.snd q f ≫ f') ≫ ν = Limits.pullback.fst q f ≫ q := by
    rw [Category.assoc, hnorm.fac, Limits.pullback.condition]
  let m : Limits.pullback q f ⟶ yoneda.obj N :=
    hpb.lift (Limits.pullback.snd q f ≫ f') (Limits.pullback.fst q f) hwfac
  have hmi : m ≫ i = Limits.pullback.snd q f ≫ f' := hpb.lift_fst _ _ _
  have hmn : m ≫ yoneda.map n = Limits.pullback.fst q f := hpb.lift_snd _ _ _
  have hsq : IsPullback (Limits.pullback.snd q f) m f' i := by
    refine IsPullback.of_bot ?_ hmi.symm hpb
    rw [hmn, hnorm.fac]
    exact (IsPullback.of_hasPullback q f).flip
  have hw : yoneda.map c = w ≫ m := by
    refine hpb.hom_ext ?_ ?_
    · rw [hci, Category.assoc, hmi]
    · rw [hcn, Category.assoc, hmn]
  have hrange : pointsMap B S hS (yoneda.obj N) i ⁻¹' Set.range (pointsMap B S hS Y f') =
      Set.range (pointsMap B S hS (Limits.pullback q f) m) := by
    simpa using preimage_image_pointsMap_of_isPullback B S hS hsq Set.univ
  have hwSurjPts : Function.Surjective (pointsMap B S hS (yoneda.obj W) w) :=
    (surjective_iff_surjective_pointsMap B S hS (Limits.pullback q f) hPspace W w).mp hwSurj
  have hdenseC : Dense (Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map c))) := by
    rw [hw, pointsMap_comp, Set.range_comp, hwSurjPts.range_eq, Set.image_univ, ← hrange]
    exact (hnorm.dense_range_pointsMap hY hX' hYred).preimage
      (isOpenMap_pointsMap_of_isEtale B S hS i hNspace hX' hiEt)
  have he : ⇑(schemePointsHomeomorph B S hS N) = pointsToScheme B S hS N := rfl
  have himg : pointsToScheme B S hS N ''
      Set.range (pointsMap B S hS (yoneda.obj W) (yoneda.map c)) =
      Set.range ((BigFppfOver.toScheme B S hS).map c).base := by
    rw [← Set.range_comp,
      show pointsToScheme B S hS N ∘ pointsMap B S hS (yoneda.obj W) (yoneda.map c) =
          ((BigFppfOver.toScheme B S hS).map c).base ∘ pointsToScheme B S hS W from
        funext fun x => pointsToScheme_pointsMap B S hS c x,
      Set.range_comp, (surjective_pointsToScheme B S hS W).range_eq, Set.image_univ]
  have hdenseScheme : DenseRange ((BigFppfOver.toScheme B S hS).map c).base := by
    refine dense_iff_closure_eq.2 ?_
    rw [← himg, ← he, ← (schemePointsHomeomorph B S hS N).image_closure, hdenseC.closure_eq,
      Set.image_univ, Set.range_eq_univ.2 (schemePointsHomeomorph B S hS N).surjective]
  have _ : IsDominant ((BigFppfOver.toScheme B S hS).map c) := ⟨hdenseScheme⟩
  have _ : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map c) :=
    .of_isDominant _
  exact ((BigFppfOver.toScheme B S hS).map c).app_injective ⊤

end Dominance

/-! ### Finiteness of the normalization -/

/-- Let `f : Y ⟶ X` be a quasi-separated morphism of finite type of algebraic spaces over `S` with
`X` Nagata and `Y` reduced. Then the normalization `ν : X' ⟶ X` of `X` in `Y`, any factorization
`Y ⟶ X' ⟶ X` of `f` satisfying `AlgebraicGeometry.Space.IsRelativeNormalization`, is finite. -/
@[stacks 0BB0 "for f : Y ⟶ X quasi-separated of finite type, X Nagata and Y reduced, every \
normalization of X in Y in the sense of Stacks 0823 is finite over X"]
theorem IsRelativeNormalization.isFinite_of_isNagata_of_isReduced
    (hnorm : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hX' : IsAlgebraicSpace B S hS X')
    (hXnagata : HasEtaleLocalProperty B S hS X fun Z : Scheme.{u} => IsNagataScheme Z)
    (hYred : HasEtaleLocalProperty B S hS Y fun Z : Scheme.{u} => IsReduced Z)
    (hft : IsFiniteType B S hS f) (_hqs : IsQuasiSeparated B S hS f) :
    IsFinite B S hS ν := by
  let T := BigFppfOver.toScheme B S hS
  have hrepν := (isIntegralHom_iff_representable B S hS ν hX' hX).mp hnorm.isIntegralHom
  refine isFinite_of_isFinite_of_isPullback_affine_etale B S hS ν hX' hX hrepν.1
    fun V N q n i hV hq hpb => ?_
  have hVnag : IsNagataScheme (T.obj V) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) hX).mp
      hXnagata V q hq
  have hnInt : _root_.AlgebraicGeometry.IsIntegralHom (T.map n) := hrepν.2.property q i n hpb
  have hNaff : IsAffine (T.obj N) := isAffine_of_isIntegralHom (T.map n) hnInt hV
  have hVspace : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hPspace : IsAlgebraicSpace B S hS (Limits.pullback q f) :=
    isAlgebraicSpace_pullback B S hS q f hVspace hY hX
  obtain ⟨W, w, hWaff, hwSurj, hwEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (Limits.pullback q f) hPspace).mp
      (hft.2 (yoneda.obj V) hVspace (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) q)
  have hsnd : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (Limits.pullback.snd q f) :=
    presheaf_of_isPullback B S hS (IsPullback.of_hasPullback q f) hq
  have hchart : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (w ≫ Limits.pullback.snd q f) := by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ _ _ (presheaf_etale_of_isEtale B S hS hwEt) hsnd
  have hWred : IsReduced (T.obj W) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun Z : Scheme.{u} => IsReduced Z) hY).mp
      hYred W (w ≫ Limits.pullback.snd q f) hchart
  let m : W ⟶ V := yoneda.preimage (w ≫ Limits.pullback.fst q f)
  have hm : yoneda.map m = w ≫ Limits.pullback.fst q f := yoneda.map_preimage _
  have hmft : LocallyOfFiniteType (T.map m) := by
    refine hft.1 W V (w ≫ Limits.pullback.snd q f) q m hchart hq ?_
    rw [hm, Category.assoc, Category.assoc, Limits.pullback.condition]
  have hwfac : (w ≫ Limits.pullback.snd q f ≫ f') ≫ ν = (w ≫ Limits.pullback.fst q f) ≫ q := by
    rw [Category.assoc, Category.assoc, hnorm.fac, Category.assoc, Limits.pullback.condition]
  let c : W ⟶ N := yoneda.preimage (hpb.lift (w ≫ Limits.pullback.snd q f ≫ f')
    (w ≫ Limits.pullback.fst q f) hwfac)
  have hc : yoneda.map c =
      hpb.lift (w ≫ Limits.pullback.snd q f ≫ f') (w ≫ Limits.pullback.fst q f) hwfac :=
    yoneda.map_preimage _
  have hci : yoneda.map c ≫ i = w ≫ Limits.pullback.snd q f ≫ f' := by
    rw [hc, hpb.lift_fst]
  have hcn : yoneda.map c ≫ yoneda.map n = w ≫ Limits.pullback.fst q f := by
    rw [hc, hpb.lift_snd]
  have hcm : c ≫ n = m := yoneda.map_injective (by rw [Functor.map_comp, hcn, hm])
  have hinj := hnorm.injective_appTop_of_isPullback hX hY hX' hYred hNaff hWaff hq hpb hwSurj
    hci hcn
  have _ : LocallyOfFiniteType (T.map c ≫ T.map n) := by
    rwa [← Functor.map_comp, hcm]
  exact isFinite_of_isIntegralHom_of_injective_appTop (T.map n) (T.map c) hVnag hinj

end AlgebraicGeometry.Space

end
