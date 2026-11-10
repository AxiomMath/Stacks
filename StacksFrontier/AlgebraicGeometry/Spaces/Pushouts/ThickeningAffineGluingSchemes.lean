module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineAtlasExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# The scheme clauses of Tag 07VY

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism
and `Y' = Y ⨿_X X'`.  [Stacks Project, Tag 07VY] asserts, besides the adjunction `G ⊣ F` between
gluing and base change, that both functors preserve schemes: `F` sends a scheme over `Y'` to a
pair of schemes, and `G` sends a pair of schemes to a scheme.  A scheme is an algebraic space
whose underlying presheaf is representable on the big fppf site.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_inl_of_isPushout`: the morphism `X' ⟶ Y'` is affine.
  Its base change along the étale chart of `Y'` built from a compatible pair of charts is the
  leg `U' ⟶ U' ⨿_U V` of a pushout of schemes, which is affine; affineness descends along the
  chart by [Stacks Project, Tag 03WG].
* `AlgebraicGeometry.Space.isRepresentable_pushoutBaseChangeFunctor_obj_left` and
  `AlgebraicGeometry.Space.isRepresentable_pushoutBaseChangeFunctor_obj_right`: `F` preserves
  schemes, `Y ⟶ Y'` being a closed immersion and `X' ⟶ Y'` being affine.
* `AlgebraicGeometry.Space.isRepresentable_of_isPushout_of_isThickeningHom`: a pushout of
  algebraic spaces of a thickening and an affine morphism between schemes is a scheme, by
  [Stacks Project, Tag 07RT] and [Stacks Project, Tag 07SY].
* `AlgebraicGeometry.Space.isRepresentable_pushoutGluingFunctor_obj`: hence `G` preserves
  schemes.

## References

* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ThickeningAffineGluingSchemes :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ThickeningAffineGluingSchemes
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is deep
/-- Small products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasLimitsOfShape_discrete_presheaf_ThickeningAffineGluingSchemes (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A morphism isomorphic, via a commutative square, to an affine morphism is affine. -/
private theorem isAffineHom_of_comm_sq_of_isIso {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {k : X' ⟶ X} {g : Y' ⟶ Y} [IsIso k] [IsIso g]
    (w : k ≫ f = f' ≫ g) (hf : IsAffineHom B S hS f) : IsAffineHom B S hS f' :=
  IsAffineHom.of_isPullback (IsPullback.of_horiz_isIso ⟨w⟩) hf

/-- **The morphism `X' ⟶ Y'` into a thickening-and-affine pushout is affine.**  If `E` is a
pushout of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` along `a` and `b`, and
the span admits compatible étale scheme charts, then `a` is affine. -/
theorem isAffineHom_inl_of_isPushout (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y E : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {a : X' ⟶ E} {b : Y ⟶ E} (hE : IsPushout i f a b) :
    IsAffineHom B S hS a.hom := by
  obtain ⟨A⟩ := hatlas i f hi hf
  obtain ⟨Epo, aY, bY, qm, hpush, -, hqmS, hqmE, haX', -⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  let eE := hpush.isoIsPushout _ _ hE
  let eP : Epo.1 ≅ E.1 :=
    { hom := eE.hom.hom
      inv := eE.inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) eE.hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) eE.inv_hom_id }
  have hinl : aY.hom ≫ eP.hom = a.hom :=
    congrArg (fun φ => φ.hom) (hpush.inl_isoIsPushout_hom _ _ hE)
  have haX'' : IsPullback (yoneda.map A.a) A.p' (qm ≫ eP.hom) a.hom :=
    haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinl)
  have hqS : IsSurjective B S hS (qm ≫ eP.hom) :=
    isSurjective_of_presheafSurjective B S hS _
      (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
  have hqE : IsEtale B S hS (qm ≫ eP.hom) :=
    isEtale_of_presheaf_etale B S hS (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE)
  have := A.isAffineHom_g
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map A.a) :=
    Stacks.Pushout.isAffineHom_of_isPushout_of_isThickening A.isPushout_chart A.isThickening_k
  have hAa : IsAffineHom B S hS (yoneda.map A.a) :=
    isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance A.a).mpr inferInstance)
  have hsnd : IsAffineHom B S hS (pullback.snd a.hom (qm ≫ eP.hom)) := by
    let e := (IsPullback.of_hasPullback a.hom (qm ≫ eP.hom)).isoIsPullback _ _ haX''.flip
    have he : e.hom ≫ yoneda.map A.a = pullback.snd a.hom (qm ≫ eP.hom) :=
      (IsPullback.of_hasPullback a.hom (qm ≫ eP.hom)).isoIsPullback_hom_snd _ _ haX''.flip
    exact isAffineHom_of_comm_sq_of_isIso (g := 𝟙 _) (by rw [he, Category.comp_id]) hAa
  have key := (isAffineHom_tfae_of_isAlgebraicSpace B S hS a.hom X'.property E.property).out 4 2
  exact key.mp ⟨_, _, hqS, hqE, hsnd⟩

variable (hatlas : HasThickeningAffineAtlases B S hS)
  {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
  (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)

/-- **Stacks 07VY, `F` on schemes, the `Y`-component.**  The base change `Z ×_{Y'} Y` of a scheme
`Z` over `Y' = Y ⨿_X X'` is a scheme: `Y ⟶ Y'` is a thickening, hence a closed immersion. -/
theorem isRepresentable_pushoutBaseChangeFunctor_obj_left
    (Z : Over (letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
      pushout i f)) (hZ : Z.left.1.IsRepresentable) :
    ((pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj Z).obj.left.left.1.IsRepresentable := by
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  exact isRepresentable_of_isClosedImmersion B S hS (pullback.fst Z.hom (pushout.inr i f)).hom
    (isClosedImmersion_of_isPullback B S hS (IsPullback.of_hasPullback Z.hom (pushout.inr i f)).flip
      (pushout_inr_isThickening B S hS hatlas i f hi hf).isClosedImmersion) hZ

/-- **Stacks 07VY, `F` on schemes, the `X'`-component.**  The base change `Z ×_{Y'} X'` of a
scheme `Z` over `Y' = Y ⨿_X X'` is a scheme: `X' ⟶ Y'` is affine, hence representable. -/
theorem isRepresentable_pushoutBaseChangeFunctor_obj_right
    (Z : Over (letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
      pushout i f)) (hZ : Z.left.1.IsRepresentable) :
    ((pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj
      Z).obj.right.left.1.IsRepresentable := by
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  have hfst : IsAffineHom B S hS (pullback.fst Z.hom (pushout.inl i f)).hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS
      (IsPullback.of_hasPullback Z.hom (pushout.inl i f))).flip
      (isAffineHom_inl_of_isPushout hatlas hi hf (IsPushout.of_hasPushout i f))
  have := hZ
  have key := (isAffineHom_tfae_of_isAlgebraicSpace B S hS
    (pullback.fst Z.hom (pushout.inl i f)).hom (pullback Z.hom (pushout.inl i f)).property
    Z.left.property).out 2 1
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (key.mp hfst).1

/-- **A pushout of a thickening and an affine morphism between schemes is a scheme.**  If
`jU : U ⟶ U'` is a thickening and `σ : U ⟶ V` an affine morphism of algebraic spaces over `S`
with `U'` and `V` schemes, then any pushout `G` of `jU` and `σ` in the algebraic spaces over `S`
is a scheme: the scheme pushout of [Stacks Project, Tag 07RT] lies in the site and is a pushout
of algebraic spaces by [Stacks Project, Tag 07SY]. -/
theorem isRepresentable_of_isPushout_of_isThickeningHom
    {U U' V G : AlgebraicSpaces B S hS} {jU : U ⟶ U'} {σ : U ⟶ V} {aG : U' ⟶ G} {bG : V ⟶ G}
    (hG : IsPushout jU σ aG bG) (hjU : IsThickeningHom B S hS jU)
    (hσ : IsAffineHom B S hS σ.hom) (hU' : U'.1.IsRepresentable) (hV : V.1.IsRepresentable) :
    G.1.IsRepresentable := by
  have hU : U.1.IsRepresentable :=
    isRepresentable_of_isClosedImmersion B S hS jU.hom hjU.isClosedImmersion hU'
  let eU : schemeSpace U.1.reprX ≅ U := ObjectProperty.isoMk _ U.1.reprW
  let eU' : schemeSpace U'.1.reprX ≅ U' := ObjectProperty.isoMk _ U'.1.reprW
  let eV : schemeSpace V.1.reprX ≅ V := ObjectProperty.isoMk _ V.1.reprW
  let k₀ : U.1.reprX ⟶ U'.1.reprX := yoneda.preimage (eU.hom ≫ jU ≫ eU'.inv).hom
  let g₀ : U.1.reprX ⟶ V.1.reprX := yoneda.preimage (eU.hom ≫ σ ≫ eV.inv).hom
  have hk₀ : schemeSpaceMap k₀ = eU.hom ≫ jU ≫ eU'.inv :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage _)
  have hg₀ : schemeSpaceMap g₀ = eU.hom ≫ σ ≫ eV.inv :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage _)
  have hk₀T : IsThickeningHom B S hS (schemeSpaceMap k₀) := by
    rw [hk₀]
    exact (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).2
      ⟨MorphismProperty.RespectsIso.precomp _ eU.hom.hom _
        (MorphismProperty.RespectsIso.postcomp _ eU'.inv.hom _ hjU.isClosedImmersion),
        isSurjective_comp B S hS (isSurjective_of_isIso B S hS _)
          (isSurjective_comp B S hS hjU.surjective_pointsMap
            (isSurjective_of_isIso B S hS _))⟩
  have hk₀s : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k₀) :=
    ⟨(presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u})
        inferInstance k₀).mp hk₀T.isClosedImmersion,
      surjective_of_isSurjective_yonedaMap B S hS k₀ hk₀T.surjective_pointsMap⟩
  have hg₀A : IsAffineHom B S hS (yoneda.map g₀) := by
    refine isAffineHom_of_comm_sq_of_isIso (k := U.1.reprW.hom) (g := V.1.reprW.hom) ?_ hσ
    have h := congrArg (fun φ => φ.hom) hg₀
    simp only [schemeSpaceMap_hom, ObjectProperty.FullSubcategory.comp_hom] at h
    rw [h]
    change U.1.reprW.hom ≫ σ.hom = (U.1.reprW.hom ≫ σ.hom ≫ V.1.reprW.inv) ≫ V.1.reprW.hom
    simp
  have key := (isAffineHom_tfae_of_isAlgebraicSpace B S hS (yoneda.map g₀)
    (schemeSpace U.1.reprX).property (schemeSpace V.1.reprX).property).out 2 1
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g₀) :=
    (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsAffineHom.{u})
      inferInstance g₀).mp (key.mp hg₀A).2
  obtain ⟨P, a₀, b₀, hP⟩ := exists_isPushout_site B S hS k₀ g₀ hk₀s
  have hPsp : IsPushout (schemeSpaceMap k₀) (schemeSpaceMap g₀) (schemeSpaceMap a₀)
      (schemeSpaceMap b₀) :=
    isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS k₀ g₀ a₀ b₀ hk₀s hP
  have hPG : IsPushout jU σ (eU'.inv ≫ schemeSpaceMap a₀) (eV.inv ≫ schemeSpaceMap b₀) :=
    hPsp.of_iso eU eU' eV (Iso.refl _) (by rw [hk₀]; simp) (by rw [hg₀]; simp) (by simp)
      (by simp)
  exact isRepresentable_of_iso B S hS (show (schemeSpace P).1.IsRepresentable from
    Functor.IsRepresentable.mk' (Iso.refl _))
    ((ObjectProperty.ι _).mapIso (hPG.isoIsPushout _ _ hG))

/-- **Stacks 07VY, `G` on schemes.**  The algebraic space `V ⨿_U U'` glued from a triple
`(V, U', φ)` of schemes is a scheme. -/
theorem isRepresentable_pushoutGluingFunctor_obj (T : pushoutGluingData B S hS i f)
    (hV : T.obj.left.left.1.IsRepresentable) (hU' : T.obj.right.left.1.IsRepresentable) :
    ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left.1.IsRepresentable := by
  obtain ⟨v, u', hpo, -, -⟩ := pushoutGluingFunctor_obj_isPushout B S hS hatlas i f hi hf T
  exact isRepresentable_of_isPushout_of_isThickeningHom hpo.flip
    (isThickeningHom_of_isPullback B S hS (IsPullback.of_hasPullback T.obj.right.hom i).flip hi)
    (isAffineHom_hom_of_isPullback (CategoryTheory.PushoutGluing.sourceMap_isPullback i f T).flip
      hf) hU' hV

end AlgebraicGeometry.Space

end
