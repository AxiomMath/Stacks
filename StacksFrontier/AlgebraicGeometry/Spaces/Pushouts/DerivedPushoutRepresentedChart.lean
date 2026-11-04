module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SchemeChartLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackAlongIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineLegs

/-!
# The affine charts of a pushout along a thickening, as represented affine squares

Let `Y' = Y ⨿_X X'` be the pushout of a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y` of algebraic spaces over `S`, and let `W ⟶ Y'` be an étale chart of `Y'` with affine
underlying scheme. The proof of Stacks 0DL7 passes, over `W`, to the rings of the four corners of
the base change of the pushout square to `W`. This file supplies the geometric half of that
passage: the base change of the square to `W` is isomorphic to the square of algebraic spaces
represented by a commutative square of affine objects of the site, whose rings form a fibre
product `Γ(W) = Γ(W_Y) ×_{Γ(W_X)} Γ(W_{X'})` along a surjection with nil kernel.

## Main definitions

* `AlgebraicGeometry.Space.PushoutGlueingIsIsoStepOnRepresentedAffine`: the isomorphism step of
  Stacks 0DL7 for every commutative square of affine objects of the site whose rings form such a
  fibre product, at the standard models.

## Main results

* `AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_representedAffine`: **Stacks 0DL7 from
  its case on represented affine squares.** The reduction of
  `AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_onAffineChart` is completed: the
  affineness of `X' ⟶ Y'` and the passage from an affine chart of `Y'` to a represented affine
  square are proved here.

## Implementation notes

The facts about the pushout used here come from the construction of the pushout of Stacks 07VX
on the base (`AlgebraicGeometry.Space.hasPushout_of_isThickening_of_isAffineHom`, from a compatible
pair of étale scheme charts, which exist by Stacks 05ZH and Stacks 05ZR); they are proved as
private lemmas of this file.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe t₁ t₂ t₃ t₄ w₁ w₂ w₃ w₄ u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Pushout

variable (B S hS) in
/-- Every thickening-and-affine span of algebraic spaces over `S` has a compatible pair of étale
scheme charts: étale scheme charts lift along thickenings (Stacks 05ZH with Stacks 05ZR). -/
private theorem hasThickeningAffineAtlases' : HasThickeningAffineAtlases B S hS :=
  C1573.hasThickeningAffineAtlases_of_schemeChartLift B S hS
    (C1573.schemeChartLiftProperty_of_thickeningRepresentable B S hS
      (fun i hi hX ↦ isRepresentable_of_isThickeningHom_of_isRepresentable B S hS i hi hX))

/-- The leg `Y ⟶ Y'` of the pushout is a thickening. -/
private theorem pushout_inr_isThickeningHom' {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (f : X ⟶ Y) (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    [HasPushout i f] : IsThickeningHom B S hS (pushout.inr i f) :=
  pushout_inr_isThickening B S hS (hasThickeningAffineAtlases' B S hS) i f hi hf

/-- A thickening of algebraic spaces is affine. -/
private theorem isAffineHom_of_isThickeningHom' {X Y : AlgebraicSpaces B S hS} {b : X ⟶ Y}
    (hb : IsThickeningHom B S hS b) : IsAffineHom B S hS b.hom :=
  isAffineHom_of_isClosedImmersion B S hS b.hom hb.isClosedImmersion

/-- **The leg `X' ⟶ Y'` of a square with two thickenings and an affine morphism is affine.** If
`i : X ⟶ X'` and `j : Y ⟶ Y'` are thickenings, `f : X ⟶ Y` is affine and `i ≫ a = f ≫ j`, then
`a` is affine: over an affine `T ⟶ Y'`, the base change of `a` receives the base change of `i`,
a thickening whose source is the base change of the affine morphism `f ≫ j`, and an algebraic
space with a thickening from an affine one is affine. -/
private theorem isAffineHom_of_isThickeningHom_of_comp_eq {X X' Y Y' : AlgebraicSpaces B S hS}
    {i : X ⟶ X'} {a : X' ⟶ Y'} {f : X ⟶ Y} {j : Y ⟶ Y'} (w : i ≫ a = f ≫ j)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (hj : IsThickeningHom B S hS j) : IsAffineHom B S hS a.hom := by
  intro Z g
  let T : AlgebraicSpaces B S hS :=
    representedAlgebraicSpace B S hS ((BigAffineFppf.inclusion B S hS).obj Z)
  let gs : T ⟶ Y' := ObjectProperty.homMk g
  have hQ := IsPullback.of_hasPullback a gs
  have hP := IsPullback.of_hasPullback i (pullback.fst a gs)
  -- the base change of `i ≫ a = f ≫ j` along `g` is affine
  have hcomp : IsAffineHom B S hS (i ≫ a).hom :=
    w ▸ isAffineHom_comp B S hS f.hom j.hom hf (isAffineHom_of_isThickeningHom' hj)
  obtain ⟨W, p, q, hpq⟩ := hcomp Z g
  have hbig : IsPullback (pullback.fst i (pullback.fst a gs)).hom
      ((pullback.snd i (pullback.fst a gs)).hom ≫ (pullback.snd a gs).hom) (i ≫ a).hom g :=
    (AlgebraicSpaces.isPullback_hom B S hS hP).paste_vert (AlgebraicSpaces.isPullback_hom B S hS hQ)
  have hPaff : IsAffineSpace B S hS (pullback i (pullback.fst a gs)).1 :=
    (isAffineSpace_yoneda B S hS _ W.property).of_iso (hpq.isoIsPullback _ _ hbig)
  -- the base change of `i` is a thickening, so the base change of `a` is affine
  have hth : IsThickeningHom B S hS (pullback.snd i (pullback.fst a gs)) :=
    C1573.isThickeningHom_fst_of_isPullback B S hS hP.flip hi
  obtain ⟨T', hT', ⟨e⟩⟩ := isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS _
    (pullback i (pullback.fst a gs)).property (pullback a gs).property hth.isClosedImmersion
    hth.surjective_pointsMap hPaff
  refine ⟨⟨T', hT'⟩, e.inv ≫ (pullback.fst a gs).hom,
    Yoneda.fullyFaithful.preimage (e.inv ≫ (pullback.snd a gs).hom), ?_⟩
  rw [Functor.FullyFaithful.map_preimage]
  exact IsPullback.of_iso (AlgebraicSpaces.isPullback_hom B S hS hQ) e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp [gs])

/-- **The leg `X' ⟶ Y'` of the pushout is affine.** -/
private alias isAffineHom_pushout_inl' := AlgebraicGeometry.Space.isAffineHom_pushout_inl

/-- **An algebraic space affine over an affine object of the site is represented by an affine
object.** -/
private theorem exists_iso_representedAlgebraicSpace_of_isAffineHom {P : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (p : P ⟶ representedAlgebraicSpace B S hS U) (hp : IsAffineHom B S hS p.hom) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V)),
      Nonempty (representedAlgebraicSpace B S hS V ≅ P) := by
  obtain ⟨W, p', q, hpb⟩ := hp ⟨U, hU⟩ (𝟙 _)
  have : IsIso p' := by
    have h₀ : IsPullback (𝟙 P.1) p.hom p.hom (𝟙 _) := IsPullback.of_id_fst
    rw [← hpb.isoIsPullback_hom_fst _ _ h₀, Category.comp_id]
    infer_instance
  exact ⟨(BigAffineFppf.inclusion B S hS).obj W, W.property,
    ⟨ObjectProperty.isoMk _ (asIso p')⟩⟩

variable (B S hS) in
/-- The object of the site underlying an étale chart. -/
private abbrev chartObj {Y' : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Y'.1) :
    BigFppfOver B S hS :=
  (SmallEtale.toOver B S hS Y'.1).obj W

/-- A morphism of the site is determined by the represented morphism it is a preimage of. -/
private theorem representedSpaceMap_preimage {U V : BigFppfOver B S hS}
    (φ : representedAlgebraicSpace B S hS U ⟶ representedAlgebraicSpace B S hS V) :
    representedSpaceMap B S hS (Yoneda.fullyFaithful.preimage φ.hom) = φ :=
  ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)

/-- **The base change of the pushout square to an affine chart, as a represented affine
square.** For an étale chart `W ⟶ Y'` with affine underlying scheme over which `X' ⟶ Y'` is
affine, the three base changes of `W` are represented by affine objects of the site, compatibly
with the four edges of the square. -/
private theorem exists_representedAffine_chartSquare {X X' Y : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    [HasPushout i f] (W : SmallEtale B S hS (pushout i f).obj)
    (hW : IsAffineChart B S hS (pushout i f).obj W)
    (hX'W : IsAffineHom B S hS
      (pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W)).hom) :
    ∃ (UY UX UX' : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj UY))
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj UX))
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj UX'))
      (eY : representedAlgebraicSpace B S hS UY ≅
        pullback (pushout.inr i f) (chartToSpace B S hS (pushout i f) W))
      (eX : representedAlgebraicSpace B S hS UX ≅
        chartCubeX f (pushout.inr i f) (chartToSpace B S hS (pushout i f) W))
      (eX' : representedAlgebraicSpace B S hS UX' ≅
        pullback (pushout.inl i f) (chartToSpace B S hS (pushout i f) W))
      (gi : UX ⟶ UX') (gf : UX ⟶ UY) (gf' : UX' ⟶ chartObj B S hS W)
      (gj : UY ⟶ chartObj B S hS W),
      gi ≫ gf' = gf ≫ gj ∧
      representedSpaceMap B S hS gj =
        eY.hom ≫ pullback.snd (pushout.inr i f) (chartToSpace B S hS (pushout i f) W) ∧
      representedSpaceMap B S hS gf' =
        eX'.hom ≫ pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W) ∧
      eX.hom ≫ pullback.snd f (pullback.fst (pushout.inr i f)
          (chartToSpace B S hS (pushout i f) W)) = representedSpaceMap B S hS gf ≫ eY.hom ∧
      eX.hom ≫ chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
          (chartToSpace B S hS (pushout i f) W) = representedSpaceMap B S hS gi ≫ eX'.hom := by
  set j := pushout.inr i f
  set f' := pushout.inl i f
  set h := chartToSpace B S hS (pushout i f) W
  have hUW : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartObj B S hS W)) := hW
  have hjW : IsAffineHom B S hS (pullback.snd j h).hom :=
    isAffineHom_of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback j h))
      (isAffineHom_of_isThickeningHom' (pushout_inr_isThickeningHom' i f hi hf))
  have hfW : IsAffineHom B S hS (pullback.snd f (pullback.fst j h)).hom :=
    isAffineHom_of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f (pullback.fst j h))) hf
  obtain ⟨UY, hUY, ⟨eY⟩⟩ :=
    exists_iso_representedAlgebraicSpace_of_isAffineHom hUW (pullback.snd j h) hjW
  obtain ⟨UX, hUX, ⟨eX⟩⟩ := exists_iso_representedAlgebraicSpace_of_isAffineHom hUW
    (pullback.snd f (pullback.fst j h) ≫ pullback.snd j h)
    (isAffineHom_comp B S hS _ _ hfW hjW)
  obtain ⟨UX', hUX', ⟨eX'⟩⟩ :=
    exists_iso_representedAlgebraicSpace_of_isAffineHom hUW (pullback.snd f' h) hX'W
  let gj : UY ⟶ chartObj B S hS W := Yoneda.fullyFaithful.preimage (eY.hom ≫ pullback.snd j h).hom
  let gf' : UX' ⟶ chartObj B S hS W :=
    Yoneda.fullyFaithful.preimage (eX'.hom ≫ pullback.snd f' h).hom
  let gf : UX ⟶ UY :=
    Yoneda.fullyFaithful.preimage (eX.hom ≫ pullback.snd f (pullback.fst j h) ≫ eY.inv).hom
  let gi : UX ⟶ UX' := Yoneda.fullyFaithful.preimage
    (eX.hom ≫ chartCubeI i f f' j pushout.condition h ≫ eX'.inv).hom
  have hgj : representedSpaceMap B S hS gj = eY.hom ≫ pullback.snd j h :=
    representedSpaceMap_preimage _
  have hgf' : representedSpaceMap B S hS gf' = eX'.hom ≫ pullback.snd f' h :=
    representedSpaceMap_preimage _
  have hgf : representedSpaceMap B S hS gf =
      eX.hom ≫ pullback.snd f (pullback.fst j h) ≫ eY.inv := representedSpaceMap_preimage _
  have hgi : representedSpaceMap B S hS gi =
      eX.hom ≫ chartCubeI i f f' j pushout.condition h ≫ eX'.inv := representedSpaceMap_preimage _
  refine ⟨UY, UX, UX', hUY, hUX, hUX', eY, eX, eX', gi, gf, gf', gj, ?_, hgj, hgf', ?_, ?_⟩
  · have key : (eX.hom ≫ chartCubeI i f f' j pushout.condition h ≫ eX'.inv) ≫
        (eX'.hom ≫ pullback.snd f' h) =
        (eX.hom ≫ pullback.snd f (pullback.fst j h) ≫ eY.inv) ≫ (eY.hom ≫ pullback.snd j h) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [chartCubeI_snd]
    rw [← hgi, ← hgf', ← hgf, ← hgj] at key
    exact Yoneda.fullyFaithful.map_injective (congrArg (fun φ ↦ φ.hom) key)
  · rw [hgf]; simp; rfl
  · rw [hgi]; simp; rfl

/-- **A scheme étale over the pushout is the pushout of its base changes** (Stacks 07W3 for an
étale chart): the base change of the pushout square along an étale chart `W ⟶ Y'` is a pushout
in the category of algebraic spaces over `S`. -/
private theorem isPushout_chartSquare {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (f : X ⟶ Y) (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    [HasPushout i f] (W : SmallEtale B S hS (pushout i f).obj) :
    IsPushout (chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
        (chartToSpace B S hS (pushout i f) W))
      (pullback.snd f (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))
      (pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W))
      (pullback.snd (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)) := by
  obtain ⟨A⟩ := hasThickeningAffineAtlases' B S hS i f hi hf
  obtain ⟨Epo, aY, bY, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  -- transport the chart of the pushout to `pushout i f`
  let eP : Epo.1 ≅ (pushout i f).1 :=
    { hom := hpush.isoPushout.hom.hom
      inv := hpush.isoPushout.inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) hpush.isoPushout.hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) hpush.isoPushout.inv_hom_id }
  have hinl : aY.hom ≫ eP.hom = (pushout.inl i f).hom :=
    congrArg (fun φ => φ.hom) hpush.inl_isoPushout_hom
  have hinr : bY.hom ≫ eP.hom = (pushout.inr i f).hom :=
    congrArg (fun φ => φ.hom) hpush.inr_isoPushout_hom
  have hqm' : IsPullback (yoneda.map A.s) (yoneda.map A.t) (qm ≫ eP.hom) (qm ≫ eP.hom) :=
    hqm.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simp)
  have hqmS' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (qm ≫ eP.hom) :=
    MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS
  have hqmE' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (qm ≫ eP.hom) :=
    MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE
  have haX'' : IsPullback (yoneda.map A.a) A.p' (qm ≫ eP.hom) (pushout.inl i f).hom :=
    haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinl)
  have hbY'' : IsPullback (yoneda.map A.b) A.q (qm ≫ eP.hom) (pushout.inr i f).hom :=
    hbYc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinr)
  have hback : i.hom ≫ (pushout.inl i f).hom = f.hom ≫ (pushout.inr i f).hom :=
    congrArg (fun φ => φ.hom) (pushout.condition (f := i) (g := f))
  let h := chartToSpace B S hS (pushout i f) W
  have hflat : IsFlat B S hS h.hom :=
    isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS (pushout i f) W)
  exact isPushout_of_isFlat_of_thickeningAffineAtlas B S hS A hqm' hqmS' hqmE' haX'' hbY''
    hback hflat
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback (pushout.inl i f) h).flip)
    (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback (pushout.inr i f) h).flip)
    (AlgebraicSpaces.isPullback_hom B S hS
      (IsPullback.of_hasPullback f (pullback.fst (pushout.inr i f) h)).flip)
    (congrArg (fun φ => φ.hom)
      (chartCubeI_fst i f (pushout.inl i f) (pushout.inr i f) pushout.condition h)).symm
    (congrArg (fun φ => φ.hom)
      (chartCubeI_snd i f (pushout.inl i f) (pushout.inr i f) pushout.condition h)).symm

/-- **The rings of a represented affine pushout square form a fibre product.** If the square of
algebraic spaces represented by a commutative square of affine objects of the site, with a
thickening `UX ⟶ UX'`, is a pushout, then `Γ(UW) = Γ(UY) ×_{Γ(UX)} Γ(UX')`: the square of
schemes is the pushout of Stacks 07RT, by comparison with the pushout of schemes in the site and
Stacks 07SY, and the sections of that pushout are the fibre product (Stacks 07RT). -/
private theorem isPullback_appTop_of_isPushout_representedSpaceMap
    {UX UX' UY UW : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj UX)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UX')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UY)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UW)]
    {gi : UX ⟶ UX'} {gf : UX ⟶ UY} {gf' : UX' ⟶ UW} {gj : UY ⟶ UW}
    (hgi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map gi))
    (hpush : IsPushout (representedSpaceMap B S hS gi) (representedSpaceMap B S hS gf)
      (representedSpaceMap B S hS gf') (representedSpaceMap B S hS gj)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map gj).appTop
      ((BigFppfOver.toScheme B S hS).map gf').appTop
      ((BigFppfOver.toScheme B S hS).map gf).appTop
      ((BigFppfOver.toScheme B S hS).map gi).appTop := by
  obtain ⟨P, a, b, hP⟩ := C1573.exists_isPushout_toScheme_of_isThickening B S hS gi gf hgi
  have hPsp := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS gi gf a b hgi hP
  let φ := hPsp.isoIsPushout _ _ hpush
  have hφl : representedSpaceMap B S hS a ≫ φ.hom = representedSpaceMap B S hS gf' :=
    hPsp.inl_isoIsPushout_hom _ _ hpush
  have hφr : representedSpaceMap B S hS b ≫ φ.hom = representedSpaceMap B S hS gj :=
    hPsp.inr_isoIsPushout_hom _ _ hpush
  let ψ : P ≅ UW := Yoneda.fullyFaithful.preimageIso ((ObjectProperty.ι _).mapIso φ)
  have hψ : representedSpaceMap B S hS ψ.hom = φ.hom := representedSpaceMap_preimage _
  have hψφ : representedSpaceMap B S hS ψ.hom = φ.hom := representedSpaceMap_preimage _
  have hψ : ∀ {V : BigFppfOver B S hS} (c : V ⟶ P) (k : V ⟶ UW),
      representedSpaceMap B S hS c ≫ φ.hom = representedSpaceMap B S hS k → c ≫ ψ.hom = k :=
    fun c k h ↦ Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp]
      exact congrArg (fun k ↦ k.hom)
        ((congrArg (representedSpaceMap B S hS c ≫ ·) hψφ).trans h))
  have hψl := hψ a gf' hφl
  have hψr := hψ b gj hφr
  have hpo : IsPushout ((BigFppfOver.toScheme B S hS).map gi)
      ((BigFppfOver.toScheme B S hS).map gf) ((BigFppfOver.toScheme B S hS).map gf')
      ((BigFppfOver.toScheme B S hS).map gj) :=
    hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((BigFppfOver.toScheme B S hS).mapIso ψ)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by rw [Functor.mapIso_hom, ← (BigFppfOver.toScheme B S hS).map_comp, hψl, Iso.refl_hom,
        Category.id_comp])
      (by rw [Functor.mapIso_hom, ← (BigFppfOver.toScheme B S hS).map_comp, hψr, Iso.refl_hom,
        Category.id_comp])
  exact ThickeningAffinePushoutSituation.sections_isPullback_of_isPushout hgi hpo ⊤

/-- A morphism of the site whose represented morphism of algebraic spaces is a thickening is a
thickening of schemes. -/
private theorem isThickening_toScheme_map_of_isThickeningHom {U V : BigFppfOver B S hS}
    (g : U ⟶ V) (hg : IsThickeningHom B S hS (representedSpaceMap B S hS g)) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map g) :=
  ⟨hg.isClosedImmersion.property (𝟙 _) (𝟙 _) g IsPullback.of_id_fst,
    (hg.surjective.property (𝟙 _) (𝟙 _) g IsPullback.of_id_fst).surj⟩

/-- On global sections, a thickening of affine schemes is surjective with nil kernel. -/
private theorem surjective_appTop_and_ker_le_nilradical {X X' : Scheme.{u}} [IsAffine X']
    {i : X ⟶ X'} (hi : Stacks.Thickenings.IsThickening i) :
    Function.Surjective i.appTop ∧ RingHom.ker i.appTop.hom ≤ nilradical Γ(X', ⊤) := by
  have := hi.1
  exact ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine i).2, fun _ ha ↦
    Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop hi ha⟩

end Pushout

section Reduction

variable (B S hS) in
/-- **The isomorphism step of Stacks 0DL7 on represented affine squares.** For every commutative
square `gi ≫ gf' = gf ≫ gj` of objects of the site with affine underlying schemes whose rings of
global functions form a fibre product `Γ(UW) = Γ(UY) ×_{Γ(UX)} Γ(UX')` along a surjection
`Γ(UX') ⟶ Γ(UX)` with nil kernel, the isomorphism step
(`AlgebraicGeometry.Space.PushoutGlueingIsIsoStep`) holds for the represented square of algebraic
spaces, at the standard models, for pseudo-coherent `M` and `K'` and every `α`. This is the case of
the proof of Stacks 0DL7 that the source settles on rings. -/
def PushoutGlueingIsIsoStepOnRepresentedAffine : Prop :=
  ∀ {UX UX' UY UW : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj UX)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UX')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UY)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj UW)]
    (gi : UX ⟶ UX') (gf : UX ⟶ UY) (gf' : UX' ⟶ UW) (gj : UY ⟶ UW) (w : gi ≫ gf' = gf ≫ gj),
    IsPullback ((BigFppfOver.toScheme B S hS).map gj).appTop
      ((BigFppfOver.toScheme B S hS).map gf').appTop
      ((BigFppfOver.toScheme B S hS).map gf).appTop
      ((BigFppfOver.toScheme B S hS).map gi).appTop →
    Function.Surjective ((BigFppfOver.toScheme B S hS).map gi).appTop →
    RingHom.ker ((BigFppfOver.toScheme B S hS).map gi).appTop.hom ≤
      nilradical Γ((BigFppfOver.toScheme B S hS).obj UX', ⊤) →
    ∀ (M : @DerivedCategory _ _ _ (HasDerivedCategory.standard (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (representedAlgebraicSpace B S hS UY)))))
      (K' : @DerivedCategory _ _ _ (HasDerivedCategory.standard (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS (representedAlgebraicSpace B S hS UX'))))),
      (letI := HasDerivedCategory.standard (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (representedAlgebraicSpace B S hS UY).1 (representedAlgebraicSpace B S hS UY).2).O));
        (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS UY).1
          (representedAlgebraicSpace B S hS UY).2).IsPseudoCoherent M) →
      (letI := HasDerivedCategory.standard (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (representedAlgebraicSpace B S hS UX').1 (representedAlgebraicSpace B S hS UX').2).O));
        (smallEtaleRingedSite B S hS (representedAlgebraicSpace B S hS UX').1
          (representedAlgebraicSpace B S hS UX').2).IsPseudoCoherent K') →
      ∀ α : (smallEtaleDerivedModulePullbackOfModels B S hS (representedSpaceMap B S hS gf)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).obj M ≅
        (smallEtaleDerivedModulePullbackOfModels B S hS (representedSpaceMap B S hS gi)
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).obj K',
      PushoutGlueingIsIsoStep B S hS (representedSpaceMap B S hS gi)
        (representedSpaceMap B S hS gf) (representedSpaceMap B S hS gf')
        (representedSpaceMap B S hS gj) (representedSpaceMap_square B S hS gf' gj gf gi w)
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) M K' α

/-- A square with an isomorphism on top and an identity at the bottom is cartesian. -/
private theorem isPullback_hom_comp_id {C : Type*} [Category* C] {A B D : C} (e : A ≅ B)
    (g : B ⟶ D) {k : A ⟶ D} (hk : k = e.hom ≫ g) : IsPullback e.hom k g (𝟙 D) := by
  subst hk
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Derived pullback along an isomorphism of algebraic spaces, at arbitrary models, reflects
isomorphisms: it is the functor of an equivalence. -/
private theorem isIso_of_isIso_map_smallEtaleDerivedModulePullbackOfModels
    {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (mX : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (mY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    {a b : @DerivedCategory _ _ _ mY} (φ : a ⟶ b)
    (h : IsIso ((smallEtaleDerivedModulePullbackOfModels B S hS e.hom mX mY).map φ)) :
    IsIso φ := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let E := (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      mY).symm.trans ((smallEtaleDerivedModulePullbackEquivalence B S hS e).trans
    (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      mX))
  have : IsIso (E.functor.map φ) := h
  exact isIso_of_reflects_iso φ E.functor

variable (B S hS) in
/-- **The isomorphism step of Stacks 0DL7 on affine étale charts, from its case on represented
affine squares.** The base change of the pushout square to an affine étale chart `W ⟶ Y'` over
which `X' ⟶ Y'` is affine is isomorphic to a represented affine square whose rings form a fibre
product along a surjection with nil kernel (Stacks 07VX, 07W3, 07RT); the isomorphism step is
carried along the isomorphism of squares by
`AlgebraicGeometry.Space.isIso_restrict_of_pushoutGlueingIsIsoStep` with the identity of `W`. -/
theorem derivedPushoutGlueingIsIsoOnAffineChart_of_representedAffine
    (hR : PushoutGlueingIsIsoStepOnRepresentedAffine B S hS) :
    DerivedPushoutGlueingIsIsoOnAffineChart.{t₁, t₂, t₃, t₄, u} B S hS := by
  intro X X' Y i f hi hf _ W hW hX'W mW mYW mXW mX'W M K' hM hK' α
  obtain ⟨UY, UX, UX', hUY, hUX, hUX', eY, eX, eX', gi, gf, gf', gj, hw, hgj, hgf', hgf, hgi⟩ :=
    exists_representedAffine_chartSquare i f hi hf W hW hX'W
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartObj B S hS W)) := hW
  -- the ring conditions on the represented square
  have hth : IsThickeningHom B S hS (representedSpaceMap B S hS gi) :=
    C1573.isThickeningHom_fst_of_isPullback B S hS (IsPullback.of_vert_isIso ⟨hgi.symm⟩)
      (C1573.isThickeningHom_fst_of_isPullback B S hS
        (isPullback_chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
          (chartToSpace B S hS (pushout i f) W)).flip hi)
  have hthS := isThickening_toScheme_map_of_isThickeningHom gi hth
  have hpush : IsPushout (representedSpaceMap B S hS gi) (representedSpaceMap B S hS gf)
      (representedSpaceMap B S hS gf') (representedSpaceMap B S hS gj) :=
    (isPushout_chartSquare i f hi hf W).of_iso eX.symm eX'.symm eY.symm (Iso.refl _)
      (by rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, hgi,
          Category.assoc, Iso.hom_inv_id, Category.comp_id])
      (by rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, hgf,
          Category.assoc, Iso.hom_inv_id, Category.comp_id])
      (by rw [Iso.symm_hom, Iso.eq_inv_comp, hgf']
          exact congrArg (eX'.hom ≫ ·) (Category.comp_id _))
      (by rw [Iso.symm_hom, Iso.eq_inv_comp, hgj]; exact congrArg (eY.hom ≫ ·) (Category.comp_id _))
  have hring := isPullback_appTop_of_isPushout_representedSpaceMap hthS hpush
  obtain ⟨hsurj, hnil⟩ := surjective_appTop_and_ker_le_nilradical hthS
  intro M' u v hT
  have key := isIso_restrict_of_pushoutGlueingIsIsoStep
    (chartCubeI i f (pushout.inl i f) (pushout.inr i f) pushout.condition
      (chartToSpace B S hS (pushout i f) W))
    (pullback.snd f (pullback.fst (pushout.inr i f) (chartToSpace B S hS (pushout i f) W)))
    (pullback.snd (pushout.inl i f) (chartToSpace B S hS (pushout i f) W))
    (pullback.snd (pushout.inr i f) (chartToSpace B S hS (pushout i f) W))
    (representedSpaceMap B S hS gi) (representedSpaceMap B S hS gf)
    (representedSpaceMap B S hS gf') (representedSpaceMap B S hS gj)
    (𝟙 (chartSpace B S hS (pushout i f) W)) eY.hom eX.hom eX'.hom
    (chartCubeI_snd i f (pushout.inl i f) (pushout.inr i f) pushout.condition
      (chartToSpace B S hS (pushout i f) W))
    (representedSpaceMap_square B S hS gf' gj gf gi hw) hgi
    (isPullback_hom_comp_id eY _ hgj)
    (IsPullback.of_horiz_isIso ⟨hgf⟩)
    (isPullback_hom_comp_id eX' _ hgf')
    (isEtale_of_isIso B S hS (𝟙 (chartSpace B S hS (pushout i f) W).1))
    mW mYW mXW mX'W (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) M K' α
    (fun αW ↦ hR gi gf gf' gj hw hring hsurj hnil _ _
      (isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels _ _ mYW M hM)
      (isPseudoCoherent_smallEtaleDerivedModulePullbackOfModels _ _ mX'W K' hK') αW) u v hT
  exact ⟨isIso_of_isIso_map_smallEtaleDerivedModulePullbackOfModels eY _ mYW _ key.1,
    isIso_of_isIso_map_smallEtaleDerivedModulePullbackOfModels eX' _ mX'W _ key.2⟩

variable (B S hS) in
/-- **Stacks 0DL7 from its case on represented affine squares.** The essential image statement
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage` follows from the isomorphism step on
represented affine squares (`AlgebraicGeometry.Space.PushoutGlueingIsIsoStepOnRepresentedAffine`):
`AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_onAffineChart`, with the affineness of
`X' ⟶ Y'` and the passage to represented affine squares proved here. -/
theorem derivedPushoutEssentialImage_of_representedAffine
    (hR : PushoutGlueingIsIsoStepOnRepresentedAffine B S hS) :
    DerivedPushoutEssentialImage.{w₁, w₂, w₃, w₄, u} B S hS :=
  derivedPushoutEssentialImage_of_onAffineChart
    (derivedPushoutGlueingIsIsoOnAffineChart_of_representedAffine B S hS hR)
    (fun i f hi hf _ ↦ isAffineHom_pushout_inl' i f hi hf)

end Reduction

end AlgebraicGeometry.Space

end
