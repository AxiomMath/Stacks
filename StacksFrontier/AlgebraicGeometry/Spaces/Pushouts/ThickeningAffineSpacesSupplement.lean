module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSectionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
import all StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces

/-!
# Supplement to `ThickeningAffineSpaces`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isPullback_chart_inr_of_thickeningAffineAtlas`
* `isPullback_chart_inl_of_thickeningAffineAtlas`
* `exists_pushout_chart_of_thickeningAffineAtlas`
* `exists_etaleChartCube_of_isThickening_of_isAffineHom`
* `universallyInjective_of_isThickeningHom`
* `isIntegralHom_universallyInjective_isSurjective_of_isThickeningHom`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfOver.hasSheafify_type

/-- The chart `V ⟶ Y` of the affine target is the base change along the quotient chart
`P ⟶ Y'` of the right leg `V ⟶ P` of the pushout of charts.

The relation `Rel ⇉ P` restricts on `V` to the kernel pair `T` of the chart of `Y`: the square
of the two right legs `T ⟶ Rel` and `V ⟶ P`, both thickenings by Stacks 07RT, over the two
first projections `T ⟶ V` and `Rel ⟶ P`, both étale, is cartesian. Stacks 07S3 then carries
that square up to the sheaves the charts present. -/
private theorem isPullback_chart_inr_of_thickeningAffineAtlas
    {X X' Y E : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) {b : Y ⟶ E} {qm : yoneda.obj A.P ⟶ E.1}
    (hqm : IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm)
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hb₀ : A.q ≫ b.hom = yoneda.map A.b ≫ qm) :
    IsPullback (yoneda.map A.b) A.q qm b.hom := by
  have := A.isAffineHom_g
  have := A.isAffineHom_gR
  -- the right leg of each scheme pushout is a thickening
  have hbT : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map A.b) :=
    isThickening_inr_of_isPushout _ _ A.isThickening_k A.isPushout_chart
  have hbRT : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map A.bR) :=
    isThickening_inr_of_isPushout _ _ A.isThickening_kR A.isPushout_relation
  -- the two first projections are étale
  have hEs : Etale ((BigFppfOver.toScheme B S hS).map A.s) := by
    have h : (relation B S hS A.s A.t).source = (Over.post B.inclusion).map A.s :=
      prod.lift_snd _ _
    have hrel := A.etaleRelation.etale_source
    rw [h] at hrel
    exact hrel
  have hEsY : Etale ((BigFppfOver.toScheme B S hS).map A.sY) :=
    A.etale_q.property A.q (yoneda.map A.tY) A.sY A.kernelPair_Y.flip
  -- the relation square over the first projections is cartesian
  have hcartScheme : IsPullback ((BigFppfOver.toScheme B S hS).map A.bR)
      ((BigFppfOver.toScheme B S hS).map A.sY) ((BigFppfOver.toScheme B S hS).map A.s)
      ((BigFppfOver.toScheme B S hS).map A.b) :=
    isPullback_of_isThickening_of_etale _ _ _ _ hbRT hbT
      (by simpa only [← Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map A.bR_s)
  have hcart : IsPullback A.bR A.sY A.s A.b :=
    IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hcartScheme
  exact isPullback_chart_of_isPullback_source B S hS Y.property.isSheaf E.property.isSheaf
    A.q qm b.hom A.surjective_q A.etale_q hqmS hqmE A.kernelPair_Y hqm
    A.bR_s A.bR_t hcart hb₀

/-- The chart `U' ⟶ X'` of the thickened space is the base change along the quotient chart
`P ⟶ Y'` of the left leg `U' ⟶ P` of the pushout of charts.

Unlike its companion `AlgebraicGeometry.Space.isPullback_chart_inr_of_thickeningAffineAtlas`
this is not an instance of Stacks 07S3 but descent along the thickening.  The comparison
morphism `U' ⟶ P ×_{Y'} X'` lies over `X'` between two algebraic spaces étale over `X'`, hence
is étale by Stacks 03FV, and its base change along the surjection `i` is the composite
`U ≅ X ×_Y V ≅ X ×_{Y'} P` of the two cartesian squares over the legs of the front span, an
isomorphism; so it is an isomorphism by
`AlgebraicGeometry.Space.isIso_of_isEtale_of_isSurjective_baseChange_isIso`. -/
private theorem isPullback_chart_inl_of_thickeningAffineAtlas
    {X X' Y E : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) (hi : IsThickeningHom B S hS i)
    {aY : X' ⟶ E} {bY : Y ⟶ E} {qm : yoneda.obj A.P ⟶ E.1}
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hback : i.hom ≫ aY.hom = f.hom ≫ bY.hom)
    (hbot : IsPullback (yoneda.map A.b) A.q qm bY.hom)
    (ha₀ : A.p' ≫ aY.hom = yoneda.map A.a ≫ qm) :
    IsPullback (yoneda.map A.a) A.p' qm aY.hom := by
  have hka : A.k ≫ A.a = A.g ≫ A.b :=
    (BigFppfOver.toScheme B S hS).map_injective
      (by simpa only [Functor.map_comp] using A.isPushout_chart.w)
  -- pasting the square over `f` with the square just proved identifies `U` with `X ×_{Y'} P`
  have hUP : IsPullback (yoneda.map (A.g ≫ A.b)) A.p qm (i.hom ≫ aY.hom) := by
    rw [hback]
    simpa only [Functor.map_comp] using A.isPullback_affine.flip.paste_horiz hbot
  have hcomm : yoneda.map A.a ≫ qm = A.p' ≫ aY.hom := ha₀.symm
  have hW : IsPullback (pullback.fst qm aY.hom) (pullback.snd qm aY.hom) qm aY.hom :=
    IsPullback.of_hasPullback _ _
  have hWalg : IsAlgebraicSpace B S hS (pullback qm aY.hom) :=
    isAlgebraicSpace_pullback B S hS qm aY.hom (isAlgebraicSpace_yoneda B S hS A.P)
      X'.property E.property
  have hc₁ : pullback.lift (yoneda.map A.a) A.p' hcomm ≫ pullback.fst qm aY.hom =
      yoneda.map A.a := pullback.lift_fst _ _ _
  have hc₂ : pullback.lift (yoneda.map A.a) A.p' hcomm ≫ pullback.snd qm aY.hom = A.p' :=
    pullback.lift_snd _ _ _
  -- `P ×_{Y'} X' ⟶ X'` is étale, being a base change of the chart `P ⟶ Y'`
  have hbc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hsndE : IsEtale B S hS (pullback.snd qm aY.hom) :=
    isEtale_of_presheaf_etale B S hS (hbc.of_isPullback hW hqmE)
  -- hence so is the comparison morphism, by Stacks 03FV
  have hcE : IsEtale B S hS (pullback.lift (yoneda.map A.a) A.p' hcomm) :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS A.U') hWalg X'.property
      _ A.p' (pullback.snd qm aY.hom)
      (isEtale_of_presheaf_etale B S hS A.etale_p') hsndE hc₂
  -- the chart of `X` is the base change of `P ×_{Y'} X'` along the thickening
  have hwU : yoneda.map (A.g ≫ A.b) ≫ qm = (A.p ≫ i.hom) ≫ aY.hom := by
    rw [Category.assoc]; exact hUP.w
  have hpU : IsPullback (pullback.lift (yoneda.map (A.g ≫ A.b)) (A.p ≫ i.hom) hwU) A.p
      (pullback.snd qm aY.hom) i.hom :=
    IsPullback.of_right (by simpa only [pullback.lift_fst] using hUP)
      (pullback.lift_snd _ _ _) hW
  have hpUsurj : IsSurjective B S hS
      (pullback.lift (yoneda.map (A.g ≫ A.b)) (A.p ≫ i.hom) hwU) :=
    isSurjective_of_isPullback_presheaf X.property hWalg X'.property hpU.flip
      hi.surjective_pointsMap
  have hpUc : pullback.lift (yoneda.map (A.g ≫ A.b)) (A.p ≫ i.hom) hwU =
      yoneda.map A.k ≫ pullback.lift (yoneda.map A.a) A.p' hcomm := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, hc₁, ← Functor.map_comp, hka]
    · rw [pullback.lift_snd, Category.assoc, hc₂]
      exact A.isPullback_thickening.w.symm
  -- so the comparison morphism becomes an isomorphism after that base change
  have hsq : IsPullback (𝟙 (yoneda.obj A.U)) (yoneda.map A.k)
      (pullback.lift (yoneda.map (A.g ≫ A.b)) (A.p ≫ i.hom) hwU)
      (pullback.lift (yoneda.map A.a) A.p' hcomm) :=
    IsPullback.of_right
      (by simpa only [Category.id_comp, hc₂] using A.isPullback_thickening.flip)
      (by simpa only [Category.id_comp] using hpUc) hpU.flip
  have hfstIso : IsIso (pullback.fst
      (pullback.lift (yoneda.map (A.g ≫ A.b)) (A.p ≫ i.hom) hwU)
      (pullback.lift (yoneda.map A.a) A.p' hcomm)) := by
    have : IsIso (hsq.isoPullback.hom ≫ pullback.fst
        (pullback.lift (yoneda.map (A.g ≫ A.b)) (A.p ≫ i.hom) hwU)
        (pullback.lift (yoneda.map A.a) A.p' hcomm)) := by
      rw [hsq.isoPullback_hom_fst]; infer_instance
    exact IsIso.of_isIso_comp_left hsq.isoPullback.hom _
  have hciso : IsIso (pullback.lift (yoneda.map A.a) A.p' hcomm) :=
    isIso_of_isEtale_of_isSurjective_baseChange_isIso B S hS
      (isAlgebraicSpace_yoneda B S hS A.U') (isAlgebraicSpace_yoneda B S hS A.U) hWalg
      _ _ hpUsurj hcE hfstIso
  exact IsPullback.of_iso_pullback ⟨hcomm⟩ (asIso (pullback.lift (yoneda.map A.a) A.p' hcomm))
    hc₁ hc₂

/-- **The pushout of a thickening-and-affine span of algebraic spaces, together with the chart
of it carried by a compatible pair of étale scheme charts and both cartesian chart squares.**

This strengthens `AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas` in the
one respect in which that theorem is weaker than equation 81.6.5.1: the two chart squares are
asserted *cartesian* here, not merely commuting.  And unlike
`AlgebraicGeometry.Space.exists_etaleChartCube_of_isThickening_of_isAffineHom`, which quantifies
over the atlas and so discards it, the atlas `A` is a parameter here, so the relation data
`A.Rel`, `A.s`, `A.t`, `A.R'`, `A.T`, `A.aR`, `A.bR` and `A.isPushout_relation` stay available
to the caller alongside the two squares — with `A.Rel` exhibited as the kernel pair of the chart
`qm` of the pushout.  That combination is what identifies the kernel pair of a chart of an
algebraic space over the pushout with a base change of `A.Rel`, and it is obtainable from
neither of the two theorems above separately. -/
theorem exists_pushout_chart_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) (hi : IsThickeningHom B S hS i) :
    ∃ (E : AlgebraicSpaces B S hS) (aY : X' ⟶ E) (bY : Y ⟶ E) (qm : yoneda.obj A.P ⟶ E.1),
      IsPushout i f aY bY ∧
      IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) qm ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) qm ∧
      IsPullback (yoneda.map A.a) A.p' qm aY.hom ∧
      IsPullback (yoneda.map A.b) A.q qm bY.hom := by
  obtain ⟨E, aY, bY, hpush, qm, hqm, hqmS, hqmE, ha₀, hb₀⟩ :=
    isPushout_quotient_of_thickeningAffineAtlas B S hS A
  have hbot : IsPullback (yoneda.map A.b) A.q qm bY.hom :=
    isPullback_chart_inr_of_thickeningAffineAtlas B S hS A hqm hqmS hqmE hb₀
  have hback : i.hom ≫ aY.hom = f.hom ≫ bY.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun φ => φ.hom) hpush.w
  exact ⟨E, aY, bY, qm, hpush, hqm, hqmS, hqmE,
    isPullback_chart_inl_of_thickeningAffineAtlas B S hS A hi hqmE hback hbot ha₀, hbot⟩

/-! ### The cube of étale charts -/

/-- **Stacks 07W1**, equation 81.6.5.1 of the proof of Stacks 07W0: the cube of étale charts of
a thickening-and-affine span and of its pushout.

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine
morphism. There are a surjective étale scheme chart `V ⟶ Y` of the affine target, the chart
`U = X ×_Y V` of `X` it determines, a surjective étale scheme chart `U' ⟶ X'` of `X'` with
`U = X ×_{X'} U'` — so that `U ⟶ U'` is again a thickening of schemes and `U ⟶ V` again
affine — the pushout of schemes `P = U' ⨿_U V`, and the pushout of algebraic spaces
`Y' = Y ⨿_X X'`, arranged in a cube whose back face is the span and its pushout, whose front
face is the charts and their pushout, and whose northeast arrows are the four chart morphisms:

```
back face:    X  ⟶ X'        front face:   U  ⟶ U'
              ↓     ↓                      ↓     ↓
              Y  ⟶ Y'                      V  ⟶ P

northeast arrows:   U ⟶ X,  U' ⟶ X',  V ⟶ Y,  P ⟶ Y'
```

The back square `X, X', Y, Y'` and the front square `U, U', V, P` are pushouts, the four
lateral squares — `U, U', X, X'` and `U, V, X, Y` over the two legs of the front span, and
`U', P, X', Y'` and `V, P, Y, Y'` over the two legs of the back pushout — are cartesian, and
the four northeast arrows are surjective and étale.

Only the two squares over the legs of the pushout have content beyond the construction. For
`V, P, Y, Y'` it is `AlgebraicGeometry.Space.isPullback_chart_inr_of_thickeningAffineAtlas`.
For `U', P, X', Y'` it is descent along the thickening: the comparison morphism
`U' ⟶ P ×_{Y'} X'` lies over `X'` between two algebraic spaces étale over `X'`, hence is étale
by Stacks 03FV, and its base change along the surjection `i` is the composite
`U ≅ X ×_Y V ≅ X ×_{Y'} P` of the other two cartesian squares, an isomorphism; so it is an
isomorphism by
`AlgebraicGeometry.Space.isIso_of_isEtale_of_isSurjective_baseChange_isIso`. -/
theorem exists_etaleChartCube_of_isThickening_of_isAffineHom
    (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    ∃ (U U' V P : BigFppfOver B S hS) (Y' : AlgebraicSpaces B S hS)
      (aY : X' ⟶ Y') (bY : Y ⟶ Y') (k : U ⟶ U') (g : U ⟶ V) (aP : U' ⟶ P) (bP : V ⟶ P)
      (p : yoneda.obj U ⟶ X.1) (p' : yoneda.obj U' ⟶ X'.1) (q : yoneda.obj V ⟶ Y.1)
      (r : yoneda.obj P ⟶ Y'.1),
      IsPushout i f aY bY ∧
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map aP) ((BigFppfOver.toScheme B S hS).map bP) ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) ∧
      IsPullback (yoneda.map k) p p' i.hom ∧
      IsPullback p (yoneda.map g) f.hom q ∧
      IsPullback (yoneda.map aP) p' r aY.hom ∧
      IsPullback (yoneda.map bP) q r bY.hom ∧
      IsSurjective B S hS p ∧ IsEtale B S hS p ∧
      IsSurjective B S hS p' ∧ IsEtale B S hS p' ∧
      IsSurjective B S hS q ∧ IsEtale B S hS q ∧
      IsSurjective B S hS r ∧ IsEtale B S hS r := by
  obtain ⟨A⟩ := hatlas i f hi hf
  obtain ⟨E, aY, bY, qm, hpush, -, hqmS, hqmE, hright, hbot⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  exact ⟨A.U, A.U', A.V, A.P, E, aY, bY, A.k, A.g, A.a, A.b, A.p, A.p', A.q, qm,
    hpush, A.isPushout_chart, A.isThickening_k, A.isAffineHom_g,
    A.isPullback_thickening, A.isPullback_affine, hright, hbot,
    isSurjective_of_presheafSurjective B S hS A.p A.surjective_p,
    isEtale_of_presheaf_etale B S hS A.etale_p,
    isSurjective_of_presheafSurjective B S hS A.p' A.surjective_p',
    isEtale_of_presheaf_etale B S hS A.etale_p',
    isSurjective_of_presheafSurjective B S hS A.q A.surjective_q,
    isEtale_of_presheaf_etale B S hS A.etale_q,
    isSurjective_of_presheafSurjective B S hS qm hqmS,
    isEtale_of_presheaf_etale B S hS hqmE⟩

/-! ### Lifting an étale scheme chart across the thickening -/

/-- A thickening of algebraic spaces over `S`, in the morphism form of
`AlgebraicGeometry.Space.IsThickeningHom`, is universally injective.

A thickening factors as an isomorphism onto its range followed by the inclusion of that range,
and both factors are universally injective: the first by
`AlgebraicGeometry.Space.universallyInjective_of_isIso` and the second by
`AlgebraicGeometry.Space.universallyInjective_ι_of_isThickening`. -/
theorem universallyInjective_of_isThickeningHom {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'}
    (hi : IsThickeningHom B S hS i) :
    UniversallyInjective B S hS i.hom := by
  have := hi.1
  have h := universallyInjective_comp B S hS hi.2.1.1 X'.property
    (Subfunctor.toRange i.hom) (Subfunctor.range i.hom).ι
    (universallyInjective_of_isIso B S hS (Subfunctor.toRange i.hom))
    (universallyInjective_ι_of_isThickening B S hS hi.2)
  rwa [Subfunctor.toRange_ι] at h

/-- **Stacks 05ZL, morphism form.** A thickening of algebraic spaces over `S`, in the morphism
form of `AlgebraicGeometry.Space.IsThickeningHom`, is integral, universally injective and
surjective.

Integrality is Stacks 081Y applied to
`AlgebraicGeometry.Space.IsThickeningHom.isClosedImmersion`, universal injectivity is
`AlgebraicGeometry.Space.universallyInjective_of_isThickeningHom`, and surjectivity is
`AlgebraicGeometry.Space.IsThickeningHom.surjective_pointsMap`. This is the hypothesis shape in
which Stacks 07VW is stated. -/
theorem isIntegralHom_universallyInjective_isSurjective_of_isThickeningHom
    {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i) :
    IsIntegralHom B S hS i.hom ∧ UniversallyInjective B S hS i.hom ∧
      IsSurjective B S hS i.hom :=
  ⟨isIntegralHom_of_isClosedImmersion B S hS i.hom hi.isClosedImmersion,
    universallyInjective_of_isThickeningHom B S hS hi, hi.surjective_pointsMap⟩

end AlgebraicGeometry.Space

end
