module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingUnit

/-!
# Pushouts of algebraic spaces along a thickening of finite order and an affine morphism

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` whose range has finite order, and
let `f : X ⟶ Y` be an affine morphism.  This file proves, with no further hypothesis, the
statements of [Stacks Project, Tag 07VX], [Stacks Project, Tag 07W0] and
[Stacks Project, Tag 07W3] for such a span: the pushout `Y' = Y ⨿_X X'` exists; a triple
`(V, U', φ)` over the span is glued by the pushout `V ⨿_U U'`, which recovers `V` and `U'` by
base change; the glued space is locally of finite type, flat, flat and locally of finite
presentation, smooth or étale over `Y'` exactly when both `V ⟶ Y` and `U' ⟶ X'` are; and an
algebraic space flat over `Y'` is the pushout of its base changes to `Y`, `X` and `X'`.

## Main results

* `AlgebraicGeometry.Space.nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening`: the
  compatible étale charts of the span.
* `AlgebraicGeometry.Space.hasPushout_of_isFiniteOrderThickening`: the pushout exists.
* `AlgebraicGeometry.Space.hasPushout_triple_of_isFiniteOrderThickening`: so does the pushout
  `V ⨿_U U'` of every triple over the span.
* `AlgebraicGeometry.Space.isPullback_glued_of_isFiniteOrderThickening`: the glued space recovers
  the triple by base change.
* `AlgebraicGeometry.Space.glued_properties_iff_of_isFiniteOrderThickening`: clauses (1)–(5) of
  Stacks 07W3.
* `AlgebraicGeometry.Space.isPushout_of_isFlat_of_isFiniteOrderThickening`: an algebraic space
  flat over `Y'` is the pushout of its base changes.

## Implementation notes

The gluing results for algebraic spaces are proved from the compatible étale charts of
`AlgebraicGeometry.Space.ThickeningAffineAtlas`, and for a general thickening they take them as the
hypothesis `AlgebraicGeometry.Space.HasThickeningAffineAtlases`, which rests on the lift of an
étale scheme chart across the thickening (Stacks 05ZS) and so on Stacks 05ZR.  At a
thickening of finite order the lift is unconditional,
`AlgebraicGeometry.Space.exists_etaleChart_lift_of_isFiniteOrderThickening`, so every statement
here is proved span by span from charts of that one span.  Base changes of `i` again have range
of finite order (`AlgebraicGeometry.Space.isFiniteOrderThickening_range_of_isPullback`), which is
what makes the span of every triple a span of the same kind.

These are the statements of Stacks 07VX, 07W0 and 07W3 under the extra hypothesis that the
thickening has finite order.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The compatible étale charts of a finite-order thickening-and-affine span.**  A span
`X' ⟵ X ⟶ Y` of algebraic spaces over `S`, with `i : X ⟶ X'` a thickening whose range has finite
order and `f : X ⟶ Y` affine, admits a `AlgebraicGeometry.Space.ThickeningAffineAtlas`. -/
theorem nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
    (hf : IsAffineHom B S hS f.hom) :
    Nonempty (ThickeningAffineAtlas B S hS i f) :=
  nonempty_thickeningAffineAtlas_of_chartLift B S hS i f hi hf
    (exists_etaleChart_lift_of_isFiniteOrderThickening B S hS i hi hn)

/-- **Stacks 07VX at a thickening of finite order.**  The pushout `Y ⨿_X X'` of a thickening
`i : X ⟶ X'` of algebraic spaces over `S` whose range has finite order along an affine morphism
`f : X ⟶ Y` exists in the category of algebraic spaces over `S`. -/
theorem hasPushout_of_isFiniteOrderThickening
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
    (hf : IsAffineHom B S hS f.hom) :
    HasPushout i f := by
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening B S hS i f hi hn hf
  obtain ⟨_, _, _, hpo, -⟩ := isPushout_quotient_of_thickeningAffineAtlas B S hS A
  exact hpo.hasPushout

/-- **The span of a triple is again a finite-order thickening-and-affine span.**  If
`U = U' ×_{X'} X = V ×_Y X`, then `U ⟶ U'` is a thickening whose range has finite order and
`U ⟶ V` is affine, so the pushout `V ⨿_U U'` exists. -/
theorem hasPushout_triple_of_isFiniteOrderThickening
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y} (hi : IsThickeningHom B S hS i)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
    (hf : IsAffineHom B S hS f.hom)
    {U U' V : AlgebraicSpaces B S hS} {jU : U ⟶ U'} {σ : U ⟶ V} {pU : U ⟶ X}
    {u' : U' ⟶ X'} {v : V ⟶ Y} (hU' : IsPullback jU pU u' i) (hV : IsPullback σ pU v f) :
    HasPushout jU σ :=
  hasPushout_of_isFiniteOrderThickening B S hS jU σ
    (isThickeningHom_of_isPullback B S hS hU'.flip hi)
    (isFiniteOrderThickening_range_of_isPullback B S hS hU'.flip hn)
    (isAffineHom_hom_of_isPullback hV.flip hf)

section Glued

variable {B S hS} {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
  (hi : IsThickeningHom B S hS i)
  (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
  (hf : IsAffineHom B S hS f.hom)
  {E : AlgebraicSpaces B S hS} {aY : X' ⟶ E} {bY : Y ⟶ E} (hE : IsPushout i f aY bY)
  {U U' V : AlgebraicSpaces B S hS} {jU : U ⟶ U'} {σ : U ⟶ V} {pU : U ⟶ X}
  {u' : U' ⟶ X'} {v : V ⟶ Y} (hU' : IsPullback jU pU u' i) (hV : IsPullback σ pU v f)
  {G : AlgebraicSpaces B S hS} {aG : U' ⟶ G} {bG : V ⟶ G} (hG : IsPushout jU σ aG bG)
  {g : G ⟶ E} (haG : aG ≫ g = u' ≫ aY) (hbG : bG ≫ g = v ≫ bY)

include hi hn hf hE hU' hV hG haG hbG

/-- **Stacks 07W0 at a thickening of finite order.**  Let `(V, U', φ)` be a triple over a span
`X' ⟵ X ⟶ Y` whose first leg is a thickening of finite order and whose second leg is affine,
with `U = U' ×_{X'} X = V ×_Y X`, and let `G = V ⨿_U U'` with its morphism `g` to
`Y' = Y ⨿_X X'`.  Then base change recovers the triple: `V = G ×_{Y'} Y` and
`U' = G ×_{Y'} X'`. -/
theorem isPullback_glued_of_isFiniteOrderThickening :
    IsPullback bG v g bY ∧ IsPullback aG u' g aY := by
  obtain ⟨D, hDV, hDU, hDY, hDX⟩ :=
    exists_thickeningAffineGluingChart_of_isFiniteOrderThickening B S hS hi hn hf hE hU' hV hG
      haG hbG
  exact ⟨IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      (D.isPullback_v hbG hDV hDY).flip,
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_u' haG hDU hDX).flip⟩

/-- **Stacks 07W3, clauses (1)–(5), at a thickening of finite order.**  In the situation of
`AlgebraicGeometry.Space.isPullback_glued_of_isFiniteOrderThickening`, the glued morphism
`G ⟶ Y'` is
1. locally of finite type,
2. flat,
3. flat and locally of finite presentation,
4. smooth,
5. étale,

if and only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem glued_properties_iff_of_isFiniteOrderThickening :
    (IsLocallyOfFiniteType B S hS g.hom ↔
        IsLocallyOfFiniteType B S hS v.hom ∧ IsLocallyOfFiniteType B S hS u'.hom) ∧
      (IsFlat B S hS g.hom ↔ IsFlat B S hS v.hom ∧ IsFlat B S hS u'.hom) ∧
      ((IsFlat B S hS g.hom ∧ IsLocallyOfFinitePresentation B S hS g.hom) ↔
        ((IsFlat B S hS v.hom ∧ IsLocallyOfFinitePresentation B S hS v.hom) ∧
          (IsFlat B S hS u'.hom ∧ IsLocallyOfFinitePresentation B S hS u'.hom))) ∧
      (IsSmooth B S hS g.hom ↔ IsSmooth B S hS v.hom ∧ IsSmooth B S hS u'.hom) ∧
      (IsEtale B S hS g.hom ↔ IsEtale B S hS v.hom ∧ IsEtale B S hS u'.hom) := by
  obtain ⟨D, -, -, -, -⟩ :=
    exists_thickeningAffineGluingChart_of_isFiniteOrderThickening B S hS hi hn hf hE hU' hV hG
      haG hbG
  exact ⟨D.isLocallyOfFiniteType_iff, D.isFlat_iff, D.isFlat_and_isLocallyOfFinitePresentation_iff,
    D.isSmooth_iff, D.isEtale_iff G.property E.property V.property Y.property U'.property
      X'.property⟩

end Glued

section Flat

variable {B S hS}

/-- **The counit assertion of Stacks 07W3 at a thickening of finite order.**  Let
`Y' = Y ⨿_X X'` be the pushout of a thickening `i : X ⟶ X'` of algebraic spaces over `S` whose
range has finite order along an affine morphism `f : X ⟶ Y`.  An algebraic space `W'` flat over
`Y'` is the pushout of its base changes `W'_Y = W' ×_{Y'} Y` and `W'_{X'} = W' ×_{Y'} X'` along
their common restriction `W'_X` to `X`. -/
theorem isPushout_of_isFlat_of_isFiniteOrderThickening
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y} (hi : IsThickeningHom B S hS i)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom))
    (hf : IsAffineHom B S hS f.hom)
    {E : AlgebraicSpaces B S hS} {aY : X' ⟶ E} {bY : Y ⟶ E} (hE : IsPushout i f aY bY)
    {W' WX WX' WY : AlgebraicSpaces B S hS} {w : W' ⟶ E} (hw : IsFlat B S hS w.hom)
    {cX' : WX' ⟶ W'} {pX' : WX' ⟶ X'} {cY : WY ⟶ W'} {pY : WY ⟶ Y}
    {jX' : WX ⟶ WX'} {jY : WX ⟶ WY} {pX : WX ⟶ X}
    (hX'sq : IsPullback cX' pX' w aY) (hYsq : IsPullback cY pY w bY)
    (hjYsq : IsPullback jY pX pY f) (hjX'w : jX' ≫ pX' = pX ≫ i)
    (hsides : jY ≫ cY = jX' ≫ cX') :
    IsPushout jX' jY cX' cY := by
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening B S hS i f hi hn hf
  obtain ⟨Epo, aY₀, bY₀, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  let eP : Epo.1 ≅ E.1 := (ObjectProperty.ι _).mapIso (hpush.isoIsPushout _ _ hE)
  have hinl : aY₀.hom ≫ eP.hom = aY.hom :=
    congrArg (fun φ => φ.hom) (hpush.inl_isoIsPushout_hom _ _ hE)
  have hinr : bY₀.hom ≫ eP.hom = bY.hom :=
    congrArg (fun φ => φ.hom) (hpush.inr_isoIsPushout_hom _ _ hE)
  have key : ∀ {P X Y} {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Epo.1} {d : Y ⟶ Epo.1} {d' : Y ⟶ E.1},
      IsPullback a b c d → d ≫ eP.hom = d' → IsPullback a b (c ≫ eP.hom) d' :=
    fun h hd => h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hd)
  have hqm' := key hqm rfl
  have haX'' := key haX' hinl
  have hbY'' := key hbYc hinr
  exact isPushout_of_isFlat_of_thickeningAffineAtlas B S hS A hqm'
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE) haX'' hbY''
    (congrArg (fun φ => φ.hom) hE.w) hw
    (AlgebraicSpaces.isPullback_hom B S hS hX'sq) (AlgebraicSpaces.isPullback_hom B S hS hYsq)
    (AlgebraicSpaces.isPullback_hom B S hS hjYsq) (congrArg (fun φ => φ.hom) hjX'w)
    (congrArg (fun φ => φ.hom) hsides)

end Flat

end AlgebraicGeometry.Space

end
