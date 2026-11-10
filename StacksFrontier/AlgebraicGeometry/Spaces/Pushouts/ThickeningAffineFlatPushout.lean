module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalenceClauses
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# A flat scheme over a thickening-and-affine pushout, as the pushout of prescribed base changes

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout.  `Stacks.Pushout.isPushout_baseChange_of_flat` says that a
scheme `W` flat over `Y'` is the pushout of its two *canonical* base changes
`W ×_{Y'} Y` and `W ×_{Y'} X'` along their common restriction to `X`.

The statement proved here is the same assertion over a span of **prescribed** objects: given any
cartesian squares exhibiting `WY ⟶ Y` and `WX' ⟶ X'` as the two base changes of `W`, and any
span `WX ⟶ WY`, `WX ⟶ WX'` exhibiting `WX` as the common restriction to `X`, the square with
cocone point `W` is a pushout.

This is the form in which the assertion is consumed by a construction that has already chosen
its objects — for instance the fields `isPushout_chart` and `isPushout_relation` of
`AlgebraicGeometry.Space.ThickeningAffineAtlas`, which are `IsPushout` properties of a square
over objects of a site and so cannot be met by the canonical pullbacks of the statement above.

That prescribed-span form is the engine of the assembly carried out in the second half of this
file.  Granted a compatible pair of étale scheme charts for a thickening-and-affine span of
algebraic spaces — [Stacks Project, Tag 07VX], carried as the hypothesis `hatlas` — an
algebraic space `W'` **flat** over the pushout `Y'` has a *prescribed* atlas of the span of its
triple `F(W')`, whose pushout of charts is a scheme `W₁` carrying a surjective étale chart of
`W'` whose kernel pair is the relation of the atlas.  Hence `W'` is itself a pushout of the
span of its triple, and the counit `G(F(W')) ⟶ W'` of [Stacks Project, Tag 07VY] is an
isomorphism: the counit assertion of [Stacks Project, Tag 07W3].

## Main results

* `Stacks.Pushout.isPushout_of_flat_of_isPullback` and
  `Stacks.Pushout.isPushout_of_flat_of_isPullback_of_isPushout`: the prescribed-span form just
  described, over the canonical pushout and over an arbitrary cocartesian square.
* `AlgebraicGeometry.Space.exists_flat_chart_pullback_of_isFlat` and
  `AlgebraicGeometry.Space.exists_flat_chart_of_thickeningAffineAtlas`: the source's *choose a
  scheme `W'_1` and a surjective étale morphism `W'_1 → Y'_1 ×_{Y'} W'`*.
* `AlgebraicGeometry.Space.exists_chart_pullback_of_isPullback`,
  `AlgebraicGeometry.Space.isPullback_of_chart_squares` and
  `AlgebraicGeometry.Space.isPullback_kernelPair_of_chart_square`: the chart squares of the
  atlas of a triple, their comparisons, and the kernel pairs of its two chart maps.
* `AlgebraicGeometry.Space.isPullback_R'_of_thickeningAffineAtlas` and
  `AlgebraicGeometry.Space.isPullback_T_of_thickeningAffineAtlas`: the two kernel pairs of an
  atlas as base changes of its relation.
* `AlgebraicGeometry.Space.exists_thickeningAffineAtlas_of_isFlat`: the prescribed atlas of the
  triple `F(W')`, for `W'` flat over the pushout.
* `AlgebraicGeometry.Space.isPushout_of_isFlat_of_thickeningAffineAtlas`: such a `W'` is the
  pushout of the span of its triple.
* `AlgebraicGeometry.Space.isIso_pushoutGluingAdjunction_counit_of_isFlat`: the counit
  assertion of [Stacks Project, Tag 07W3].

## Implementation notes

The transport needs no chase through the counit.  The two cartesian squares of
`Stacks.Pushout.gluing_components_isPullback` identify the two pushout inclusions into the
glued scheme with the projections of its base changes; composing them with the counit
isomorphism `Stacks.Pushout.gluingCounit_isIso_of_flat` exhibits the two canonical base changes
of `W` as pullback squares whose cocone point is `W` itself.  Uniqueness of a pullback then
produces the two comparison isomorphisms with the prescribed objects, and uniqueness of the
pullback `WX` produces the third; the one thing that is not automatic is that the comparison
isomorphism obtained from the `Y`-side agrees with the one obtained from the `X'`-side, and that
is exactly what the hypothesis `jY ≫ cY = jX' ≫ cX'` supplies.

Only the commutativity `jX' ≫ pX' = pX ≫ i` of the `X'`-side square is used, not its
cartesianness: the apex `WX` is pinned by the `Y`-side square alone.

## References

* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-- **[Stacks Project, Tag 07RX], the final assertion, over a prescribed span.**  Let
`i : X ⟶ X'` be a thickening of schemes, `f : X ⟶ Y` an affine morphism and `Y' = Y ⨿_X X'` the
pushout, and let `w : W ⟶ Y'` be flat.  Let `cY : WY ⟶ W` over `pY : WY ⟶ Y` exhibit `WY` as
the base change `W ×_{Y'} Y`, let `cX' : WX' ⟶ W` over `pX' : WX' ⟶ X'` exhibit `WX'` as the
base change `W ×_{Y'} X'`, and let `jY : WX ⟶ WY` over `pX : WX ⟶ X` exhibit `WX` as the base
change `WY ×_Y X`, with `jX' : WX ⟶ WX'` lying over `i` and agreeing with `jY` on `W`.  Then
`W` is the pushout of `WY` and `WX'` along `WX`.

This is `Stacks.Pushout.isPushout_baseChange_of_flat` with the canonical base changes replaced
by prescribed ones; see the module documentation. -/
theorem isPushout_of_flat_of_isPullback {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ {W WY WX' WX : Scheme.{u}} (w : W ⟶ pushout i f), Flat w →
      ∀ {cY : WY ⟶ W} {pY : WY ⟶ Y} {cX' : WX' ⟶ W} {pX' : WX' ⟶ X'}
        {jY : WX ⟶ WY} {jX' : WX ⟶ WX'} {pX : WX ⟶ X},
        IsPullback cY pY w (pushout.inr i f) →
        IsPullback cX' pX' w (pushout.inl i f) →
        IsPullback jY pX pY f →
        jX' ≫ pX' = pX ≫ i →
        jY ≫ cY = jX' ≫ cX' →
        IsPushout jY jX' cY cX' := by
  let := hasPushout_of_isThickening i f hi
  intro W WY WX' WX w hflat cY pY cX' pX' jY jX' pX hY hX' hjY hjX'w hcomm
  let := hflat
  let W₀ : Over (pushout i f) := Over.mk w
  let : Flat W₀.hom := hflat
  let T : gluingData i f := (baseChangeFunctor i f hi).obj W₀
  let := gluingHasPushout i f hi T
  -- `W` is the pushout of its two canonical base changes, which are cartesian over `W` itself.
  obtain ⟨Sp, gs, jj, sX, v, u', hpushW, hvY, hvX', hgs, hjjcond⟩ :
      ∃ (Sp : Scheme.{u}) (gs : Sp ⟶ T.obj.left.left) (jj : Sp ⟶ T.obj.right.left)
        (sX : Sp ⟶ X) (v : T.obj.left.left ⟶ W) (u' : T.obj.right.left ⟶ W),
        IsPushout gs jj v u' ∧
        IsPullback v T.obj.left.hom w (pushout.inr i f) ∧
        IsPullback u' T.obj.right.hom w (pushout.inl i f) ∧
        IsPullback gs sX T.obj.left.hom f ∧
        jj ≫ T.obj.right.hom = sX ≫ i := by
    obtain ⟨ec, hecw⟩ : ∃ ec : ((gluingFunctor i f hi).obj T).left ≅ W,
        ec.hom ≫ w = ((gluingFunctor i f hi).obj T).hom := by
      have : IsIso ((gluingAdjunction i f hi).counit.app W₀) :=
        gluingCounit_isIso_of_flat i f hi W₀
      have : IsIso ((Over.forget (pushout i f)).map
        ((gluingAdjunction i f hi).counit.app W₀)) := Functor.map_isIso _ _
      exact ⟨asIso ((Over.forget (pushout i f)).map
        ((gluingAdjunction i f hi).counit.app W₀)),
        ((gluingAdjunction i f hi).counit.app W₀).w⟩
    obtain ⟨hdY, hdX'⟩ := gluing_components_isPullback i f hi T
    refine ⟨pullback T.obj.right.hom i, gluingSourceMap i f T,
      pullback.fst T.obj.right.hom i, pullback.snd T.obj.right.hom i,
      pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ ec.hom,
      pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ ec.hom,
      ?_, ?_, ?_, gluingSourceMap_isPullback i f T, pullback.condition⟩
    · exact (IsPushout.of_hasPushout (pullback.fst T.obj.right.hom i)
        (gluingSourceMap i f T)).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ec
        (by simp) (by simp) (by simp) (by simp)
    · exact hdY.of_iso (Iso.refl _) ec (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp only; exact hecw.symm) (by simp)
    · exact hdX'.of_iso (Iso.refl _) ec (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp only; exact hecw.symm) (by simp)
  -- The comparison isomorphisms with the prescribed objects.
  let eY : WY ≅ T.obj.left.left := hY.isoIsPullback _ _ hvY
  have heYfst : eY.hom ≫ v = cY := hY.isoIsPullback_hom_fst _ _ hvY
  have heYsnd : eY.hom ≫ T.obj.left.hom = pY := hY.isoIsPullback_hom_snd _ _ hvY
  let eX' : WX' ≅ T.obj.right.left := hX'.isoIsPullback _ _ hvX'
  have heX'fst : eX'.hom ≫ u' = cX' := hX'.isoIsPullback_hom_fst _ _ hvX'
  have heX'snd : eX'.hom ≫ T.obj.right.hom = pX' := hX'.isoIsPullback_hom_snd _ _ hvX'
  -- The apex, pinned by the `Y`-side square alone.
  have hjY' : IsPullback (jY ≫ eY.hom) pX T.obj.left.hom f :=
    hjY.of_iso (Iso.refl _) eY (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa using heYsnd.symm) (by simp)
  let e₁ : WX ≅ Sp := hjY'.isoIsPullback _ _ hgs
  have he₁gs : e₁.hom ≫ gs = jY ≫ eY.hom := hjY'.isoIsPullback_hom_fst _ _ hgs
  have he₁snd : e₁.hom ≫ sX = pX := hjY'.isoIsPullback_hom_snd _ _ hgs
  -- The `Y`-side identification of the apex also matches the `X'`-side leg.
  have he₁jj : e₁.hom ≫ jj = jX' ≫ eX'.hom := by
    refine hvX'.hom_ext ?_ ?_
    · rw [Category.assoc, ← hpushW.w, reassoc_of% he₁gs, heYfst, hcomm, Category.assoc, heX'fst]
    · rw [Category.assoc, hjjcond, reassoc_of% he₁snd, ← hjX'w, Category.assoc, heX'snd]
  exact hpushW.of_iso' e₁ eY eX' (Iso.refl _) he₁gs he₁jj
    (by simpa using heYfst) (by simpa using heX'fst)

/-- **[Stacks Project, Tag 07RX], the final assertion, over a prescribed span and an arbitrary
cocartesian square.**  `Stacks.Pushout.isPushout_of_flat_of_isPullback` with the canonical
pushout `pushout k g` replaced by any cocone point `P` of a cocartesian square on the span, so
that it applies to a pushout square carried as data — for instance the field
`AlgebraicGeometry.Space.ThickeningAffineAtlas.isPushout_chart`. -/
theorem isPushout_of_flat_of_isPullback_of_isPushout {U U' V P : Scheme.{u}}
    {k : U ⟶ U'} {g : U ⟶ V} {a : U' ⟶ P} {b : V ⟶ P}
    (hk : IsThickening k) [IsAffineHom g] (hP : IsPushout k g a b)
    {W WV WU' WU : Scheme.{u}} (w : W ⟶ P) (hw : Flat w)
    {cV : WV ⟶ W} {pV : WV ⟶ V} {cU' : WU' ⟶ W} {pU' : WU' ⟶ U'}
    {jV : WU ⟶ WV} {jU' : WU ⟶ WU'} {pU : WU ⟶ U}
    (hV : IsPullback cV pV w b) (hU' : IsPullback cU' pU' w a)
    (hjV : IsPullback jV pU pV g) (hjU' : jU' ≫ pU' = pU ≫ k)
    (hcomm : jV ≫ cV = jU' ≫ cU') :
    IsPushout jV jU' cV cU' := by
  let := hasPushout_of_isThickening k g hk
  have hea : a ≫ hP.isoPushout.hom = pushout.inl k g := hP.inl_isoPushout_hom
  have heb : b ≫ hP.isoPushout.hom = pushout.inr k g := hP.inr_isoPushout_hom
  have : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hw' : Flat (w ≫ hP.isoPushout.hom) :=
    MorphismProperty.RespectsIso.postcomp _ _ _ hw
  refine isPushout_of_flat_of_isPullback k g hk (w ≫ hP.isoPushout.hom) hw' ?_ ?_ hjV hjU' hcomm
  · exact hV.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hP.isoPushout (by simp) (by simp)
      (by simp) (by simp)
  · exact hU'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) hP.isoPushout (by simp) (by simp)
      (by simp) (by simp)

end Stacks.Pushout

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- **The prescribed chart of step (ii), with the intermediate algebraic space exposed.**  Let
`qm : yoneda.obj P₀ ⟶ E` be a surjective étale scheme chart of an algebraic space `E` over `S`
and let `w : W' ⟶ E` be flat.  There are a presheaf `Q` exhibited as the fibre product
`P₀ ×_E W'`, with its two projections `qQ` and `pQ`, and a scheme chart `cQ : W₁ ⟶ Q` of it,
surjective and étale, whose composite with `qQ` is a morphism `χ : W₁ ⟶ P₀` of the site that is
**flat** on schemes.

`AlgebraicGeometry.Space.exists_flat_chart_of_thickeningAffineAtlas` is the shape of this that
the chart half of the atlas of a triple consumes, and it is deduced from this one.  The extra
data here — the fibre product `Q` and the chart `cQ` of it, rather than only the composites
`χ = cQ ≫ qQ` and `W₁ ⟶ W'` — is what the *relation* half needs: flatness of the induced
morphism from the kernel pair of `W₁ ⟶ W'` to the relation of the atlas is proved by exhibiting
that morphism as a base change of `cQ`, and no composite of `χ` and `W₁ ⟶ W'` sees `cQ`. -/
theorem exists_flat_chart_pullback_of_isFlat
    {P₀ : BigFppfOver B S hS} {E : AlgebraicSpaces B S hS}
    (qm : yoneda.obj P₀ ⟶ E.1)
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    {W' : AlgebraicSpaces B S hS} (w : W' ⟶ E) (hw : IsFlat B S hS w.hom) :
    ∃ (Qpsh : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (qQ : Qpsh ⟶ yoneda.obj P₀)
      (pQ : Qpsh ⟶ W'.1) (W₁ : BigFppfOver B S hS) (cQ : yoneda.obj W₁ ⟶ Qpsh)
      (χ : W₁ ⟶ P₀),
      IsPullback qQ pQ qm w.hom ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) pQ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) pQ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) cQ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) cQ ∧
      cQ ≫ qQ = yoneda.map χ ∧
      _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map χ) := by
  let Pspace : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj P₀, isAlgebraicSpace_yoneda B S hS P₀⟩
  let qmSp : Pspace ⟶ E := ObjectProperty.homMk qm
  have hQ : IsPullback (Limits.pullback.fst qmSp w) (Limits.pullback.snd qmSp w) qmSp w :=
    IsPullback.of_hasPullback qmSp w
  have hQh : IsPullback (Limits.pullback.fst qmSp w).hom
      (Limits.pullback.snd qmSp w).hom qm w.hom :=
    AlgebraicSpaces.isPullback_hom B S hS hQ
  have hflatQ : IsFlat B S hS (Limits.pullback.fst qmSp w).hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hQ.flip hw
  have hbcS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbcE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨W₁, cQ, hcS, hcE⟩ := (Limits.pullback qmSp w).property.exists_atlas
  obtain ⟨χ, hχ⟩ : ∃ χ : W₁ ⟶ P₀,
      yoneda.map χ = cQ ≫ (Limits.pullback.fst qmSp w).hom :=
    ⟨yoneda.preimage (show yoneda.obj W₁ ⟶ yoneda.obj P₀ from
      cQ ≫ (Limits.pullback.fst qmSp w).hom), yoneda.map_preimage _⟩
  refine ⟨(Limits.pullback qmSp w).1, (Limits.pullback.fst qmSp w).hom,
    (Limits.pullback.snd qmSp w).hom, W₁, cQ, χ, hQh,
    hbcS.of_isPullback hQh hqmS, hbcE.of_isPullback hQh hqmE, hcS, hcE, hχ.symm, ?_⟩
  refine hflatQ W₁ P₀ cQ (𝟙 (yoneda.obj P₀)) χ hcE ?_ ?_
  · apply AlgebraicGeometry.presheaf_id_of_iso B S hS
    intro Z Z' h hh
    let _ := hh
    change _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h)
    infer_instance
  rw [hχ, Category.comp_id]

/-- **Two chart squares over a common chart compare.**  Let `pW : W₁ ⟶ W'` be a morphism of
presheaves and let `ma` and `mb` exhibit `Za` and `Zb` as base changes of `pW` along
`ca : Fa ⟶ W'` and `cb : Fb ⟶ W'`.  A morphism `φ : Za ⟶ Zb` of the site and a morphism
`ψ : Fa ⟶ Fb` of presheaves which are compatible with the two chart maps and with the two
morphisms to `W'` exhibit `Za` as the base change `Fa ×_{Fb} Zb`.

This is the step that turns the three chart squares of the atlas of a triple into its fields
`isPullback_affine` and `isPullback_thickening`: those two squares are not chart squares but
comparisons between chart squares. -/
theorem isPullback_of_chart_squares
    {W₁ Za Zb : BigFppfOver B S hS} {W'psh Fa Fb : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {pW : yoneda.obj W₁ ⟶ W'psh}
    {ma : yoneda.obj Za ⟶ Fa} {ua : Za ⟶ W₁} {ca : Fa ⟶ W'psh}
    {mb : yoneda.obj Zb ⟶ Fb} {ub : Zb ⟶ W₁} {cb : Fb ⟶ W'psh}
    {φ : Za ⟶ Zb} {ψ : Fa ⟶ Fb}
    (ha : IsPullback ma (yoneda.map ua) ca pW)
    (hb : IsPullback mb (yoneda.map ub) cb pW)
    (hφ : φ ≫ ub = ua) (hψ : ψ ≫ cb = ca)
    (hcomm : ma ≫ ψ = yoneda.map φ ≫ mb) :
    IsPullback ma (yoneda.map φ) ψ mb := by
  refine IsPullback.of_bot ?_ hcomm hb
  rw [← Functor.map_comp, hφ, hψ]
  exact ha

/-- **The kernel pair of a base change of a chart is the base change of its kernel pair.**  Let
`m` exhibit `Z` as a base change of a chart `pW : W₁ ⟶ W'` along `c : F ⟶ W'`, let `σ, τ` be the
kernel pair of `pW`, and let `σK, τK : K ⟶ Z` over `κ : K ⟶ Rel` exhibit `K` as the base change
`F ×_{W'} Rel`, in the form of the cartesian square `hK`.  Then `σK, τK` is the kernel pair
of `m`.

This is the step that gives the atlas of a triple its two kernel-pair fields `kernelPair_X'`
and `kernelPair_Y`; `hK` comes from
`AlgebraicGeometry.Space.exists_chart_pullback_of_isPullback` applied at the relation span. -/
theorem isPullback_kernelPair_of_chart_square
    {W₁ Z K Rel : BigFppfOver B S hS} {W'psh F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {pW : yoneda.obj W₁ ⟶ W'psh} {m : yoneda.obj Z ⟶ F} {u : Z ⟶ W₁} {c : F ⟶ W'psh}
    {σ τ : Rel ⟶ W₁} {κ : K ⟶ Rel} {σK τK : K ⟶ Z}
    (hchart : IsPullback m (yoneda.map u) c pW)
    (hkp : IsPullback (yoneda.map σ) (yoneda.map τ) pW pW)
    (hK : IsPullback (yoneda.map σK ≫ m) (yoneda.map κ) c (yoneda.map σ ≫ pW))
    (hσu : σK ≫ u = κ ≫ σ) (hτu : τK ≫ u = κ ≫ τ)
    (hn : yoneda.map σK ≫ m = yoneda.map τK ≫ m) :
    IsPullback (yoneda.map σK) (yoneda.map τK) m m := by
  have hleft : IsPullback (yoneda.map σK) (yoneda.map κ) (yoneda.map u) (yoneda.map σ) := by
    refine IsPullback.of_right hK ?_ hchart
    rw [← Functor.map_comp, ← Functor.map_comp, hσu]
  refine IsPullback.of_bot ?_ hn hchart
  have h := hleft.paste_vert hkp
  rw [← Functor.map_comp, ← hτu, Functor.map_comp, ← hchart.w] at h
  exact h

/-- **The prescribed chart of step (ii) of the proof of [Stacks Project, Tag 07W3].**  Let `A`
be a `AlgebraicGeometry.Space.ThickeningAffineAtlas` for a thickening-and-affine span of
algebraic spaces over `S`, let `qm : A.P ⟶ E` be the surjective étale scheme chart of the
pushout that it carries, and let `W'` be an algebraic space **flat** over `E`.  There is a
scheme chart `W₁` of `A.P ×_E W'`: a morphism `χ : W₁ ⟶ A.P` of the site lying over a
surjective étale chart `W₁ ⟶ W'`, whose underlying morphism of schemes `W₁ ⟶ A.P` is flat.

This is the source's *"choose a scheme `W'_1` and a surjective étale morphism
`W'_1 → Y'_1 ×_{Y'} W'`; observe that `W'_1 → W'` is surjective étale as a composition of
surjective étale morphisms"*.  It is the one place where flatness of `W'` enters the
construction of the atlas of the triple `F(W')`: the flatness of `χ` is what lets
`Stacks.Pushout.isPushout_of_flat_of_isPullback_of_isPushout` exhibit `W₁` as the scheme
pushout of its own base changes along the two legs `A.a` and `A.b` of `A.isPushout_chart`,
which is the field `isPushout_chart` of the atlas being built.

`A.P ×_E W'` is an algebraic space by Stacks 02X2
(`AlgebraicGeometry.Space.isAlgebraicSpace_pullback`), so it has a scheme chart at all; nothing
has to be known about the size of the scheme pushout `A.P`, which is already an object of the
site by construction of the atlas. -/
theorem exists_flat_chart_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) {E : AlgebraicSpaces B S hS}
    (qm : yoneda.obj A.P ⟶ E.1)
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    {W' : AlgebraicSpaces B S hS} (w : W' ⟶ E) (hw : IsFlat B S hS w.hom) :
    ∃ (W₁ : BigFppfOver B S hS) (χ : W₁ ⟶ A.P) (pW : yoneda.obj W₁ ⟶ W'.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) pW ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) pW ∧
      _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map χ) ∧
      yoneda.map χ ≫ qm = pW ≫ w.hom := by
  obtain ⟨Qpsh, qQ, pQ, W₁, cQ, χ, hQ, hpQS, hpQE, hcS, hcE, hcq, hflat⟩ :=
    exists_flat_chart_pullback_of_isFlat B S hS (P₀ := A.P) qm hqmS hqmE w hw
  have hcompS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hcompE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  refine ⟨W₁, χ, cQ ≫ pQ, MorphismProperty.comp_mem _ _ _ hcS hpQS,
    MorphismProperty.comp_mem _ _ _ hcE hpQE, hflat, ?_⟩
  rw [← hcq, Category.assoc, Category.assoc, hQ.w]

/-- **The chart squares of the atlas of the triple.**  Let `χ : W₁ ⟶ P₀` be a morphism of the
site lying over a map `pW : W₁ ⟶ W'` of presheaves, in the sense that `χ ≫ qm = pW ≫ w` for a
chart `qm : P₀ ⟶ E` and a morphism `w : W' ⟶ E`.  Let `z : Z ⟶ P₀` exhibit `Z` as a base change
`P₀ ×_E D` of some `D ⟶ E`, and let `DW` be the base change `W' ×_E D`.  Then the fibre product
`W₁ ×_{P₀} Z` of the site is the base change `W₁ ×_{W'} DW`.

Specialised to the three legs of `AlgebraicGeometry.Space.ThickeningAffineAtlas` — `A.a` over
`X'`, `A.b` over `Y`, and their common restriction over `X`, each of which is cartesian over
the chart `qm` of the pushout by the two squares of
`AlgebraicGeometry.Space.exists_pushout_chart_of_thickeningAffineAtlas` — this produces the
three charts of the triple `F(W')` together with their chart squares, and hence their
surjectivity and étaleness by base change of `pW`.  The same statement applied to the kernel
pairs produces the identifications of `A.R'` and `A.T` with base changes of `A.Rel`.

`yoneda` preserves the fibre products of the site, so the square of representables over
`W₁ ×_{P₀} Z` is cartesian; the conclusion is that square pasted with the square of `z` and
then cancelled against the square of `DW`. -/
theorem exists_chart_pullback_of_isPullback
    {P₀ W₁ Z : BigFppfOver B S hS} (χ : W₁ ⟶ P₀) (z : Z ⟶ P₀)
    {Epsh Dpsh W'psh DWpsh : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {qm : yoneda.obj P₀ ⟶ Epsh} {c : Dpsh ⟶ Epsh} {wh : W'psh ⟶ Epsh}
    {pZ : yoneda.obj Z ⟶ Dpsh} {pW : yoneda.obj W₁ ⟶ W'psh}
    {cD : DWpsh ⟶ W'psh} {pD : DWpsh ⟶ Dpsh}
    (hZ : IsPullback (yoneda.map z) pZ qm c)
    (hD : IsPullback cD pD wh c)
    (hχ : yoneda.map χ ≫ qm = pW ≫ wh) :
    ∃ m : yoneda.obj (Limits.pullback χ z) ⟶ DWpsh,
      IsPullback m (yoneda.map (Limits.pullback.fst χ z)) cD pW ∧
      m ≫ pD = yoneda.map (Limits.pullback.snd χ z) ≫ pZ := by
  have hsite : IsPullback (yoneda.map (Limits.pullback.fst χ z))
      (yoneda.map (Limits.pullback.snd χ z)) (yoneda.map χ) (yoneda.map z) :=
    IsPullback.map yoneda (IsPullback.of_hasPullback χ z)
  have souter := hsite.paste_vert hZ
  rw [hχ] at souter
  exact ⟨_, IsPullback.of_right' souter.flip hD.flip, hD.flip.lift_fst _ _ _⟩

/-- **The kernel pair of the chart of `X'` is a base change of the relation.**  In the situation
of `AlgebraicGeometry.Space.exists_pushout_chart_of_thickeningAffineAtlas`, the kernel pair
`A.R'` of the chart `A.p'` of `X'` is the base change `A.Rel ×_E X'` of the relation along
`X' ⟶ E`, with `A.aR` as the projection to `A.Rel`.

The relation `A.Rel` is the kernel pair of the chart `qm` of the pushout, `A.R'` is the kernel
pair of `A.p'`, and `A.U'` is the base change `A.P ×_E X'`; so
`A.R' = A.U' ×_{X'} A.U' = A.P ×_E A.U' = (A.P ×_E A.P) ×_E X' = A.Rel ×_E X'`.  That the
canonical projection is `A.aR` is forced by the atlas fields `A.aR_s` and `A.aR_t`, a morphism
into a kernel pair being determined by its two legs.

Together with `AlgebraicGeometry.Space.isPullback_T_of_thickeningAffineAtlas` this is the pair
of identifications that the field `isPushout_relation` of the atlas of a triple needs: it is
what lets `AlgebraicGeometry.Space.exists_chart_pullback_of_isPullback` be applied at the
relation span `(A.kR, A.gR)`, whose pushout is `A.Rel`. -/
theorem isPullback_R'_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) {E : AlgebraicSpaces B S hS}
    {aY : X' ⟶ E} {qm : yoneda.obj A.P ⟶ E.1}
    (hqm : IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm)
    (haX' : IsPullback (yoneda.map A.a) A.p' qm aY.hom) :
    IsPullback (yoneda.map A.aR) (yoneda.map A.s' ≫ A.p')
      (yoneda.map A.s ≫ qm) aY.hom := by
  have outer : IsPullback (yoneda.map A.s') (yoneda.map A.aR ≫ yoneda.map A.t)
      (yoneda.map A.a ≫ qm) qm := by
    rw [haX'.w, ← Functor.map_comp, A.aR_t, Functor.map_comp]
    exact A.kernelPair_X'.paste_vert haX'.flip
  have hcell : IsPullback (yoneda.map A.s') (yoneda.map A.aR)
      (yoneda.map A.a) (yoneda.map A.s) :=
    (IsPullback.paste_vert_iff hqm
      (by rw [← Functor.map_comp, ← Functor.map_comp, A.aR_s])).1 outer
  exact hcell.flip.paste_vert haX'

/-- **The kernel pair of the chart of `Y` is a base change of the relation.**  The `Y`-side
counterpart of `AlgebraicGeometry.Space.isPullback_R'_of_thickeningAffineAtlas`: the kernel pair
`A.T` of the chart `A.q` of `Y` is the base change `A.Rel ×_E Y`, with `A.bR` as the projection
to `A.Rel`. -/
theorem isPullback_T_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) {E : AlgebraicSpaces B S hS}
    {bY : Y ⟶ E} {qm : yoneda.obj A.P ⟶ E.1}
    (hqm : IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm)
    (hbY : IsPullback (yoneda.map A.b) A.q qm bY.hom) :
    IsPullback (yoneda.map A.bR) (yoneda.map A.sY ≫ A.q)
      (yoneda.map A.s ≫ qm) bY.hom := by
  have outer : IsPullback (yoneda.map A.sY) (yoneda.map A.bR ≫ yoneda.map A.t)
      (yoneda.map A.b ≫ qm) qm := by
    rw [hbY.w, ← Functor.map_comp, A.bR_t, Functor.map_comp]
    exact A.kernelPair_Y.paste_vert hbY.flip
  have hcell : IsPullback (yoneda.map A.sY) (yoneda.map A.bR)
      (yoneda.map A.b) (yoneda.map A.s) :=
    (IsPullback.paste_vert_iff hqm
      (by rw [← Functor.map_comp, ← Functor.map_comp, A.bR_s])).1 outer
  exact hcell.flip.paste_vert hbY


/-! ### The prescribed atlas of the triple -/

/-- Base changing a thickening-and-affine pushout of charts along a flat `χ` gives again a pushout,
with thickening and affine legs; the base changes are given by the pullbacks `ha`, `hb`, `hout`. -/
private theorem isPushout_thickening_affine_of_flat
    {P U U' V W₁ U₂ U'₂ V₂ : BigFppfOver B S hS} {k : U ⟶ U'} {g : U ⟶ V} {a : U' ⟶ P}
    {b : V ⟶ P} (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (hg : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g))
    (hP : IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b))
    (χ : W₁ ⟶ P) (hχ : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map χ))
    {a₂ : U'₂ ⟶ W₁} {za : U'₂ ⟶ U'} {b₂ : V₂ ⟶ W₁} {zb : V₂ ⟶ V} {aU : U₂ ⟶ W₁}
    {pU : U₂ ⟶ U} {k₂ : U₂ ⟶ U'₂} {g₂ : U₂ ⟶ V₂}
    (ha : IsPullback a₂ za χ a) (hb : IsPullback b₂ zb χ b) (hout : IsPullback aU pU χ (k ≫ a))
    (hk₂a : k₂ ≫ a₂ = aU) (hk₂z : k₂ ≫ za = pU ≫ k) (hg₂b : g₂ ≫ b₂ = aU)
    (hg₂z : g₂ ≫ zb = pU ≫ g) (hab : k ≫ a = g ≫ b) :
    IsPushout ((BigFppfOver.toScheme B S hS).map k₂) ((BigFppfOver.toScheme B S hS).map g₂)
      ((BigFppfOver.toScheme B S hS).map a₂) ((BigFppfOver.toScheme B S hS).map b₂) ∧
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k₂) ∧
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g₂) := by
  have hk₂bc : IsPullback k₂ pU za k := IsPullback.of_right (by rwa [hk₂a]) hk₂z ha
  have hg₂bc : IsPullback g₂ pU zb g :=
    IsPullback.of_right (by rwa [hg₂b, ← hab]) hg₂z hb
  have := hg
  exact ⟨(Stacks.Pushout.isPushout_of_flat_of_isPullback_of_isPushout hk hP
      ((BigFppfOver.toScheme B S hS).map χ) hχ (IsPullback.map _ hb) (IsPullback.map _ ha)
      (IsPullback.map _ hg₂bc) (by rw [← Functor.map_comp, ← Functor.map_comp, hk₂z])
      (by rw [← Functor.map_comp, ← Functor.map_comp, hg₂b, hk₂a])).flip,
    Stacks.Thickenings.isThickening_of_isPullback (IsPullback.map _ hk₂bc) hk,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsAffineHom) (IsPullback.map _ hg₂bc).flip hg⟩

/-- **Steps (a)–(d) of the assembly: the prescribed atlas of the triple `F(W')`.**  Let `A` be a
`AlgebraicGeometry.Space.ThickeningAffineAtlas` for a thickening-and-affine span
`X' ⟵ X ⟶ Y` of algebraic spaces over `S`, let `E` be its pushout with the surjective étale
scheme chart `qm : A.P ⟶ E` and the two cartesian chart squares that
`AlgebraicGeometry.Space.exists_pushout_chart_of_thickeningAffineAtlas` provides, and let `W'`
be an algebraic space **flat** over `E`.  Let `WX' ⟵ WX ⟶ WY` be the span of the triple
`F(W')`, given as prescribed base changes of `W'` along the two legs of the pushout together
with their common restriction to `X`.

Then that span again carries a `AlgebraicGeometry.Space.ThickeningAffineAtlas`, whose pushout of
charts is a scheme `W₁` carrying a surjective étale chart `pW : W₁ ⟶ W'` **whose kernel pair is
the relation of the atlas**, and whose two chart squares lie over `cX'` and `cY`.

Those last clauses are what makes this atlas the *prescribed* one of the source's proof of
[Stacks Project, Tag 07W3]: `W'` and the pushout that
`AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas` builds from this atlas are
then two sheaves with the same surjective étale chart and the same kernel pair over it, hence
canonically isomorphic, compatibly with the two legs.

The construction is the four steps (a)–(d) of the route recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineGluingDescent`:

* (a) the three chart objects `W₁ ×_{A.P} A.U'`, `W₁ ×_{A.P} A.V` and `W₁ ×_{A.P} A.U`, with
  their chart maps from `AlgebraicGeometry.Space.exists_chart_pullback_of_isPullback` and the
  two fields `isPullback_affine` and `isPullback_thickening` from
  `AlgebraicGeometry.Space.isPullback_of_chart_squares`;
* (b) `isPushout_chart`, an instance of
  `Stacks.Pushout.isPushout_of_flat_of_isPullback_of_isPushout` at `A.isPushout_chart`, which is
  the one place where flatness of `W'` is used;
* (c) the relation half: the kernel pair `Rel` of `pW`, the morphism `ρ : Rel ⟶ A.Rel` induced
  by the kernel-pair square of `qm`, the **flatness of `ρ`** — proved by factoring it as a base
  change of the chart `cQ` of `A.P ×_E W'`, which is étale, followed by the base change of `χ`
  along `A.s`, which is flat — and then `isPushout_relation` by the same engine at the span
  `(A.kR, A.gR)`, using `AlgebraicGeometry.Space.isPullback_R'_of_thickeningAffineAtlas` and
  `AlgebraicGeometry.Space.isPullback_T_of_thickeningAffineAtlas`;
* (d) `etaleRelation` from `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_etaleImage`,
  applied with the two projections **transposed**, since
  `AlgebraicGeometry.Space.relation B S hS s t` is `prod.lift (map t) (map s)`. -/
theorem exists_thickeningAffineAtlas_of_isFlat
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f)
    {E : AlgebraicSpaces B S hS} {aY : X' ⟶ E} {bY : Y ⟶ E}
    {qm : yoneda.obj A.P ⟶ E.1}
    (hqm : IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm)
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (haX' : IsPullback (yoneda.map A.a) A.p' qm aY.hom)
    (hbYc : IsPullback (yoneda.map A.b) A.q qm bY.hom)
    (hback : i.hom ≫ aY.hom = f.hom ≫ bY.hom)
    {W' WX WX' WY : AlgebraicSpaces B S hS} {w : W' ⟶ E} (hw : IsFlat B S hS w.hom)
    {cX' : WX' ⟶ W'} {pX' : WX' ⟶ X'} {cY : WY ⟶ W'} {pY : WY ⟶ Y}
    {jX' : WX ⟶ WX'} {jY : WX ⟶ WY} {pX : WX ⟶ X}
    (hX'sq : IsPullback cX'.hom pX'.hom w.hom aY.hom)
    (hYsq : IsPullback cY.hom pY.hom w.hom bY.hom)
    (hjYsq : IsPullback jY.hom pX.hom pY.hom f.hom)
    (hjX'w : jX'.hom ≫ pX'.hom = pX.hom ≫ i.hom)
    (hsides : jY.hom ≫ cY.hom = jX'.hom ≫ cX'.hom) :
    ∃ (A₂ : ThickeningAffineAtlas B S hS jX' jY) (pW : yoneda.obj A₂.P ⟶ W'.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) pW ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) pW ∧
      IsPullback (yoneda.map A₂.s) (yoneda.map A₂.t) pW pW ∧
      A₂.p' ≫ cX'.hom = yoneda.map A₂.a ≫ pW ∧
      A₂.q ≫ cY.hom = yoneda.map A₂.b ≫ pW := by
  have hbcS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbcE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hcompS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  have hcompE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  obtain ⟨Qpsh, qQ, pQ, W₁, cQ, χ, hQ, hpQS, hpQE, hcQS, hcQE, hcq, hflatχ⟩ :=
    exists_flat_chart_pullback_of_isFlat B S hS (P₀ := A.P) qm hqmS hqmE w hw
  obtain ⟨pW, hpWS, hpWE, hχqm, hcqp⟩ :
      ∃ pW : yoneda.obj W₁ ⟶ W'.1,
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) pW ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) pW ∧
        yoneda.map χ ≫ qm = pW ≫ w.hom ∧ cQ ≫ pQ = pW := by
    refine ⟨cQ ≫ pQ, MorphismProperty.comp_mem _ _ _ hcQS hpQS,
      MorphismProperty.comp_mem _ _ _ hcQE hpQE, ?_, rfl⟩
    rw [← hcq, Category.assoc, Category.assoc, hQ.w]
  -- the two legs of each of the atlas's pushouts agree on the apex, as morphisms of the site
  have hab : A.k ≫ A.a = A.g ≫ A.b :=
    (BigFppfOver.toScheme B S hS).map_injective
      (by simpa only [Functor.map_comp] using A.isPushout_chart.w)
  have habR : A.kR ≫ A.aR = A.gR ≫ A.bR :=
    (BigFppfOver.toScheme B S hS).map_injective
      (by simpa only [Functor.map_comp] using A.isPushout_relation.w)
  -- (a) the three chart objects of the triple, and their chart squares
  obtain ⟨p'₂, hp'₂sq, hp'₂c⟩ :=
    exists_chart_pullback_of_isPullback B S hS χ A.a haX' hX'sq hχqm
  obtain ⟨q₂, hq₂sq, hq₂c⟩ :=
    exists_chart_pullback_of_isPullback B S hS χ A.b hbYc hYsq hχqm
  have hZU : IsPullback (yoneda.map (A.k ≫ A.a)) A.p qm (i.hom ≫ aY.hom) := by
    rw [Functor.map_comp]
    exact A.isPullback_thickening.paste_horiz haX'
  have hWXsq : IsPullback (jY.hom ≫ cY.hom) pX.hom w.hom (i.hom ≫ aY.hom) := by
    rw [hback]
    exact hjYsq.paste_horiz hYsq
  obtain ⟨p₂, hp₂sq, hp₂c⟩ :=
    exists_chart_pullback_of_isPullback B S hS χ (A.k ≫ A.a) hZU hWXsq hχqm
  let U'₂ : BigFppfOver B S hS := Limits.pullback χ A.a
  let a₂ : U'₂ ⟶ W₁ := Limits.pullback.fst χ A.a
  let za' : U'₂ ⟶ A.U' := Limits.pullback.snd χ A.a
  let V₂ : BigFppfOver B S hS := Limits.pullback χ A.b
  let b₂ : V₂ ⟶ W₁ := Limits.pullback.fst χ A.b
  let zb : V₂ ⟶ A.V := Limits.pullback.snd χ A.b
  let U₂ : BigFppfOver B S hS := Limits.pullback χ (A.k ≫ A.a)
  let aU : U₂ ⟶ W₁ := Limits.pullback.fst χ (A.k ≫ A.a)
  let pU : U₂ ⟶ A.U := Limits.pullback.snd χ (A.k ≫ A.a)
  have hk₂cond : aU ≫ χ = (pU ≫ A.k) ≫ A.a := by
    rw [Category.assoc]; exact Limits.pullback.condition
  have hg₂cond : aU ≫ χ = (pU ≫ A.g) ≫ A.b := by
    rw [Category.assoc, ← hab]; exact Limits.pullback.condition
  let k₂ : U₂ ⟶ U'₂ := Limits.pullback.lift aU (pU ≫ A.k) hk₂cond
  let g₂ : U₂ ⟶ V₂ := Limits.pullback.lift aU (pU ≫ A.g) hg₂cond
  have hk₂a : k₂ ≫ a₂ = aU := Limits.pullback.lift_fst _ _ _
  have hk₂z : k₂ ≫ za' = pU ≫ A.k := Limits.pullback.lift_snd _ _ _
  have hg₂b : g₂ ≫ b₂ = aU := Limits.pullback.lift_fst _ _ _
  have hg₂z : g₂ ≫ zb = pU ≫ A.g := Limits.pullback.lift_snd _ _ _
  have hp₂S := hbcS.of_isPullback hp₂sq.flip hpWS
  have hp₂E := hbcE.of_isPullback hp₂sq.flip hpWE
  have hp'₂S := hbcS.of_isPullback hp'₂sq.flip hpWS
  have hp'₂E := hbcE.of_isPullback hp'₂sq.flip hpWE
  have hq₂S := hbcS.of_isPullback hq₂sq.flip hpWS
  have hq₂E := hbcE.of_isPullback hq₂sq.flip hpWE
  have haff : IsPullback p₂ (yoneda.map g₂) jY.hom q₂ := by
    refine isPullback_of_chart_squares B S hS hp₂sq hq₂sq hg₂b rfl ?_
    refine hYsq.hom_ext ?_ ?_
    · calc (p₂ ≫ jY.hom) ≫ cY.hom = p₂ ≫ jY.hom ≫ cY.hom := Category.assoc _ _ _
        _ = yoneda.map aU ≫ pW := hp₂sq.w
        _ = yoneda.map (g₂ ≫ b₂) ≫ pW := by rw [hg₂b]
        _ = yoneda.map g₂ ≫ yoneda.map b₂ ≫ pW := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map g₂ ≫ q₂ ≫ cY.hom := by rw [hq₂sq.w]
        _ = (yoneda.map g₂ ≫ q₂) ≫ cY.hom := (Category.assoc _ _ _).symm
    · calc (p₂ ≫ jY.hom) ≫ pY.hom = p₂ ≫ jY.hom ≫ pY.hom := Category.assoc _ _ _
        _ = p₂ ≫ pX.hom ≫ f.hom := by rw [hjYsq.w]
        _ = (p₂ ≫ pX.hom) ≫ f.hom := (Category.assoc _ _ _).symm
        _ = (yoneda.map pU ≫ A.p) ≫ f.hom := by rw [hp₂c]
        _ = yoneda.map pU ≫ A.p ≫ f.hom := Category.assoc _ _ _
        _ = yoneda.map pU ≫ yoneda.map A.g ≫ A.q := by rw [A.isPullback_affine.w]
        _ = yoneda.map (g₂ ≫ zb) ≫ A.q := by
            rw [hg₂z, Functor.map_comp, Category.assoc]
        _ = yoneda.map g₂ ≫ yoneda.map zb ≫ A.q := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map g₂ ≫ q₂ ≫ pY.hom := by rw [hq₂c]
        _ = (yoneda.map g₂ ≫ q₂) ≫ pY.hom := (Category.assoc _ _ _).symm
  have hthick : IsPullback (yoneda.map k₂) p₂ p'₂ jX'.hom := by
    refine (isPullback_of_chart_squares B S hS hp₂sq hp'₂sq hk₂a hsides.symm ?_).flip
    refine hX'sq.hom_ext ?_ ?_
    · calc (p₂ ≫ jX'.hom) ≫ cX'.hom = p₂ ≫ jX'.hom ≫ cX'.hom := Category.assoc _ _ _
        _ = p₂ ≫ jY.hom ≫ cY.hom := by rw [hsides]
        _ = yoneda.map aU ≫ pW := hp₂sq.w
        _ = yoneda.map (k₂ ≫ a₂) ≫ pW := by rw [hk₂a]
        _ = yoneda.map k₂ ≫ yoneda.map a₂ ≫ pW := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map k₂ ≫ p'₂ ≫ cX'.hom := by rw [hp'₂sq.w]
        _ = (yoneda.map k₂ ≫ p'₂) ≫ cX'.hom := (Category.assoc _ _ _).symm
    · calc (p₂ ≫ jX'.hom) ≫ pX'.hom = p₂ ≫ jX'.hom ≫ pX'.hom := Category.assoc _ _ _
        _ = p₂ ≫ pX.hom ≫ i.hom := by rw [hjX'w]
        _ = (p₂ ≫ pX.hom) ≫ i.hom := (Category.assoc _ _ _).symm
        _ = (yoneda.map pU ≫ A.p) ≫ i.hom := by rw [hp₂c]
        _ = yoneda.map pU ≫ A.p ≫ i.hom := Category.assoc _ _ _
        _ = yoneda.map pU ≫ yoneda.map A.k ≫ A.p' := by
            rw [← A.isPullback_thickening.w]
        _ = yoneda.map (k₂ ≫ za') ≫ A.p' := by
            rw [hk₂z, Functor.map_comp, Category.assoc]
        _ = yoneda.map k₂ ≫ yoneda.map za' ≫ A.p' := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map k₂ ≫ p'₂ ≫ pX'.hom := by rw [hp'₂c]
        _ = (yoneda.map k₂ ≫ p'₂) ≫ pX'.hom := (Category.assoc _ _ _).symm
  -- (b) the field `isPushout_chart`
  obtain ⟨hpushchart, hthickk₂, haffg₂⟩ :=
    isPushout_thickening_affine_of_flat B S hS A.isThickening_k A.isAffineHom_g
      A.isPushout_chart χ hflatχ (IsPullback.of_hasPullback χ A.a)
      (IsPullback.of_hasPullback χ A.b) (IsPullback.of_hasPullback χ (A.k ≫ A.a))
      hk₂a hk₂z hg₂b hg₂z hab
  -- (c) the relation half
  obtain ⟨Rel, σ, τ, hkp⟩ := exists_kernelPair_of_etale_atlas B S hS pW hpWE
  obtain ⟨ρ, hρs, hρt⟩ : ∃ ρ : Rel ⟶ A.Rel, ρ ≫ A.s = σ ≫ χ ∧ ρ ≫ A.t = τ ≫ χ := by
    have hcond : yoneda.map (σ ≫ χ) ≫ qm = yoneda.map (τ ≫ χ) ≫ qm := by
      calc yoneda.map (σ ≫ χ) ≫ qm = yoneda.map σ ≫ yoneda.map χ ≫ qm := by
            rw [Functor.map_comp, Category.assoc]
        _ = (yoneda.map σ ≫ pW) ≫ w.hom := by rw [hχqm, Category.assoc]
        _ = (yoneda.map τ ≫ pW) ≫ w.hom := by rw [hkp.w]
        _ = yoneda.map τ ≫ yoneda.map χ ≫ qm := by rw [hχqm, Category.assoc]
        _ = yoneda.map (τ ≫ χ) ≫ qm := by rw [Functor.map_comp, Category.assoc]
    refine ⟨yoneda.preimage
      (hqm.lift (yoneda.map (σ ≫ χ)) (yoneda.map (τ ≫ χ)) hcond), ?_, ?_⟩
    · refine yoneda.map_injective ?_
      rw [Functor.map_comp, yoneda.map_preimage]
      exact hqm.lift_fst _ _ _
    · refine yoneda.map_injective ?_
      rw [Functor.map_comp, yoneda.map_preimage]
      exact hqm.lift_snd _ _ _
  have hflatρ : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map ρ) := by
    let Zσ : BigFppfOver B S hS := Limits.pullback χ A.s
    let fstZ : Zσ ⟶ W₁ := Limits.pullback.fst χ A.s
    let sndZ : Zσ ⟶ A.Rel := Limits.pullback.snd χ A.s
    let μ : Rel ⟶ Zσ := Limits.pullback.lift σ ρ hρs.symm
    have hμf : μ ≫ fstZ = σ := Limits.pullback.lift_fst _ _ _
    have hμs : μ ≫ sndZ = ρ := Limits.pullback.lift_snd _ _ _
    have hgQcond : yoneda.map (sndZ ≫ A.t) ≫ qm =
        (yoneda.map fstZ ≫ pW) ≫ w.hom := by
      calc yoneda.map (sndZ ≫ A.t) ≫ qm = yoneda.map sndZ ≫ yoneda.map A.t ≫ qm := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map sndZ ≫ yoneda.map A.s ≫ qm := by rw [hqm.w]
        _ = yoneda.map (sndZ ≫ A.s) ≫ qm := by rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (fstZ ≫ χ) ≫ qm := by rw [Limits.pullback.condition]
        _ = yoneda.map fstZ ≫ yoneda.map χ ≫ qm := by
            rw [Functor.map_comp, Category.assoc]
        _ = (yoneda.map fstZ ≫ pW) ≫ w.hom := by rw [hχqm, Category.assoc]
    let gQ : yoneda.obj Zσ ⟶ Qpsh :=
      hQ.lift (yoneda.map (sndZ ≫ A.t)) (yoneda.map fstZ ≫ pW) hgQcond
    have hgQq : gQ ≫ qQ = yoneda.map (sndZ ≫ A.t) := hQ.lift_fst _ _ _
    have hgQp : gQ ≫ pQ = yoneda.map fstZ ≫ pW := hQ.lift_snd _ _ _
    have hZQ : IsPullback (yoneda.map fstZ) gQ pW pQ := by
      refine IsPullback.of_bot ?_ hgQp.symm hQ.flip
      rw [hgQq, ← hχqm, Functor.map_comp]
      exact (IsPullback.map yoneda (IsPullback.of_hasPullback χ A.s)).paste_vert hqm
    have hμsq : IsPullback (yoneda.map τ) (yoneda.map μ) cQ gQ := by
      refine IsPullback.of_bot ?_ ?_ hZQ.flip
      · rw [← Functor.map_comp, hμf, hcqp]
        exact hkp.flip
      · refine hQ.hom_ext ?_ ?_
        · calc (yoneda.map τ ≫ cQ) ≫ qQ = yoneda.map τ ≫ cQ ≫ qQ := Category.assoc _ _ _
            _ = yoneda.map τ ≫ yoneda.map χ := by rw [hcq]
            _ = yoneda.map (τ ≫ χ) := by rw [← Functor.map_comp]
            _ = yoneda.map (ρ ≫ A.t) := by rw [hρt]
            _ = yoneda.map (μ ≫ sndZ ≫ A.t) := by rw [← Category.assoc, hμs]
            _ = yoneda.map μ ≫ yoneda.map (sndZ ≫ A.t) := by rw [Functor.map_comp]
            _ = yoneda.map μ ≫ gQ ≫ qQ := by rw [hgQq]
            _ = (yoneda.map μ ≫ gQ) ≫ qQ := (Category.assoc _ _ _).symm
        · calc (yoneda.map τ ≫ cQ) ≫ pQ = yoneda.map τ ≫ cQ ≫ pQ := Category.assoc _ _ _
            _ = yoneda.map τ ≫ pW := by rw [hcqp]
            _ = yoneda.map σ ≫ pW := hkp.w.symm
            _ = yoneda.map (μ ≫ fstZ) ≫ pW := by rw [hμf]
            _ = yoneda.map μ ≫ yoneda.map fstZ ≫ pW := by
                rw [Functor.map_comp, Category.assoc]
            _ = yoneda.map μ ≫ gQ ≫ pQ := by rw [hgQp]
            _ = (yoneda.map μ ≫ gQ) ≫ pQ := (Category.assoc _ _ _).symm
    have hetaleμ : _root_.AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map μ) := hcQE.property gQ (yoneda.map τ) μ hμsq
    have hflatsndZ : _root_.AlgebraicGeometry.Flat
        ((BigFppfOver.toScheme B S hS).map sndZ) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @_root_.AlgebraicGeometry.Flat.{u})
        (IsPullback.map (BigFppfOver.toScheme B S hS)
          (IsPullback.of_hasPullback χ A.s)) hflatχ
    have := hetaleμ
    have := hflatsndZ
    rw [← hμs, Functor.map_comp]
    infer_instance
  have hρqm : yoneda.map ρ ≫ (yoneda.map A.s ≫ qm) = (yoneda.map σ ≫ pW) ≫ w.hom := by
    calc yoneda.map ρ ≫ yoneda.map A.s ≫ qm = yoneda.map (ρ ≫ A.s) ≫ qm := by
          rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map (σ ≫ χ) ≫ qm := by rw [hρs]
      _ = yoneda.map σ ≫ yoneda.map χ ≫ qm := by rw [Functor.map_comp, Category.assoc]
      _ = (yoneda.map σ ≫ pW) ≫ w.hom := by rw [hχqm, Category.assoc]
  obtain ⟨mR', hmR'sq, hmR'c⟩ :=
    exists_chart_pullback_of_isPullback B S hS ρ A.aR
      (isPullback_R'_of_thickeningAffineAtlas B S hS A hqm haX') hX'sq hρqm
  obtain ⟨mT, hmTsq, hmTc⟩ :=
    exists_chart_pullback_of_isPullback B S hS ρ A.bR
      (isPullback_T_of_thickeningAffineAtlas B S hS A hqm hbYc) hYsq hρqm
  let R'₂ : BigFppfOver B S hS := Limits.pullback ρ A.aR
  let aR₂ : R'₂ ⟶ Rel := Limits.pullback.fst ρ A.aR
  let yR' : R'₂ ⟶ A.R' := Limits.pullback.snd ρ A.aR
  let T₂ : BigFppfOver B S hS := Limits.pullback ρ A.bR
  let bR₂ : T₂ ⟶ Rel := Limits.pullback.fst ρ A.bR
  let yT : T₂ ⟶ A.T := Limits.pullback.snd ρ A.bR
  let R₀₂ : BigFppfOver B S hS := Limits.pullback ρ (A.kR ≫ A.aR)
  let aR₀ : R₀₂ ⟶ Rel := Limits.pullback.fst ρ (A.kR ≫ A.aR)
  let pUR : R₀₂ ⟶ A.R₀ := Limits.pullback.snd ρ (A.kR ≫ A.aR)
  have hs'cond : (aR₂ ≫ σ) ≫ χ = (yR' ≫ A.s') ≫ A.a := by
    rw [Category.assoc, ← hρs, ← Category.assoc, Limits.pullback.condition, Category.assoc,
      A.aR_s, Category.assoc]
  have ht'cond : (aR₂ ≫ τ) ≫ χ = (yR' ≫ A.t') ≫ A.a := by
    rw [Category.assoc, ← hρt, ← Category.assoc, Limits.pullback.condition, Category.assoc,
      A.aR_t, Category.assoc]
  have hsYcond : (bR₂ ≫ σ) ≫ χ = (yT ≫ A.sY) ≫ A.b := by
    rw [Category.assoc, ← hρs, ← Category.assoc, Limits.pullback.condition, Category.assoc,
      A.bR_s, Category.assoc]
  have htYcond : (bR₂ ≫ τ) ≫ χ = (yT ≫ A.tY) ≫ A.b := by
    rw [Category.assoc, ← hρt, ← Category.assoc, Limits.pullback.condition, Category.assoc,
      A.bR_t, Category.assoc]
  let s'₂ : R'₂ ⟶ U'₂ := Limits.pullback.lift (aR₂ ≫ σ) (yR' ≫ A.s') hs'cond
  let t'₂ : R'₂ ⟶ U'₂ := Limits.pullback.lift (aR₂ ≫ τ) (yR' ≫ A.t') ht'cond
  let sY₂ : T₂ ⟶ V₂ := Limits.pullback.lift (bR₂ ≫ σ) (yT ≫ A.sY) hsYcond
  let tY₂ : T₂ ⟶ V₂ := Limits.pullback.lift (bR₂ ≫ τ) (yT ≫ A.tY) htYcond
  have hkR₂cond : aR₀ ≫ ρ = (pUR ≫ A.kR) ≫ A.aR := by
    rw [Category.assoc]; exact Limits.pullback.condition
  have hgR₂cond : aR₀ ≫ ρ = (pUR ≫ A.gR) ≫ A.bR := by
    rw [Category.assoc, ← habR]; exact Limits.pullback.condition
  let kR₂ : R₀₂ ⟶ R'₂ := Limits.pullback.lift aR₀ (pUR ≫ A.kR) hkR₂cond
  let gR₂ : R₀₂ ⟶ T₂ := Limits.pullback.lift aR₀ (pUR ≫ A.gR) hgR₂cond
  have hs'a : s'₂ ≫ a₂ = aR₂ ≫ σ := Limits.pullback.lift_fst _ _ _
  have hs'z : s'₂ ≫ za' = yR' ≫ A.s' := Limits.pullback.lift_snd _ _ _
  have ht'a : t'₂ ≫ a₂ = aR₂ ≫ τ := Limits.pullback.lift_fst _ _ _
  have ht'z : t'₂ ≫ za' = yR' ≫ A.t' := Limits.pullback.lift_snd _ _ _
  have hsYb : sY₂ ≫ b₂ = bR₂ ≫ σ := Limits.pullback.lift_fst _ _ _
  have hsYz : sY₂ ≫ zb = yT ≫ A.sY := Limits.pullback.lift_snd _ _ _
  have htYb : tY₂ ≫ b₂ = bR₂ ≫ τ := Limits.pullback.lift_fst _ _ _
  have htYz : tY₂ ≫ zb = yT ≫ A.tY := Limits.pullback.lift_snd _ _ _
  have hkR₂a : kR₂ ≫ aR₂ = aR₀ := Limits.pullback.lift_fst _ _ _
  have hkR₂y : kR₂ ≫ yR' = pUR ≫ A.kR := Limits.pullback.lift_snd _ _ _
  have hgR₂b : gR₂ ≫ bR₂ = aR₀ := Limits.pullback.lift_fst _ _ _
  have hgR₂y : gR₂ ≫ yT = pUR ≫ A.gR := Limits.pullback.lift_snd _ _ _
  have keyX' : ∀ (r : R'₂ ⟶ U'₂) (sg : Rel ⟶ W₁) (sa : A.R' ⟶ A.U'),
      r ≫ a₂ = aR₂ ≫ sg → r ≫ za' = yR' ≫ sa →
      yoneda.map sg ≫ pW = yoneda.map σ ≫ pW →
      yoneda.map sa ≫ A.p' = yoneda.map A.s' ≫ A.p' →
      yoneda.map r ≫ p'₂ = mR' := by
    intro r sg sa hra hrz hsg hsa
    refine hX'sq.hom_ext ?_ ?_
    · calc (yoneda.map r ≫ p'₂) ≫ cX'.hom = yoneda.map r ≫ p'₂ ≫ cX'.hom :=
            Category.assoc _ _ _
        _ = yoneda.map r ≫ yoneda.map a₂ ≫ pW := by rw [hp'₂sq.w]
        _ = yoneda.map (r ≫ a₂) ≫ pW := by rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (aR₂ ≫ sg) ≫ pW := by rw [hra]
        _ = yoneda.map aR₂ ≫ yoneda.map sg ≫ pW := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map aR₂ ≫ yoneda.map σ ≫ pW := by rw [hsg]
        _ = mR' ≫ cX'.hom := hmR'sq.w.symm
    · calc (yoneda.map r ≫ p'₂) ≫ pX'.hom = yoneda.map r ≫ p'₂ ≫ pX'.hom :=
            Category.assoc _ _ _
        _ = yoneda.map r ≫ yoneda.map za' ≫ A.p' := by rw [hp'₂c]
        _ = yoneda.map (r ≫ za') ≫ A.p' := by rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (yR' ≫ sa) ≫ A.p' := by rw [hrz]
        _ = yoneda.map yR' ≫ yoneda.map sa ≫ A.p' := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map yR' ≫ yoneda.map A.s' ≫ A.p' := by rw [hsa]
        _ = mR' ≫ pX'.hom := hmR'c.symm
  have keyY : ∀ (r : T₂ ⟶ V₂) (sg : Rel ⟶ W₁) (sa : A.T ⟶ A.V),
      r ≫ b₂ = bR₂ ≫ sg → r ≫ zb = yT ≫ sa →
      yoneda.map sg ≫ pW = yoneda.map σ ≫ pW →
      yoneda.map sa ≫ A.q = yoneda.map A.sY ≫ A.q →
      yoneda.map r ≫ q₂ = mT := by
    intro r sg sa hra hrz hsg hsa
    refine hYsq.hom_ext ?_ ?_
    · calc (yoneda.map r ≫ q₂) ≫ cY.hom = yoneda.map r ≫ q₂ ≫ cY.hom :=
            Category.assoc _ _ _
        _ = yoneda.map r ≫ yoneda.map b₂ ≫ pW := by rw [hq₂sq.w]
        _ = yoneda.map (r ≫ b₂) ≫ pW := by rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (bR₂ ≫ sg) ≫ pW := by rw [hra]
        _ = yoneda.map bR₂ ≫ yoneda.map sg ≫ pW := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map bR₂ ≫ yoneda.map σ ≫ pW := by rw [hsg]
        _ = mT ≫ cY.hom := hmTsq.w.symm
    · calc (yoneda.map r ≫ q₂) ≫ pY.hom = yoneda.map r ≫ q₂ ≫ pY.hom :=
            Category.assoc _ _ _
        _ = yoneda.map r ≫ yoneda.map zb ≫ A.q := by rw [hq₂c]
        _ = yoneda.map (r ≫ zb) ≫ A.q := by rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map (yT ≫ sa) ≫ A.q := by rw [hrz]
        _ = yoneda.map yT ≫ yoneda.map sa ≫ A.q := by
            rw [Functor.map_comp, Category.assoc]
        _ = yoneda.map yT ≫ yoneda.map A.sY ≫ A.q := by rw [hsa]
        _ = mT ≫ pY.hom := hmTc.symm
  have hs'p : yoneda.map s'₂ ≫ p'₂ = mR' := keyX' s'₂ σ A.s' hs'a hs'z rfl rfl
  have ht'p : yoneda.map t'₂ ≫ p'₂ = mR' :=
    keyX' t'₂ τ A.t' ht'a ht'z hkp.w.symm A.kernelPair_X'.w.symm
  have hsYp : yoneda.map sY₂ ≫ q₂ = mT := keyY sY₂ σ A.sY hsYb hsYz rfl rfl
  have htYp : yoneda.map tY₂ ≫ q₂ = mT :=
    keyY tY₂ τ A.tY htYb htYz hkp.w.symm A.kernelPair_Y.w.symm
  have hkpX' : IsPullback (yoneda.map s'₂) (yoneda.map t'₂) p'₂ p'₂ := by
    refine isPullback_kernelPair_of_chart_square B S hS hp'₂sq hkp ?_ hs'a ht'a ?_
    · rw [hs'p]; exact hmR'sq
    · rw [hs'p, ht'p]
  have hkpY : IsPullback (yoneda.map sY₂) (yoneda.map tY₂) q₂ q₂ := by
    refine isPullback_kernelPair_of_chart_square B S hS hq₂sq hkp ?_ hsYb htYb ?_
    · rw [hsYp]; exact hmTsq
    · rw [hsYp, htYp]
  obtain ⟨hpushrel, hthickkR₂, haffgR₂⟩ :=
    isPushout_thickening_affine_of_flat B S hS A.isThickening_kR A.isAffineHom_gR
      A.isPushout_relation ρ hflatρ (IsPullback.of_hasPullback ρ A.aR)
      (IsPullback.of_hasPullback ρ A.bR) (IsPullback.of_hasPullback ρ (A.kR ≫ A.aR))
      hkR₂a hkR₂y hgR₂b hgR₂y habR
  -- (d) the étale equivalence relation, and the atlas itself
  let A₂ : ThickeningAffineAtlas B S hS jX' jY :=
    { U := U₂
      U' := U'₂
      V := V₂
      R₀ := R₀₂
      R' := R'₂
      T := T₂
      P := W₁
      Rel := Rel
      p := p₂
      p' := p'₂
      q := q₂
      k := k₂
      g := g₂
      kR := kR₂
      gR := gR₂
      s' := s'₂
      t' := t'₂
      sY := sY₂
      tY := tY₂
      a := a₂
      b := b₂
      aR := aR₂
      bR := bR₂
      s := σ
      t := τ
      isPullback_affine := haff
      isPullback_thickening := hthick
      isThickening_k := hthickk₂
      isAffineHom_g := haffg₂
      isThickening_kR := hthickkR₂
      isAffineHom_gR := haffgR₂
      surjective_p := hp₂S
      etale_p := hp₂E
      surjective_p' := hp'₂S
      etale_p' := hp'₂E
      surjective_q := hq₂S
      etale_q := hq₂E
      kernelPair_X' := hkpX'
      kernelPair_Y := hkpY
      isPushout_chart := hpushchart
      isPushout_relation := hpushrel
      aR_s := hs'a.symm
      aR_t := ht'a.symm
      bR_s := hsYb.symm
      bR_t := htYb.symm
      etaleRelation :=
        isEtaleEquivalenceRelation_etaleImage B S hS W₁ pW hpWE τ σ hkp.flip }
  exact ⟨A₂, pW, hpWS, hpWE, hkp, hp'₂sq.w, hq₂sq.w⟩


/-- **Step (e), first half: a flat algebraic space over the pushout IS the pushout of the span of
its triple.**  In the situation of
`AlgebraicGeometry.Space.exists_thickeningAffineAtlas_of_isFlat`, the prescribed span
`WX' ⟵ WX ⟶ WY` of base changes of `W'` has `W'` itself, with the two projections `cX'` and
`cY`, as a pushout.

This is the content of the counit assertion of [Stacks Project, Tag 07W3], before it is read off
as a statement about the adjunction of [Stacks Project, Tag 07VY].  The proof is the second half
of step (e): `AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas` applied to the
atlas of the triple produces *a* pushout `E₂` of the span, carrying a surjective étale chart
`qm₂` of `E₂` on the prescribed scheme `A₂.P` whose kernel pair is `A₂.s, A₂.t`.  But the chart
`pW` of `W'` is a surjective étale chart on the *same* scheme with the *same* kernel pair, so
each of `E₂` and `W'` is the quotient of that scheme by that relation: the two descended
morphisms between them compose to the identity on either side, by the uniqueness half of
`AlgebraicGeometry.Space.existsUnique_desc_of_surjective_etale_atlas`.  That isomorphism carries
the two legs of `E₂` to `cX'` and `cY`, because it does so after composition with the surjective
étale chart `A₂.p'`, resp. `A₂.q`.

No step here needs Tag 03FS or Tag 05W5, which the recorded route priced for it: the comparison
is an isomorphism because both objects are quotients of one relation, so neither étaleness of
the comparison nor its universal injectivity has to be proved. -/
theorem isPushout_of_isFlat_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f)
    {E : AlgebraicSpaces B S hS} {aY : X' ⟶ E} {bY : Y ⟶ E}
    {qm : yoneda.obj A.P ⟶ E.1}
    (hqm : IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm)
    (hqmS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (hqmE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) qm)
    (haX' : IsPullback (yoneda.map A.a) A.p' qm aY.hom)
    (hbYc : IsPullback (yoneda.map A.b) A.q qm bY.hom)
    (hback : i.hom ≫ aY.hom = f.hom ≫ bY.hom)
    {W' WX WX' WY : AlgebraicSpaces B S hS} {w : W' ⟶ E} (hw : IsFlat B S hS w.hom)
    {cX' : WX' ⟶ W'} {pX' : WX' ⟶ X'} {cY : WY ⟶ W'} {pY : WY ⟶ Y}
    {jX' : WX ⟶ WX'} {jY : WX ⟶ WY} {pX : WX ⟶ X}
    (hX'sq : IsPullback cX'.hom pX'.hom w.hom aY.hom)
    (hYsq : IsPullback cY.hom pY.hom w.hom bY.hom)
    (hjYsq : IsPullback jY.hom pX.hom pY.hom f.hom)
    (hjX'w : jX'.hom ≫ pX'.hom = pX.hom ≫ i.hom)
    (hsides : jY.hom ≫ cY.hom = jX'.hom ≫ cX'.hom) :
    IsPushout jX' jY cX' cY := by
  obtain ⟨A₂, pW, hpWS, hpWE, hkp, hcX'c, hcYc⟩ :=
    exists_thickeningAffineAtlas_of_isFlat B S hS A hqm hqmS hqmE haX' hbYc hback hw
      hX'sq hYsq hjYsq hjX'w hsides
  obtain ⟨E₂, a₂, b₂, hpush₂, qm₂, hqm₂, hqm₂S, hqm₂E, ha₂, hb₂⟩ :=
    isPushout_quotient_of_thickeningAffineAtlas B S hS A₂
  obtain ⟨ε, hε, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
    E₂.property.isSheaf qm₂ hqm₂ hqm₂S hqm₂E W'.property.isSheaf pW hkp.w
  obtain ⟨δ, hδ, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
    W'.property.isSheaf pW hkp hpWS hpWE E₂.property.isSheaf qm₂ hqm₂.w
  have hεδ : ε ≫ δ = 𝟙 E₂.1 :=
    hom_ext_of_etale_atlas B S hS E₂.property.isSheaf E₂.property.isSheaf qm₂ hqm₂S hqm₂E
      (by rw [← Category.assoc, hε, hδ, Category.comp_id])
  have hδε : δ ≫ ε = 𝟙 W'.1 :=
    hom_ext_of_etale_atlas B S hS W'.property.isSheaf W'.property.isSheaf pW hpWS hpWE
      (by rw [← Category.assoc, hδ, hε, Category.comp_id])
  let εsp : E₂ ⟶ W' := ObjectProperty.homMk ε
  let δsp : W' ⟶ E₂ := ObjectProperty.homMk δ
  have h1 : εsp ≫ δsp = 𝟙 E₂ := by
    apply ObjectProperty.hom_ext
    exact hεδ
  have h2 : δsp ≫ εsp = 𝟙 W' := by
    apply ObjectProperty.hom_ext
    exact hδε
  have ha₂' : a₂ ≫ εsp = cX' := by
    apply ObjectProperty.hom_ext
    refine hom_ext_of_etale_atlas B S hS WX'.property.isSheaf W'.property.isSheaf A₂.p'
      A₂.surjective_p' A₂.etale_p' ?_
    change A₂.p' ≫ a₂.hom ≫ ε = A₂.p' ≫ cX'.hom
    rw [← Category.assoc, ha₂, Category.assoc, hε, hcX'c]
  have hb₂' : b₂ ≫ εsp = cY := by
    apply ObjectProperty.hom_ext
    refine hom_ext_of_etale_atlas B S hS WY.property.isSheaf W'.property.isSheaf A₂.q
      A₂.surjective_q A₂.etale_q ?_
    change A₂.q ≫ b₂.hom ≫ ε = A₂.q ≫ cY.hom
    rw [← Category.assoc, hb₂, Category.assoc, hε, hcYc]
  exact hpush₂.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ⟨εsp, δsp, h1, h2⟩
    (by simp) (by simp) (by simpa using ha₂') (by simpa using hb₂')


/-! ### The counit of the gluing adjunction at a flat algebraic space -/

/-- **[Stacks Project, Tag 07W3], the counit assertion.**  Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`, let `f : X ⟶ Y` be an affine morphism and let `Y' = Y ⨿_X X'` be the
pushout.  If `W'` is **flat** over `Y'`, the adjunction morphism `G(F(W')) ⟶ W'` of
[Stacks Project, Tag 07VY] is an isomorphism.

The counit at `W'` is the morphism out of the pushout of the span of the triple `F(W')` induced
by the two projections of `W'`, so it suffices to know that `W'` *is* a pushout of that span,
compatibly with those projections: that is
`AlgebraicGeometry.Space.isPushout_of_isFlat_of_thickeningAffineAtlas`, the prescribed-atlas
construction of steps (a)–(e).  The only work here is matching the data: the chart of the
pushout produced by
`AlgebraicGeometry.Space.exists_pushout_chart_of_thickeningAffineAtlas` lives over a pushout of
the span which is transported to the canonical `pushout i f`, the three prescribed squares are
the canonical base changes of `W'` and the common restriction
`CategoryTheory.PushoutGluing.sourceMap_isPullback`, and the compatibility of the two sides of
the span over `W'` is
`CategoryTheory.PushoutGluing.baseChangeComparison_fst`. -/
theorem isIso_pushoutGluingAdjunction_counit_of_isFlat
    (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    ∀ Z : Over (Limits.pushout i f), IsFlat B S hS Z.hom.hom →
      IsIso ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.app Z) := by
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  intro Z hflatZ
  obtain ⟨A⟩ := hatlas i f hi hf
  obtain ⟨Epo, aY, bY, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  -- transport the chart of the pushout to the canonical pushout `Limits.pushout i f`
  let eP : Epo.1 ≅ (Limits.pushout i f).1 :=
    { hom := hpush.isoPushout.hom.hom
      inv := hpush.isoPushout.inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) hpush.isoPushout.hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) hpush.isoPushout.inv_hom_id }
  have hinl : aY.hom ≫ eP.hom = (Limits.pushout.inl i f).hom :=
    congrArg (fun φ => φ.hom) hpush.inl_isoPushout_hom
  have hinr : bY.hom ≫ eP.hom = (Limits.pushout.inr i f).hom :=
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
  have haX'' : IsPullback (yoneda.map A.a) A.p' (qm ≫ eP.hom)
      (Limits.pushout.inl i f).hom :=
    haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (hinl.trans (Category.id_comp _).symm)
  have hbY'' : IsPullback (yoneda.map A.b) A.q (qm ≫ eP.hom)
      (Limits.pushout.inr i f).hom :=
    hbYc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (hinr.trans (Category.id_comp _).symm)
  have hback' : i.hom ≫ (Limits.pushout.inl i f).hom =
      f.hom ≫ (Limits.pushout.inr i f).hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun φ => φ.hom) (Limits.pushout.condition (f := i) (g := f))
  -- the span of the triple `F(Z)`
  have pc : i ≫ Limits.pushout.inl i f = f ≫ Limits.pushout.inr i f := Limits.pushout.condition
  let T := (pushoutBaseChangeFunctor B S hS hatlas i f hi hf).obj Z
  have hX'sq : IsPullback (Limits.pullback.fst Z.hom (Limits.pushout.inl i f)).hom
      T.obj.right.hom.hom Z.hom.hom (Limits.pushout.inl i f).hom :=
    AlgebraicSpaces.isPullback_hom B S hS
      (IsPullback.of_hasPullback Z.hom (Limits.pushout.inl i f))
  have hYsq : IsPullback (Limits.pullback.fst Z.hom (Limits.pushout.inr i f)).hom
      T.obj.left.hom.hom Z.hom.hom (Limits.pushout.inr i f).hom :=
    AlgebraicSpaces.isPullback_hom B S hS
      (IsPullback.of_hasPullback Z.hom (Limits.pushout.inr i f))
  have hjYsq : IsPullback (CategoryTheory.PushoutGluing.sourceMap i f T).hom
      (Limits.pullback.snd T.obj.right.hom i).hom T.obj.left.hom.hom f.hom :=
    AlgebraicSpaces.isPullback_hom B S hS
      (CategoryTheory.PushoutGluing.sourceMap_isPullback i f T)
  have hjX'w : (Limits.pullback.fst T.obj.right.hom i).hom ≫ T.obj.right.hom.hom =
      (Limits.pullback.snd T.obj.right.hom i).hom ≫ i.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun φ => φ.hom)
        (Limits.pullback.condition (f := T.obj.right.hom) (g := i))
  have hsidesSp : CategoryTheory.PushoutGluing.sourceMap i f T ≫
      Limits.pullback.fst Z.hom (Limits.pushout.inr i f) =
      Limits.pullback.fst T.obj.right.hom i ≫
        Limits.pullback.fst Z.hom (Limits.pushout.inl i f) := by
    have : IsIso T.obj.hom := T.property
    have hid : (inv T.obj.hom).left ≫ T.obj.hom.left = 𝟙 _ :=
      congrArg CategoryTheory.Over.Hom.left (IsIso.inv_hom_id T.obj.hom)
    have hbc : T.obj.hom.left ≫ Limits.pullback.fst T.obj.right.hom i ≫
        Limits.pullback.fst Z.hom (Limits.pushout.inl i f) =
        Limits.pullback.fst T.obj.left.hom f ≫
          Limits.pullback.fst Z.hom (Limits.pushout.inr i f) :=
      CategoryTheory.PushoutGluing.baseChangeComparison_fst i f pc Z
    calc CategoryTheory.PushoutGluing.sourceMap i f T ≫
          Limits.pullback.fst Z.hom (Limits.pushout.inr i f)
        = ((inv T.obj.hom).left ≫ Limits.pullback.fst T.obj.left.hom f) ≫
            Limits.pullback.fst Z.hom (Limits.pushout.inr i f) := by rfl
      _ = (inv T.obj.hom).left ≫ Limits.pullback.fst T.obj.left.hom f ≫
            Limits.pullback.fst Z.hom (Limits.pushout.inr i f) := Category.assoc _ _ _
      _ = (inv T.obj.hom).left ≫ T.obj.hom.left ≫
            Limits.pullback.fst T.obj.right.hom i ≫
              Limits.pullback.fst Z.hom (Limits.pushout.inl i f) := by rw [hbc]
      _ = ((inv T.obj.hom).left ≫ T.obj.hom.left) ≫
            Limits.pullback.fst T.obj.right.hom i ≫
              Limits.pullback.fst Z.hom (Limits.pushout.inl i f) :=
            (Category.assoc _ _ _).symm
      _ = Limits.pullback.fst T.obj.right.hom i ≫
            Limits.pullback.fst Z.hom (Limits.pushout.inl i f) := by
            rw [hid, Category.id_comp]
  have hsides' : (CategoryTheory.PushoutGluing.sourceMap i f T).hom ≫
      (Limits.pullback.fst Z.hom (Limits.pushout.inr i f)).hom =
      (Limits.pullback.fst T.obj.right.hom i).hom ≫
        (Limits.pullback.fst Z.hom (Limits.pushout.inl i f)).hom :=
    congrArg (fun φ => φ.hom) hsidesSp
  have hW'push : IsPushout (Limits.pullback.fst T.obj.right.hom i)
      (CategoryTheory.PushoutGluing.sourceMap i f T)
      (Limits.pullback.fst Z.hom (Limits.pushout.inl i f))
      (Limits.pullback.fst Z.hom (Limits.pushout.inr i f)) :=
    isPushout_of_isFlat_of_thickeningAffineAtlas B S hS A hqm' hqmS' hqmE' haX'' hbY''
      hback' hflatZ hX'sq hYsq hjYsq hjX'w hsides'
  -- the counit is the comparison between two pushouts of that span
  let := pushoutGluingHasPushout B S hS hatlas i f hi hf T
  have hGpush : IsPushout (Limits.pullback.fst T.obj.right.hom i)
      (CategoryTheory.PushoutGluing.sourceMap i f T)
      (Limits.pushout.inl (Limits.pullback.fst T.obj.right.hom i)
        (CategoryTheory.PushoutGluing.sourceMap i f T))
      (Limits.pushout.inr (Limits.pullback.fst T.obj.right.hom i)
        (CategoryTheory.PushoutGluing.sourceMap i f T)) := IsPushout.of_hasPushout _ _
  have hinlc := CategoryTheory.PushoutGluing.inl_comp_gluingFromPair i f pc
    (pushoutGluingHasPushout B S hS hatlas i f hi hf) (𝟙 T)
  have hinrc := CategoryTheory.PushoutGluing.inr_comp_gluingFromPair i f pc
    (pushoutGluingHasPushout B S hS hatlas i f hi hf) (𝟙 T)
  have hεleft : ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.app Z).left =
      (hGpush.isoIsPushout _ _ hW'push).hom := by
    refine hGpush.hom_ext ?_ ?_
    · rw [hGpush.inl_isoIsPushout_hom _ _ hW'push]
      exact hinlc.trans (Category.id_comp _)
    · rw [hGpush.inr_isoIsPushout_hom _ _ hW'push]
      exact hinrc.trans (Category.id_comp _)
  have : IsIso ((Over.forget (Limits.pushout i f)).map
      ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.app Z)) := by
    change IsIso ((pushoutGluingAdjunction B S hS hatlas i f hi hf).counit.app Z).left
    rw [hεleft]
    exact ⟨⟨(hGpush.isoIsPushout _ _ hW'push).inv,
      (hGpush.isoIsPushout _ _ hW'push).hom_inv_id,
      (hGpush.isoIsPushout _ _ hW'push).inv_hom_id⟩⟩
  exact isIso_of_reflects_iso _ (Over.forget (Limits.pushout i f))

end AlgebraicGeometry.Space

end
