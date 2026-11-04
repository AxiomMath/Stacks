module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineAtlasExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineGluingDescent
import StacksFrontier.AlgebraicGeometry.Spaces.Immersions

/-!
# The prescribed cube of étale charts over a triple, and the five clauses of Tag 07W3

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism,
`Y' = Y ⨿_X X'` their pushout, and `(V, U', φ)` a triple over the span with pushout
`G = V ⨿_U U'` and structure morphism `G ⟶ Y'`.  The proof of [Stacks Project, Tag 07W0]
builds two cubes of étale charts, diagrams 81.6.5.1 ([Stacks Project, Tag 07W1]) and 81.6.5.2
([Stacks Project, Tag 07W2]), the second one *prescribed* by the first: its chart `V₁` of `V`
is a chart of `Y₁ ×_Y V`, so that the pushout of charts `G₁ = V₁ ⨿_{U₁} U₁'` carries a morphism
to the pushout of charts `Y₁' = Y₁ ⨿_{X₁} X₁'`.  The proof of [Stacks Project, Tag 07W3]
reduces its clauses (1)–(5) to [Stacks Project, Tag 07RX] along these charts.

This module builds the two prescribed cubes, in the form of an
`AlgebraicGeometry.Space.ThickeningAffineGluingChart` for `G ⟶ Y'`, `V ⟶ Y` and `U' ⟶ X'`,
from the chart form of the essential surjectivity half of [Stacks Project, Tag 05ZS]:
surjective étale scheme charts lift across thickenings of algebraic spaces
(`AlgebraicGeometry.Space.HasEtaleChartLifts`).  The clauses (1)–(5) of Tag 07W3 for the gluing
functor of [Stacks Project, Tag 07VY] follow.

## Main definitions

* `AlgebraicGeometry.Space.HasEtaleChartLifts`: every surjective étale scheme chart of `X` lifts
  across every thickening `X ⟶ X'` to a surjective étale scheme chart of `X'`.

## Main results

* `AlgebraicGeometry.Space.nonempty_thickeningAffineGluingChart_of_chartLift`: the prescribed
  cubes, as a `ThickeningAffineGluingChart`.
* `AlgebraicGeometry.Space.nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj`: the
  same for the value of the gluing functor of Tag 07VY on a triple.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_pushoutGluingFunctor_obj_iff`,
  `isFlat_pushoutGluingFunctor_obj_iff`,
  `isFlat_and_isLocallyOfFinitePresentation_pushoutGluingFunctor_obj_iff`,
  `isSmooth_pushoutGluingFunctor_obj_iff` and `isEtale_pushoutGluingFunctor_obj_iff`: clauses
  (1)–(5) of Tag 07W3, given the chart lift.

## Implementation notes

The chart `U₁'` of `U'` must restrict both to `U₁` along `U ⟶ U'` and to the chart `X₁` of `X`
along `X₁ ⟶ X₁'`.  It is obtained by lifting the chart `U₁ ⟶ Z` of
`Z = U ×_{U'} (U' ×_{X'} X₁')` across the thickening `Z ⟶ U' ×_{X'} X₁'`, which is a base change
of `U ⟶ U'`.  That `U₁ ⟶ Z` is a surjective étale chart comes from `Z = (Y₁ ×_Y V) ×_V U`,
along which it is the base change of the chosen chart `V₁ ⟶ Y₁ ×_Y V`.

## References

* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Charts lift across thickenings.**  Every surjective étale scheme chart `p : U ⟶ X` of an
algebraic space lifts across every thickening `i : X ⟶ X'` of algebraic spaces over `S` to a
surjective étale scheme chart `p' : U' ⟶ X'` with `U = X ×_{X'} U'`, the morphism of charts
`U ⟶ U'` being a thickening of schemes.  This is the chart form of the essential surjectivity
half of [Stacks Project, Tag 05ZS]. -/
abbrev HasEtaleChartLifts : Prop :=
  ∀ {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X'), IsThickeningHom B S hS i →
    ∀ {U : BigFppfOver B S hS} (p : yoneda.obj U ⟶ X.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) p →
      ∃ (U' : BigFppfOver B S hS) (p' : yoneda.obj U' ⟶ X'.1) (k : U ⟶ U'),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) p' ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) p' ∧
        IsPullback (yoneda.map k) p p' i.hom ∧
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)

/-- **The prescribed cubes of étale charts of the proof of [Stacks Project, Tag 07W0].**  Let
`i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism and
`E = Y ⨿_X X'` a pushout.  Let `U = U' ×_{X'} X = V ×_Y X` be the restriction of a triple
`(V, U', φ)`, let `G = V ⨿_U U'` be a pushout and `g : G ⟶ E` the morphism induced by
`V ⟶ Y` and `U' ⟶ X'`.  If surjective étale scheme charts lift across thickenings, then `g`,
`V ⟶ Y` and `U' ⟶ X'` admit a `ThickeningAffineGluingChart`: the cubes 81.6.5.1 and 81.6.5.2,
the second prescribed by the first so that the pushout of the charts of the triple maps to the
pushout of the charts of the span.

Besides the fields of the chart, the four lateral squares over the pushout corners are
cartesian: `V₁ = G₁ ×_G V`, `U₁' = G₁ ×_G U'`, `Y₁ = Y₁' ×_{E} Y` and `X₁' = Y₁' ×_E X'`. -/
theorem exists_thickeningAffineGluingChart_of_chartLift (hlift : HasEtaleChartLifts B S hS)
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {E : AlgebraicSpaces B S hS} {aY : X' ⟶ E} {bY : Y ⟶ E} (hE : IsPushout i f aY bY)
    {U U' V : AlgebraicSpaces B S hS} {jU : U ⟶ U'} {σ : U ⟶ V} {pU : U ⟶ X}
    {u' : U' ⟶ X'} {v : V ⟶ Y} (hU' : IsPullback jU pU u' i) (hV : IsPullback σ pU v f)
    {G : AlgebraicSpaces B S hS} {aG : U' ⟶ G} {bG : V ⟶ G} (hG : IsPushout jU σ aG bG)
    {g : G ⟶ E} (haG : aG ≫ g = u' ≫ aY) (hbG : bG ≫ g = v ≫ bY) :
    ∃ D : ThickeningAffineGluingChart B S hS g.hom v.hom u'.hom,
      IsPullback (yoneda.map D.inV) D.sqY.chartSrc D.sqGlued.chartSrc bG.hom ∧
      IsPullback (yoneda.map D.inU') D.sqX'.chartSrc D.sqGlued.chartSrc aG.hom ∧
      IsPullback (yoneda.map D.inY) D.sqY.chartTgt D.sqGlued.chartTgt bY.hom ∧
      IsPullback (yoneda.map D.inX') D.sqX'.chartTgt D.sqGlued.chartTgt aY.hom := by
  let F := BigFppfOver.toScheme B S hS
  have htr : ∀ {P₀ Q₀ R₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {E₁ E₂ : AlgebraicSpaces B S hS}
      (eI : E₁ ≅ E₂) {x : P₀ ⟶ Q₀} {y : P₀ ⟶ R₀} {qq : Q₀ ⟶ E₁.1} {z : R₀ ⟶ E₁.1}
      {z' : R₀ ⟶ E₂.1}, IsPullback x y qq z → z ≫ eI.hom.hom = z' →
        IsPullback x y (qq ≫ eI.hom.hom) z' := fun eI _ _ _ _ _ h hz ↦
    h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((ObjectProperty.ι _).mapIso eI)
      (by simp) (by simp) (by simp) (by simpa using hz)
  let Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ⊓
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
  have hbc : Q.IsStableUnderBaseChange := by
    have h : ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange],
        (MorphismProperty.presheaf (MorphismProperty.inverseImage P
          (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      fun P _ => MorphismProperty.relative_isStableUnderBaseChange _
    exact @MorphismProperty.IsStableUnderBaseChange.inf _ _ _ _ (h _) (h _)
  have hisoS : ∀ {P Q : AlgebraicSpaces B S hS} (e : P ≅ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.hom.hom := by
    intro P Q e
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda
      ((ObjectProperty.ι _).mapIso e).hom, ?_⟩
    intro A C g fst snd sq
    have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    change AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map snd)
    infer_instance
  have hisoE : ∀ {P Q : AlgebraicSpaces B S hS} (e : P ≅ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.hom.hom := fun e =>
    presheaf_etale_of_iso B S hS ((ObjectProperty.ι _).mapIso e)
  -- the cube 81.6.5.1: the atlas of the span and the chart of `E`
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_chartLift B S hS i f hi hf (hlift i hi)
  obtain ⟨E₀, aY₀, bY₀, qm₀, hpush₀, -, -, hqm₀E, haX'₀, hbY₀⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B S hS A hi
  let e : E₀ ≅ E := hpush₀.isoIsPushout _ _ hE
  have hea : aY₀.hom ≫ e.hom.hom = aY.hom :=
    congrArg (fun φ => φ.hom) (hpush₀.inl_isoIsPushout_hom _ _ hE)
  have heb : bY₀.hom ≫ e.hom.hom = bY.hom :=
    congrArg (fun φ => φ.hom) (hpush₀.inr_isoIsPushout_hom _ _ hE)
  have hab : A.k ≫ A.a = A.g ≫ A.b := F.map_injective (by
    simpa only [Functor.map_comp] using A.isPushout_chart.w)
  -- the chart `V₁` of `A.V ×_Y V`
  have hσ := AlgebraicSpaces.isPullback_hom B S hS hV
  have hU'h := AlgebraicSpaces.isPullback_hom B S hS hU'
  have hW := IsPullback.of_hasPullback A.q v.hom
  obtain ⟨V₁, c, hcS, hcE⟩ := (isAlgebraicSpace_pullback B S hS A.q v.hom
    (isAlgebraicSpace_yoneda B S hS A.V) V.property Y.property).exists_atlas
  obtain ⟨q₁, hq₁def⟩ : ∃ q₁, q₁ = c ≫ pullback.snd A.q v.hom := ⟨_, rfl⟩
  have hq₁ : Q q₁ := by
    rw [hq₁def]
    exact MorphismProperty.comp_mem _ _ _ ⟨hcS, hcE⟩
      (hbc.of_isPullback hW ⟨A.surjective_q, A.etale_q⟩)
  let vY : V₁ ⟶ A.V := yoneda.preimage (c ≫ pullback.fst A.q v.hom)
  have hvY : yoneda.map vY = c ≫ pullback.fst A.q v.hom := yoneda.map_preimage _
  have hvYq : yoneda.map vY ≫ A.q = q₁ ≫ v.hom := by
    rw [hvY, hq₁def, Category.assoc, Category.assoc, hW.w]
  -- the chart `U₁ = V₁ ×_{A.V} A.U` of `U`
  have hU₁ := IsPullback.of_hasPullback vY A.g
  have hU₁y := hU₁.map yoneda
  have hU₁F := hU₁.map F
  have : _root_.AlgebraicGeometry.IsAffineHom (F.map (pullback.fst vY A.g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.IsAffineHom) hU₁F.flip A.isAffineHom_g
  have hcomm₁ : (yoneda.map (pullback.fst vY A.g) ≫ q₁) ≫ v.hom =
      (yoneda.map (pullback.snd vY A.g) ≫ A.p) ≫ f.hom := by
    rw [Category.assoc, Category.assoc, ← hvYq, A.isPullback_affine.w, ← Category.assoc,
      ← Category.assoc, hU₁y.w]
  obtain ⟨p₁, hp₁σ, hp₁X⟩ : ∃ p₁ : yoneda.obj (pullback vY A.g) ⟶ U.1,
      p₁ ≫ σ.hom = yoneda.map (pullback.fst vY A.g) ≫ q₁ ∧
        p₁ ≫ pU.hom = yoneda.map (pullback.snd vY A.g) ≫ A.p :=
    ⟨hσ.lift _ _ hcomm₁, hσ.lift_fst _ _ _, hσ.lift_snd _ _ _⟩
  have hp₁ : IsPullback p₁ (yoneda.map (pullback.fst vY A.g)) σ.hom q₁ := by
    refine IsPullback.of_right ?_ hp₁σ hσ.flip
    rw [hp₁X, ← hvYq]
    exact hU₁y.flip.paste_horiz A.isPullback_affine
  have hp₁Q : Q p₁ := hbc.of_isPullback hp₁.flip hq₁
  -- the thickening `Z ⟶ Z'`, with `Z' = U' ×_{X'} A.U'` and `Z = U ×_{U'} Z'`
  let Z' : AlgebraicSpaces B S hS := ⟨pullback u'.hom A.p', isAlgebraicSpace_pullback B S hS
    u'.hom A.p' U'.property (isAlgebraicSpace_yoneda B S hS A.U') X'.property⟩
  let pr : Z' ⟶ U' := ObjectProperty.homMk (pullback.fst u'.hom A.p')
  let zt : AlgebraicSpaces.fiberProduct B S hS jU pr ⟶ Z' :=
    ObjectProperty.homMk (pullback.snd jU.hom pr.hom)
  have hjU : IsThickeningHom B S hS jU := isThickeningHom_of_isPullback B S hS hU'.flip hi
  have hzt : IsThickeningHom B S hS zt := isThickeningHom_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS jU pr) hjU
  have S1 := IsPullback.of_hasPullback u'.hom A.p'
  have S2 := IsPullback.of_hasPullback jU.hom (pullback.fst u'.hom A.p')
  obtain ⟨zA, hZ1, hZA⟩ := exists_isPullback_pullback_of_isPullback hU'h A.isPullback_thickening
  -- `Z = (A.V ×_Y V) ×_V U`, and the chart `χ : U₁ ⟶ Z`
  have hζw : (zA ≫ yoneda.map A.g) ≫ A.q =
      (pullback.fst jU.hom (pullback.fst u'.hom A.p') ≫ σ.hom) ≫ v.hom := by
    rw [Category.assoc, ← A.isPullback_affine.w, ← Category.assoc, hZA.w, Category.assoc,
      Category.assoc, hσ.w]
  obtain ⟨ζ, hζ₁, hζ₂⟩ : ∃ ζ : pullback jU.hom (pullback.fst u'.hom A.p') ⟶ pullback A.q v.hom,
      ζ ≫ pullback.fst A.q v.hom = zA ≫ yoneda.map A.g ∧
        ζ ≫ pullback.snd A.q v.hom = pullback.fst jU.hom (pullback.fst u'.hom A.p') ≫ σ.hom :=
    ⟨pullback.lift _ _ hζw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hZ3 : IsPullback ζ (pullback.fst jU.hom (pullback.fst u'.hom A.p'))
      (pullback.snd A.q v.hom) σ.hom := by
    refine IsPullback.of_right ?_ hζ₂ hW
    rw [hζ₁, hσ.w]
    exact hZA.paste_horiz A.isPullback_affine.flip
  have hχw : (yoneda.map (pullback.fst vY A.g) ≫ c) ≫ pullback.snd A.q v.hom = p₁ ≫ σ.hom := by
    rw [Category.assoc, hp₁σ, hq₁def]
  obtain ⟨χ, hχζ, hχfst⟩ : ∃ χ : yoneda.obj (pullback vY A.g) ⟶
      pullback jU.hom (pullback.fst u'.hom A.p'),
      χ ≫ ζ = yoneda.map (pullback.fst vY A.g) ≫ c ∧
        χ ≫ pullback.fst jU.hom (pullback.fst u'.hom A.p') = p₁ :=
    ⟨hZ3.lift _ _ hχw, hZ3.lift_fst _ _ _, hZ3.lift_snd _ _ _⟩
  have hχ : IsPullback (yoneda.map (pullback.fst vY A.g)) χ c ζ :=
    IsPullback.of_bot (by rw [hχfst, ← hq₁def]; exact hp₁.flip) hχζ.symm hZ3
  have hχQ : Q χ := hbc.of_isPullback hχ ⟨hcS, hcE⟩
  have hχA : χ ≫ zA = yoneda.map (pullback.snd vY A.g) := by
    refine A.isPullback_affine.hom_ext ?_ ?_
    · rw [Category.assoc, hZA.w, ← Category.assoc, hχfst, hp₁X]
    · rw [Category.assoc, ← hζ₁, ← Category.assoc, hχζ, Category.assoc, ← hvY,
        ← Functor.map_comp, ← Functor.map_comp, hU₁.w]
  -- the lift `U₁'` of the chart `χ` across the thickening `Z ⟶ Z'`
  obtain ⟨U₁', p₁', k₁, hp₁'S, hp₁'E, hL, hk₁⟩ := hlift zt hzt χ hχQ.1 hχQ.2
  let h' : U₁' ⟶ A.U' := yoneda.preimage (p₁' ≫ pullback.snd u'.hom A.p')
  have hh' : yoneda.map h' = p₁' ≫ pullback.snd u'.hom A.p' := yoneda.map_preimage _
  have hIy : IsPullback (yoneda.map k₁) (yoneda.map (pullback.snd vY A.g)) (yoneda.map h')
      (yoneda.map A.k) := by
    rw [← hχA, hh']
    exact hL.paste_vert hZ1
  have hkh : k₁ ≫ h' = pullback.snd vY A.g ≫ A.k :=
    yoneda.map_injective (by simpa only [Functor.map_comp] using hIy.w)
  have hI := (IsPullback.of_map yoneda hkh hIy).map F
  have hthick : IsPullback (yoneda.map k₁) p₁ (p₁' ≫ pullback.fst u'.hom A.p') jU.hom := by
    rw [← hχfst]
    exact hL.paste_vert S2.flip
  have hcQ : Q (p₁' ≫ pullback.fst u'.hom A.p') :=
    MorphismProperty.comp_mem _ _ _ ⟨hp₁'S, hp₁'E⟩
      (hbc.of_isPullback S1.flip ⟨A.surjective_p', A.etale_p'⟩)
  -- the cube 81.6.5.2 over the span of the triple
  obtain ⟨G₁, a₂, b₂, E₂, aY₂, bY₂, qm₂, hG₁, hpush₂, hqm₂S, hqm₂E, ha₂, hb₂, -⟩ :=
    exists_chartCube_of_charts B S hS jU σ hjU q₁ hq₁.1 hq₁.2 p₁ (pullback.fst vY A.g) hp₁
      (p₁' ≫ pullback.fst u'.hom A.p') k₁ hcQ.1 hcQ.2 hthick hk₁
  let e₂ : E₂ ≅ G := hpush₂.isoIsPushout _ _ hG
  have he₂a : aY₂.hom ≫ e₂.hom.hom = aG.hom :=
    congrArg (fun φ => φ.hom) (hpush₂.inl_isoIsPushout_hom _ _ hG)
  have he₂b : bY₂.hom ≫ e₂.hom.hom = bG.hom :=
    congrArg (fun φ => φ.hom) (hpush₂.inr_isoIsPushout_hom _ _ hG)
  -- the morphism of pushouts of charts `G₁ ⟶ A.P`
  obtain ⟨m, hma, hmb⟩ := exists_desc_site B S hS hG₁ (h' ≫ A.a) (vY ≫ A.b) (by
    rw [← Category.assoc, hkh, ← Category.assoc, hU₁.w, Category.assoc, Category.assoc, hab])
  have hPSp := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS k₁
    (pullback.fst vY A.g) a₂ b₂ hk₁ hG₁
  have hX'c : yoneda.map h' ≫ A.p' = (p₁' ≫ pullback.fst u'.hom A.p') ≫ u'.hom := by
    rw [hh', Category.assoc, ← S1.w, Category.assoc]
  have hGa : aG.hom ≫ g.hom = u'.hom ≫ aY.hom := congrArg (fun φ => φ.hom) haG
  have hGb : bG.hom ≫ g.hom = v.hom ≫ bY.hom := congrArg (fun φ => φ.hom) hbG
  have hmcomm : yoneda.map m ≫ qm₀ ≫ e.hom.hom = (qm₂ ≫ e₂.hom.hom) ≫ g.hom := by
    have key : (ObjectProperty.homMk (yoneda.map m ≫ qm₀ ≫ e.hom.hom) :
        representedAlgebraicSpace B S hS G₁ ⟶ E) =
        ObjectProperty.homMk ((qm₂ ≫ e₂.hom.hom) ≫ g.hom) := by
      refine hPSp.hom_ext (ObjectProperty.hom_ext _ ?_) (ObjectProperty.hom_ext _ ?_)
      · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        rw [← Functor.map_comp_assoc, hma, Functor.map_comp]
        simp only [Category.assoc, reassoc_of% haX'₀.w, hea, reassoc_of% hX'c,
          reassoc_of% ha₂.w, reassoc_of% he₂a, hGa]
      · simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
        rw [← Functor.map_comp_assoc, hmb, Functor.map_comp]
        simp only [Category.assoc, reassoc_of% hbY₀.w, heb, reassoc_of% hvYq,
          reassoc_of% hb₂.w, reassoc_of% he₂b, hGb]
    exact congrArg (fun φ => φ.hom) key
  exact ⟨
    { sqGlued :=
        { src := G₁, tgt := A.P, hom := m, chartSrc := qm₂ ≫ e₂.hom.hom
          chartTgt := qm₀ ≫ e.hom.hom
          etale_chartSrc := MorphismProperty.comp_mem _ _ _ hqm₂E (hisoE e₂)
          surjective_chartSrc := MorphismProperty.comp_mem _ _ _ hqm₂S (hisoS e₂)
          etale_chartTgt := MorphismProperty.comp_mem _ _ _ hqm₀E (hisoE e)
          comm := hmcomm }
      sqY :=
        { src := V₁, tgt := A.V, hom := vY, chartSrc := q₁, chartTgt := A.q
          etale_chartSrc := hq₁.2
          surjective_chartSrc := hq₁.1
          etale_chartTgt := A.etale_q
          comm := hvYq }
      sqX' :=
        { src := U₁', tgt := A.U', hom := h', chartSrc := p₁' ≫ pullback.fst u'.hom A.p'
          chartTgt := A.p'
          etale_chartSrc := hcQ.2
          surjective_chartSrc := hcQ.1
          etale_chartTgt := A.etale_p'
          comm := hX'c }
      chartX := A.U
      chartU := pullback vY A.g
      i := A.k
      f := A.g
      inX' := A.a
      inY := A.b
      iT := k₁
      fT := pullback.fst vY A.g
      inU' := a₂
      inV := b₂
      toX := pullback.snd vY A.g
      isThickening_i := A.isThickening_k
      isAffineHom_f := A.isAffineHom_g
      isPushout_base := A.isPushout_chart
      isPushout_glued := hG₁
      isPullback_i := hI
      isPullback_f := hU₁F
      inU'_comp_hom := hma
      inV_comp_hom := hmb },
    htr e₂ hb₂ he₂b, htr e₂ ha₂ he₂a, htr e hbY₀ heb, htr e haX'₀ hea⟩

/-- The prescribed cubes of étale charts of the proof of [Stacks Project, Tag 07W0], as a
`ThickeningAffineGluingChart`; see `exists_thickeningAffineGluingChart_of_chartLift`. -/
theorem nonempty_thickeningAffineGluingChart_of_chartLift (hlift : HasEtaleChartLifts B S hS)
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    {E : AlgebraicSpaces B S hS} {aY : X' ⟶ E} {bY : Y ⟶ E} (hE : IsPushout i f aY bY)
    {U U' V : AlgebraicSpaces B S hS} {jU : U ⟶ U'} {σ : U ⟶ V} {pU : U ⟶ X}
    {u' : U' ⟶ X'} {v : V ⟶ Y} (hU' : IsPullback jU pU u' i) (hV : IsPullback σ pU v f)
    {G : AlgebraicSpaces B S hS} {aG : U' ⟶ G} {bG : V ⟶ G} (hG : IsPushout jU σ aG bG)
    {g : G ⟶ E} (haG : aG ≫ g = u' ≫ aY) (hbG : bG ≫ g = v ≫ bY) :
    Nonempty (ThickeningAffineGluingChart B S hS g.hom v.hom u'.hom) :=
  let ⟨D, _⟩ := exists_thickeningAffineGluingChart_of_chartLift B S hS hlift hi hf hE hU' hV hG
    haG hbG
  ⟨D⟩

/-! ### The gluing functor of Tag 07VY -/

section gluing

variable {B S hS} (hlift : HasEtaleChartLifts B S hS)
  (hatlas : HasThickeningAffineAtlases B S hS) {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X')
  (f : X ⟶ Y) (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
  (T : pushoutGluingData B S hS i f)

include hlift

/-- The cubes 81.6.5.1 and 81.6.5.2 for the value `G(V, U', φ) = V ⨿_U U'` of the gluing functor
of [Stacks Project, Tag 07VY] on a triple, with its structure morphism to `Y' = Y ⨿_X X'`. -/
theorem nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    Nonempty (ThickeningAffineGluingChart B S hS
      ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom
      T.obj.left.hom.hom T.obj.right.hom.hom) := by
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  obtain ⟨v, u', hpo, hv, hu'⟩ :=
    pushoutGluingFunctor_obj_isPushout B S hS hatlas i f hi hf T
  exact nonempty_thickeningAffineGluingChart_of_chartLift B S hS hlift hi hf
    (IsPushout.of_hasPushout i f) (IsPullback.of_hasPullback T.obj.right.hom i)
    (CategoryTheory.PushoutGluing.sourceMap_isPullback i f T) hpo.flip hu' hv

/-- **Clause (1) of [Stacks Project, Tag 07W3], given that charts lift across thickenings.**
The glued algebraic space `G(V, U', φ) ⟶ Y'` is locally of finite type if and only if both
`V ⟶ Y` and `U' ⟶ X'` are. -/
theorem isLocallyOfFiniteType_pushoutGluingFunctor_obj_iff :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    IsLocallyOfFiniteType B S hS
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
      IsLocallyOfFiniteType B S hS T.obj.left.hom.hom ∧
        IsLocallyOfFiniteType B S hS T.obj.right.hom.hom :=
  (nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj hlift hatlas i f hi hf
    T).some.isLocallyOfFiniteType_iff

/-- **Clause (2) of [Stacks Project, Tag 07W3], given that charts lift across thickenings.**
The glued algebraic space `G(V, U', φ) ⟶ Y'` is flat if and only if both `V ⟶ Y` and
`U' ⟶ X'` are. -/
theorem isFlat_pushoutGluingFunctor_obj_iff :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    IsFlat B S hS
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
      IsFlat B S hS T.obj.left.hom.hom ∧
        IsFlat B S hS T.obj.right.hom.hom :=
  (nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj hlift hatlas i f hi hf
    T).some.isFlat_iff

/-- **Clause (4) of [Stacks Project, Tag 07W3], given that charts lift across thickenings.**
The glued algebraic space `G(V, U', φ) ⟶ Y'` is smooth if and only if both `V ⟶ Y` and
`U' ⟶ X'` are. -/
theorem isSmooth_pushoutGluingFunctor_obj_iff :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    IsSmooth B S hS
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
      IsSmooth B S hS T.obj.left.hom.hom ∧
        IsSmooth B S hS T.obj.right.hom.hom :=
  (nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj hlift hatlas i f hi hf
    T).some.isSmooth_iff

/-- **Clause (3) of [Stacks Project, Tag 07W3], given that charts lift across thickenings.**
The glued algebraic space `G(V, U', φ) ⟶ Y'` is flat and locally of finite presentation if and
only if both `V ⟶ Y` and `U' ⟶ X'` are. -/
theorem isFlat_and_isLocallyOfFinitePresentation_pushoutGluingFunctor_obj_iff :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    (IsFlat B S hS
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ∧
        IsLocallyOfFinitePresentation B S hS
          ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom) ↔
      ((IsFlat B S hS T.obj.left.hom.hom ∧
          IsLocallyOfFinitePresentation B S hS T.obj.left.hom.hom) ∧
        (IsFlat B S hS T.obj.right.hom.hom ∧
          IsLocallyOfFinitePresentation B S hS T.obj.right.hom.hom)) :=
  (nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj hlift hatlas i f hi hf
    T).some.isFlat_and_isLocallyOfFinitePresentation_iff

/-- **Clause (5) of [Stacks Project, Tag 07W3], given that charts lift across thickenings.**
The glued algebraic space `G(V, U', φ) ⟶ Y'` is étale if and only if both `V ⟶ Y` and
`U' ⟶ X'` are. -/
theorem isEtale_pushoutGluingFunctor_obj_iff :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    IsEtale B S hS
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom.hom ↔
      IsEtale B S hS T.obj.left.hom.hom ∧
        IsEtale B S hS T.obj.right.hom.hom :=
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  (nonempty_thickeningAffineGluingChart_pushoutGluingFunctor_obj hlift hatlas i f hi hf
    T).some.isEtale_iff
    ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left.property (pushout i f).property
    T.obj.left.left.property Y.property T.obj.right.left.property X'.property

end gluing

end AlgebraicGeometry.Space

end
