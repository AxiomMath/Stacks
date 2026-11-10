module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutPrescribed
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CartesianSquareDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineGluingDescent
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The cartesian squares of Tag 07W0 along a chart presentation

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, `f : X ⟶ Y` an affine morphism
and `Y' = Y ⨿_X X'`.  [Stacks Project, Tag 07W0] says that the composite `F ∘ G` of the gluing
functor `G` of [Stacks Project, Tag 07VY] and the base-change functor `F` is isomorphic to the
identity: a triple `(V, U', φ)` is recovered from its glued algebraic space `V' = V ⨿_U U'` by
base change, `V = V' ×_{Y'} Y` and `U' = V' ×_{Y'} X'`.

The source reduces this along the cubes of étale charts of
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartFiniteOrder` to the
last
assertion of [Stacks Project, Tag 07RV] for schemes,
`AlgebraicGeometry.ThickeningAffinePushoutSituation.isPullback_of_isPushout_of_isPullback`; the
cartesian square of charts descends along the surjective étale chart of `V'` by
[Stacks Project, Tag 07VZ],
`AlgebraicGeometry.Space.isPullback_right_of_isPullback_of_surjective_etale`.

## Main results

* `AlgebraicGeometry.Space.ThickeningAffineGluingChart.isPullback_v` and
  `AlgebraicGeometry.Space.ThickeningAffineGluingChart.isPullback_u'`: the descent of the two
  cartesian squares of Tag 07RV along a chart presentation.

## References

* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07VZ](https://stacks.math.columbia.edu/tag/07VZ)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ThickeningAffineGluingChart

variable {G E V Y U' X' : AlgebraicSpaces B S hS} {g : G ⟶ E} {v : V ⟶ Y} {u' : U' ⟶ X'}
  (D : ThickeningAffineGluingChart B S hS g.hom v.hom u'.hom)

/-- A square of the big fppf site is cartesian as soon as its square of schemes is, and then so
is its square of representable presheaves. -/
private theorem isPullback_yoneda_of_isPullback_toScheme {P Q R W : BigFppfOver B S hS}
    {a : P ⟶ Q} {b : P ⟶ R} {c : Q ⟶ W} {e : R ⟶ W}
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map e)) :
    IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map e) := by
  have _ : ReflectsLimit (cospan c e) (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact (IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) h).map yoneda

/-- The last assertion of [Stacks Project, Tag 07RV] on the charts of a presentation: the chart
`V₁` of `V` is `G₁ ×_{Y₁'} Y₁` and the chart `U₁'` of `U'` is `G₁ ×_{Y₁'} X₁'`. -/
theorem isPullback_charts :
    IsPullback (yoneda.map D.inV) (yoneda.map D.sqY.hom) (yoneda.map D.sqGlued.hom)
        (yoneda.map D.inY) ∧
      IsPullback (yoneda.map D.inU') (yoneda.map D.sqX'.hom) (yoneda.map D.sqGlued.hom)
        (yoneda.map D.inX') := by
  have := D.isAffineHom_f
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map D.fT) :=
    MorphismProperty.of_isPullback D.isPullback_f.flip inferInstance
  obtain ⟨h₁, h₂⟩ := ThickeningAffinePushoutSituation.isPullback_of_isPushout_of_isPullback
    D.isPushout_base D.isThickening_i D.isPushout_glued D.isPullback_i D.isPullback_f
    D.map_inU'_comp_hom D.map_inV_comp_hom
  exact ⟨isPullback_yoneda_of_isPullback_toScheme h₁, isPullback_yoneda_of_isPullback_toScheme h₂⟩

/-- Descent of a cartesian square along the surjective étale chart `sqG.chartSrc`, given the
cartesian square of charts and the two base-change squares of charts. -/
private theorem isPullback_of_isPullback_charts (sqG : EtaleChartSquare B S hS g.hom)
    (sq : EtaleChartSquare B S hS v.hom) {inS : sq.src ⟶ sqG.src} {inT : sq.tgt ⟶ sqG.tgt}
    (hc : IsPullback (yoneda.map inS) (yoneda.map sq.hom) (yoneda.map sqG.hom) (yoneda.map inT))
    {bG : V ⟶ G} {bY : Y ⟶ E} (hw : bG ≫ g = v ≫ bY)
    (hV : IsPullback (yoneda.map inS) sq.chartSrc sqG.chartSrc bG.hom)
    (hY : IsPullback (yoneda.map inT) sq.chartTgt sqG.chartTgt bY.hom) :
    IsPullback v.hom bG.hom bY.hom g.hom := by
  have houter := (hc.paste_vert hY).flip
  rw [sq.comm, sqG.comm] at houter
  exact isPullback_right_of_isPullback_of_surjective_etale B S hS
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) V.property
    G.property Y.property E.property (congrArg (fun φ => φ.hom) hw).symm hV.flip houter
    (isSurjective_of_presheafSurjective B S hS _ sqG.surjective_chartSrc)
    (isEtale_of_presheaf_etale B S hS sqG.etale_chartSrc)

/-- **The `V`-half of [Stacks Project, Tag 07W0] along a chart presentation.**  If the chart of
`V` is the base change of the chart of `G` along `bG : V ⟶ G`, and the chart of `Y` is the base
change of the chart of `E` along `bY : Y ⟶ E`, then `V = G ×_E Y`. -/
theorem isPullback_v {bG : V ⟶ G} {bY : Y ⟶ E} (hw : bG ≫ g = v ≫ bY)
    (hV : IsPullback (yoneda.map D.inV) D.sqY.chartSrc D.sqGlued.chartSrc bG.hom)
    (hY : IsPullback (yoneda.map D.inY) D.sqY.chartTgt D.sqGlued.chartTgt bY.hom) :
    IsPullback v.hom bG.hom bY.hom g.hom :=
  isPullback_of_isPullback_charts D.sqGlued D.sqY D.isPullback_charts.1 hw hV hY

/-- **The `U'`-half of [Stacks Project, Tag 07W0] along a chart presentation.**  If the chart of
`U'` is the base change of the chart of `G` along `aG : U' ⟶ G`, and the chart of `X'` is the
base change of the chart of `E` along `aY : X' ⟶ E`, then `U' = G ×_E X'`. -/
theorem isPullback_u' {aG : U' ⟶ G} {aY : X' ⟶ E} (hw : aG ≫ g = u' ≫ aY)
    (hU : IsPullback (yoneda.map D.inU') D.sqX'.chartSrc D.sqGlued.chartSrc aG.hom)
    (hX : IsPullback (yoneda.map D.inX') D.sqX'.chartTgt D.sqGlued.chartTgt aY.hom) :
    IsPullback u'.hom aG.hom aY.hom g.hom :=
  isPullback_of_isPullback_charts D.sqGlued D.sqX' D.isPullback_charts.2 hw hU hX

end ThickeningAffineGluingChart

end AlgebraicGeometry.Space

end
