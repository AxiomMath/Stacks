module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardChartRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueSectionsChart

/-!
# The rings of functions on base-changed charts over a cartesian square of spaces

Let
```
P --p--> Q
|q       |r
v        v
R --s--> T
```
be a cartesian square of algebraic spaces with `q` and `r` representable, and let `d` be a
commuting square of étale scheme charts over `s`, from a chart `W` of `R` to a chart `W'` of `T`.
Then the base change `W ×_R P` of `W` along `q` maps to the base change `W' ×_T Q` of `W'` along
`r` (`AlgebraicGeometry.Space.cartesianChartDiagram`), and the four schemes form a cartesian
square, since `W ×_R P = W ×_T Q = W ×_{W'} (W' ×_T Q)`. When the three charts `W`, `W'` and
`W' ×_T Q` are affine the four rings of global functions therefore form a pushout
(`AlgebraicGeometry.Space.isPushout_cartesianChartDiagram`): the functions on `W ×_R P` are the
base change of the functions on `W` along `Γ(W') ⟶ Γ(W' ×_T Q)`.

## Main definitions

* `AlgebraicGeometry.Space.cartesianChartDiagram`: the chart diagram `W ×_R P ⟶ W' ×_T Q` over `p`.

## Main results

* `AlgebraicGeometry.Space.isPullback_toScheme_cartesianChartDiagram`: the square of schemes is
  cartesian.
* `AlgebraicGeometry.Space.isPushout_cartesianChartDiagram`: the square of rings is a pushout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q R T : AlgebraicSpaces B S hS} {p : P ⟶ Q} {q : P ⟶ R} {r : Q ⟶ T} {s : R ⟶ T}
    (hsq : IsPullback p q r s) (hq : yoneda.relativelyRepresentable q.hom)
    (hr : yoneda.relativelyRepresentable r.hom) (d : ChartDiagram B S hS R.1 T.1 s.hom)

include hsq in
/-- The two maps `W ×_R P ⟶ T` given by `W ×_R P ⟶ P ⟶ Q ⟶ T` and `W ×_R P ⟶ W ⟶ W' ⟶ T`
agree. -/
theorem cartesianChartDiagram_cond :
    (hq.fst d.U.1.hom ≫ p.hom) ≫ r.hom = yoneda.map (hq.snd d.U.1.hom ≫ d.g) ≫ d.V.1.hom := by
  have hw : p.hom ≫ r.hom = q.hom ≫ s.hom := congrArg (fun k => k.hom) hsq.w
  calc (hq.fst d.U.1.hom ≫ p.hom) ≫ r.hom = (hq.fst d.U.1.hom ≫ q.hom) ≫ s.hom := by
        rw [Category.assoc, hw, Category.assoc]
    _ = (yoneda.map (hq.snd d.U.1.hom) ≫ d.U.1.hom) ≫ s.hom := by rw [hq.w]
    _ = yoneda.map (hq.snd d.U.1.hom) ≫ yoneda.map d.g ≫ d.V.1.hom := by
        rw [Category.assoc, d.comm]
    _ = yoneda.map (hq.snd d.U.1.hom ≫ d.g) ≫ d.V.1.hom := by
        rw [yoneda.map_comp, Category.assoc]

/-- **The chart diagram `W ×_R P ⟶ W' ×_T Q` over `p`** of a cartesian square and a chart diagram
`W ⟶ W'` over `s`. -/
def cartesianChartDiagram : ChartDiagram B S hS P.1 Q.1 p.hom where
  U := (smallBaseChange B S hS q hq).obj d.U
  V := (smallBaseChange B S hS r hr).obj d.V
  g := hr.lift (hq.fst d.U.1.hom ≫ p.hom) (hq.snd d.U.1.hom ≫ d.g)
    (cartesianChartDiagram_cond B S hS hsq hq d)
  comm := (hr.lift_fst _ _ _).symm

/-- The chart map `W ×_R P ⟶ W' ×_T Q` followed by the projection to `W'` is the projection
`W ×_R P ⟶ W` followed by `d.g`. -/
theorem cartesianChartDiagram_g_snd :
    (cartesianChartDiagram B S hS hsq hq hr d).g ≫ hr.snd d.V.1.hom =
      hq.snd d.U.1.hom ≫ d.g :=
  hr.lift_snd _ _ _

/-- The chart map `W ×_R P ⟶ W' ×_T Q` followed by the projection to `Q` is the projection
`W ×_R P ⟶ P` followed by `p`. -/
theorem cartesianChartDiagram_g_fst :
    yoneda.map (cartesianChartDiagram B S hS hsq hq hr d).g ≫ hr.fst d.V.1.hom =
      hq.fst d.U.1.hom ≫ p.hom :=
  hr.lift_fst _ _ _

/-- **The square of schemes `W ×_R P`, `W`, `W' ×_T Q`, `W'` is cartesian.** -/
theorem isPullback_toScheme_cartesianChartDiagram :
    IsPullback ((BigFppfOver.toScheme B S hS).map (hq.snd d.U.1.hom))
      ((BigFppfOver.toScheme B S hS).map (cartesianChartDiagram B S hS hsq hq hr d).g)
      ((BigFppfOver.toScheme B S hS).map d.g)
      ((BigFppfOver.toScheme B S hS).map (hr.snd d.V.1.hom)) := by
  have hbig' : IsPullback (yoneda.map (cartesianChartDiagram B S hS hsq hq hr d).g ≫
      hr.fst d.V.1.hom) (yoneda.map (hq.snd d.U.1.hom)) r.hom
      (yoneda.map d.g ≫ d.V.1.hom) := by
    rw [cartesianChartDiagram_g_fst, ← d.comm]
    exact (hq.isPullback d.U.1.hom).paste_horiz (AlgebraicSpaces.isPullback_hom B S hS hsq)
  have hp : yoneda.map (cartesianChartDiagram B S hS hsq hq hr d).g ≫
      yoneda.map (hr.snd d.V.1.hom) = yoneda.map (hq.snd d.U.1.hom) ≫ yoneda.map d.g :=
    (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
      (cartesianChartDiagram_g_snd B S hS hsq hq hr d)).trans (yoneda.map_comp _ _))
  have hpre := (IsPullback.of_right hbig' hp (hr.isPullback d.V.1.hom)).flip
  exact (IsPullback.of_map_of_faithful yoneda hpre).map (BigFppfOver.toScheme B S hS)

/-- **The rings of functions of a cartesian chart diagram over affine charts form a pushout**:
`Γ(W ×_R P) = Γ(W) ⊗_{Γ(W')} Γ(W' ×_T Q)`. -/
theorem isPushout_cartesianChartDiagram (hU : IsAffine (chartScheme d.U))
    (hV : IsAffine (chartScheme d.V))
    (hQV : IsAffine (chartScheme ((smallBaseChange B S hS r hr).obj d.V))) :
    IsPushout (CommRingCat.ofHom (chartDiagramRestrict B S hS s d))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS r hr d.V))
      (CommRingCat.ofHom (baseChangeChartRestrict B S hS q hq d.U))
      (CommRingCat.ofHom
        (chartDiagramRestrict B S hS p (cartesianChartDiagram B S hS hsq hq hr d))) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.obj.left) := hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.obj.left) := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Q.obj).obj (cartesianChartDiagram B S hS hsq hq hr d).V)) := hQV
  have h := isPushout_appTop_of_isPullback
    (isPullback_toScheme_cartesianChartDiagram B S hS hsq hq hr d)
  exact h

end AlgebraicGeometry.Space

end
