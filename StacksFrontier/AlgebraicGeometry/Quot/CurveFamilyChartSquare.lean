module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyChartToBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Chart squares of a morphism of families of curves

Let `a : F' ⟶ F` be a morphism of families of curves (Stacks 0D4Z): a cartesian square
`X' = X ×_S S'` of algebraic spaces. For étale charts `W` of `X'` and `V` of `X` and a morphism
of schemes `g : W ⟶ V` lying over `X' ⟶ X`, the square of schemes
```
W --g--> V
|        |
S' ----> S
```
commutes, and the induced morphism `W ⟶ V ×_S S'` is étale: `V ×_S S'` is the base change
`V ×_X X'`, an étale chart of `X'`, and a morphism between étale charts is étale (Stacks 03EC).
These are the squares along which relative dualizing complexes of the charts are compared.

## Main results

* `AlgebraicGeometry.CurveFamily.Hom.chartToBase_comm`: the square commutes.
* `AlgebraicGeometry.CurveFamily.Hom.etale_chartGap`: the gap morphism `W ⟶ V ×_S S'` is étale.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily.Hom

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} {F' F : CurveFamily B hZ} (a : F' ⟶ F)
  {W : Space.SmallEtale B integerBase hZ F'.total.1}
  {V : Space.SmallEtale B integerBase hZ F.total.1}
  {g : W.obj.left ⟶ V.obj.left}

/-- The cartesian square of a morphism of families, read on presheaves. -/
theorem isPullback_presheaf :
    IsPullback a.totalMap.hom F'.toBaseHom F.toBaseHom (yoneda.map a.baseMap) :=
  AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian

include a in
/-- **The square of a chart morphism over a morphism of families commutes.** -/
theorem chartToBase_comm (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.totalMap.hom) :
    g ≫ F.chartToBase V = F'.chartToBase W ≫ a.baseMap := by
  apply Yoneda.fullyFaithful.map_injective
  have hw := (isPullback_presheaf a).w
  rw [Functor.map_comp, Functor.map_comp, yoneda_map_chartToBase, yoneda_map_chartToBase,
    ← Category.assoc, hg, Category.assoc, hw, Category.assoc]

/-- The morphism of the site `V ×_S S' ⟶ X'` exhibiting the base change of the chart `V` as an
étale chart of `X'`. -/
def chartBaseChangeHom (V : Space.SmallEtale B integerBase hZ F.total.1) :
    yoneda.obj (pullback (F.chartToBase V) a.baseMap) ⟶ F'.total.1 :=
  (isPullback_presheaf a).lift (yoneda.map (pullback.fst _ _) ≫ V.obj.hom)
    (yoneda.map (pullback.snd _ _)) (by
      calc (yoneda.map (pullback.fst (F.chartToBase V) a.baseMap) ≫ V.obj.hom) ≫ F.toBaseHom
          = yoneda.map (pullback.fst (F.chartToBase V) a.baseMap) ≫ (V.obj.hom ≫ F.toBaseHom) :=
            Category.assoc _ _ _
        _ = yoneda.map (pullback.fst (F.chartToBase V) a.baseMap) ≫
            yoneda.map (F.chartToBase V) := by rw [yoneda_map_chartToBase]
        _ = yoneda.map (pullback.fst (F.chartToBase V) a.baseMap ≫ F.chartToBase V) :=
            (Functor.map_comp _ _ _).symm
        _ = yoneda.map (pullback.snd (F.chartToBase V) a.baseMap ≫ a.baseMap) := by
            rw [pullback.condition]
        _ = yoneda.map (pullback.snd (F.chartToBase V) a.baseMap) ≫ yoneda.map a.baseMap :=
            Functor.map_comp _ _ _)

/-- The base change `V ×_S S' ⟶ X'` of the chart `V`, followed by `X' ⟶ X`, is the projection
`V ×_S S' ⟶ V` followed by the chart `V ⟶ X`. -/
theorem chartBaseChangeHom_totalMap (V : Space.SmallEtale B integerBase hZ F.total.1) :
    a.chartBaseChangeHom V ≫ a.totalMap.hom = yoneda.map (pullback.fst _ _) ≫ V.obj.hom :=
  (isPullback_presheaf a).lift_fst _ _ _

/-- The base change `V ×_S S' ⟶ X'` of the chart `V`, followed by `X' ⟶ S'`, is the projection
`V ×_S S' ⟶ S'`. -/
theorem chartBaseChangeHom_toBase (V : Space.SmallEtale B integerBase hZ F.total.1) :
    a.chartBaseChangeHom V ≫ F'.toBaseHom = yoneda.map (pullback.snd _ _) :=
  (isPullback_presheaf a).lift_snd _ _ _

/-- `V ×_S S' = V ×_X X'`. -/
theorem isPullback_chartBaseChangeHom (V : Space.SmallEtale B integerBase hZ F.total.1) :
    IsPullback (a.chartBaseChangeHom V) (yoneda.map (pullback.fst (F.chartToBase V) a.baseMap))
      a.totalMap.hom V.obj.hom := by
  have hP := ((IsPullback.of_hasPullback (F.chartToBase V) a.baseMap).map yoneda).flip
  have hout : IsPullback (a.chartBaseChangeHom V ≫ F'.toBaseHom)
      (yoneda.map (pullback.fst (F.chartToBase V) a.baseMap)) (yoneda.map a.baseMap)
      (V.obj.hom ≫ F.toBaseHom) := by
    have e1 := a.chartBaseChangeHom_toBase V
    have e2 := yoneda_map_chartToBase F V
    exact (e1 ▸ e2 ▸ hP)
  exact IsPullback.of_right hout (a.chartBaseChangeHom_totalMap V) (isPullback_presheaf a).flip

/-- The base change of an étale chart of `X` is an étale chart of `X'`. -/
theorem isEtale_chartBaseChangeHom (V : Space.SmallEtale B integerBase hZ F.total.1) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ)).presheaf (a.chartBaseChangeHom V) :=
  Space.presheaf_of_isPullback B integerBase hZ (a.isPullback_chartBaseChangeHom V).flip
    V.property

/-- The gap morphism of the site `W ⟶ V ×_S S'`. -/
def chartGap (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.totalMap.hom) :
    W.obj.left ⟶ pullback (F.chartToBase V) a.baseMap :=
  pullback.lift g (F'.chartToBase W) (a.chartToBase_comm hg)

/-- The gap morphism `W ⟶ V ×_S S'` followed by `V ×_S S' ⟶ X'` is the chart `W ⟶ X'`. -/
theorem chartGap_chartBaseChangeHom (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.totalMap.hom) :
    yoneda.map (a.chartGap hg) ≫ a.chartBaseChangeHom V = W.obj.hom := by
  apply (isPullback_presheaf a).hom_ext
  · rw [Category.assoc, chartBaseChangeHom_totalMap, ← Category.assoc, ← Functor.map_comp,
      chartGap, pullback.lift_fst, hg]
  · rw [Category.assoc, chartBaseChangeHom_toBase, ← Functor.map_comp, chartGap, pullback.lift_snd,
      yoneda_map_chartToBase]

/-- **The gap morphism of a chart square is étale** (as a morphism of the site). -/
theorem etale_chartGap (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.totalMap.hom) :
    Etale ((BigFppfOver.toScheme B integerBase hZ).map (a.chartGap hg)) :=
  Space.etale_of_etale_charts B integerBase hZ W.obj.hom (a.chartBaseChangeHom V) W.property
    (a.isEtale_chartBaseChangeHom V) (a.chartGap hg) (a.chartGap_chartBaseChangeHom hg)

end AlgebraicGeometry.CurveFamily.Hom

end
