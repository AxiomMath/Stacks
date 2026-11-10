module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport

/-!
# The étale chart of an open immersion into a chart is a Zariski open of the chart

Let `U` be an étale chart of an algebraic space `X` and `u : V ⟶ U` a morphism of the big fppf
site whose underlying morphism of schemes is an open immersion. Then `V → U → X` is again an
étale chart of `X`, and it is isomorphic, in the small étale site of `X`, to the Zariski open
`u(V)` of `U` regarded as a chart through `AlgebraicGeometry.Space.chartOpens`. This lets
statements about the Zariski opens of a chart be applied to open immersions into it.

## Main results

* `AlgebraicGeometry.Space.isEtale_yoneda_map_comp_of_isOpenImmersion`: `V → U → X` is étale.
* `AlgebraicGeometry.Space.etaleChartIsoChartOpensOfIsOpenImmersion`: the isomorphism with the
  Zariski open `u(V)` of `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open immersion into an étale chart, followed by the chart, is étale. -/
theorem isEtale_yoneda_map_comp_of_isOpenImmersion {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS X) {V : BigFppfOver B S hS} (u : V ⟶ U.obj.left)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u)] :
    IsEtale B S hS (yoneda.map u ≫ U.obj.hom) := by
  rw [isEtale_iff_presheaf_of_yoneda]
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  have : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : P.IsStableUnderBaseChange :=
    ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (sq.map (BigFppfOver.toScheme B S hS)) hg⟩
  have : P.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition P
  apply MorphismProperty.IsStableUnderComposition.comp_mem (P := P.presheaf)
    _ _ _ U.property
  apply (P.relative_map_iff (F := yoneda)).2
  change Etale ((BigFppfOver.toScheme B S hS).map u)
  infer_instance

/-- The étale chart `V → U → X` of an open immersion `u : V ⟶ U` into an étale chart `U` of `X`
is isomorphic, in the small étale site of `X`, to the Zariski open `u(V)` of `U`. -/
def etaleChartIsoChartOpensOfIsOpenImmersion {X : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X.1) {V : BigFppfOver B S hS} (u : V ⟶ U.obj.left)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u)] :
    etaleChartOfIsEtale B S hS (yoneda.map u ≫ U.obj.hom)
        (isEtale_yoneda_map_comp_of_isOpenImmersion B S hS U u) ≅
      (chartOpens B S hS U).obj ((BigFppfOver.toScheme B S hS).map u).opensRange :=
  let f := (BigFppfOver.toScheme B S hS).map u
  let e : V ≅ chartOpenOver B S hS U f.opensRange :=
    Over.isoMk (ObjectProperty.isoMk _ f.isoOpensRange) (by
      apply ObjectProperty.hom_ext
      change f.isoOpensRange.hom ≫ f.opensRange.ι ≫ U.obj.left.hom.hom = V.hom.hom
      rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      exact congrArg (fun g => g.hom) (Over.w u))
  have he : e.hom ≫ chartOpenOverι B S hS U f.opensRange = u := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Scheme.Hom.isoOpensRange_hom_ι f
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk e (by
    change yoneda.map e.hom ≫ yoneda.map (chartOpenOverι B S hS U f.opensRange) ≫ U.obj.hom =
      yoneda.map u ≫ U.obj.hom
    rw [← Category.assoc, ← Functor.map_comp, he]))

/-- The isomorphism `etaleChartIsoChartOpensOfIsOpenImmersion` is compatible with the maps of
both charts to `U`: on underlying objects over the base it composes with the inclusion of
`u(V)` into `U` to give `u`. -/
theorem etaleChartIsoChartOpensOfIsOpenImmersion_hom_comp_ι {X : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X.1) {V : BigFppfOver B S hS} (u : V ⟶ U.obj.left)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u)] :
    (etaleChartIsoChartOpensOfIsOpenImmersion B S hS U u).hom.hom.left ≫
        chartOpenOverι B S hS U ((BigFppfOver.toScheme B S hS).map u).opensRange = u := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact Scheme.Hom.isoOpensRange_hom_ι ((BigFppfOver.toScheme B S hS).map u)

end AlgebraicGeometry.Space

end
