module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMapNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSquareQcoh
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaExistence

/-!
# `θ` of Stacks 0D2Z on `U(ψ)` descended from the chart maps

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space
`Y` of Situation 0849, the map `θ : r^*𝒪(d) ⟶ ℒ^{⊗ d}|_{U(ψ)}` of [Stacks, Tag 0D2Z] is descended
along a presentation of `U(ψ)` from the family of chart maps
`χ_w = (chartTargetIso w) ∘ θ_w^a ∘ (chartSourceIso w)` at the scheme points `w : W ⟶ U(ψ)`
(`…InvertibleTwistingRestriction.thetaOfFamily`), as soon as that family is compatible
(`AlgebraicGeometry.Space.PointFamilyNatural`) in every degree.  The compatibility follows from the
squares of `θ` of [Stacks, Tag 01O9] on the schemes along the morphisms `τ : T' ⟶ T` of the site
(`…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_square`); this file collects it in
every degree and defines `θ` from it.

## Main definitions

* `…InvertibleTwistingRestriction.thetaOfChartMaps`: `θ` descended from the chart maps, given
  their compatibility.
* `…InvertibleTwistingRestriction.descendedTheta`: `θ` descended from the chart maps.

## Main results

* `…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_squares`: the chart maps form a
  compatible family in every degree, from the squares of `θ` on the schemes.
* `…InvertibleTwistingRestriction.modulePullback_map_pointHom_thetaOfChartMaps`: the restriction
  of `θ` to a scheme point `w` is `θ` of Tag 01O9 on `W` through the identifications of its source
  and target.
* `…InvertibleTwistingRestriction.pointFamilyNatural_chartMap`: **the chart maps form a compatible
  family in every degree**, the squares of `θ` on the schemes being
  `…InvertibleTwistingRestriction.chartSchemeTheta_square`.
* `…InvertibleTwistingRestriction.descendedTheta`,
  `…InvertibleTwistingRestriction.modulePullback_map_pointHom_descendedTheta`: `θ` on `U(ψ)` and
  its restriction to the scheme points.
* `…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_points`: `θ` and clause (1)
  with no presentation among the arguments, from clause (1) at the scheme points.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (P : Presentation s.shrink.site s.shrink.base s.shrink.containsBase
    (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property)

/-- **The chart maps of `θ` form a compatible family in every degree, from the squares of `θ` on
the schemes**: if in every degree `d` the maps `θ_w` of [Stacks, Tag 01O9] at the scheme points
`w` of `U(ψ)` form squares along every `τ : T' ⟶ T` with the comparisons `σ` of their sources and
`τ^*((w^*ℒ)^{⊗ d}) ⟶ ((w ∘ τ)^*ℒ)^{⊗ d}` of their targets, the chart maps `χ_w` form a compatible
family (`AlgebraicGeometry.Space.PointFamilyNatural`) in every degree. -/
theorem pointFamilyNatural_chartMap_of_squares
    (hm : ∀ (d : ℤ) ⦃T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase⦄
      (τ : T' ⟶ T)
      {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
      {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')
      (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
        s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
      (hy : s.relativeProjPoints.LiesOver y τ)
      (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
          (quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) ⟶
        quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
          (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d)),
      σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).hom ≫
        quasicoherentPullbackEqToHom s.site s.base s.containsBase
          (comp_chartSection_locusPoint τ hw y hy) (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) ≫
        (quasicoherentPullbackCompIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
          (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d).hom →
      quasicoherentPullbackMap s.site s.base s.containsBase τ
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d) ≫
            (pointLaurentPiecePullbackHom L τ (locusPoint w) d ≫
              eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k d)
                (map_comp_locusPoint τ hw))) =
        σ ≫ chartSchemeTheta s f L ψ (locusPoint w') (locusOpen_locusPoint w') d)
    (d : ℤ) :
    PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj (thetaTarget s f L ψ d).obj
      (fun _ w => chartMap Px w d) :=
  pointFamilyNatural_chartMap_of_square Px d (hm d)

/-- **`θ` of [Stacks, Tag 0D2Z] descended from the chart maps**, in every degree `d`: the morphism
`r^*𝒪(d) ⟶ ℒ^{⊗ d}|_{U(ψ)}` of quasi-coherent `𝒪_{U(ψ)}`-modules descended along the presentation
`P` of `U(ψ)` from the compatible family of chart maps `χ_w` (Stacks 03M3). -/
def thetaOfChartMaps
    (hχ : ∀ d : ℤ, PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj
      (thetaTarget s f L ψ d).obj (fun _ w => chartMap Px w d)) (d : ℤ) :
    (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj :=
  thetaOfFamily (χ := fun d _ w => chartMap Px w d) P hχ d

/-- **Clause (3) of [Stacks, Tag 0D2Z] for `θ` descended from the chart maps**: its restriction
to a scheme point `w : W ⟶ U(ψ)` is `θ` of [Stacks, Tag 01O9] on `W` for `w^*ψ`
(`…InvertibleTwistingRestriction.chartSchemeTheta`), read through the identifications
`…chartSourceIso` and `…chartTargetIso` of its source and target. -/
theorem modulePullback_map_pointHom_thetaOfChartMaps
    (hχ : ∀ d : ℤ, PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj
      (thetaTarget s f L ψ d).obj (fun _ w => chartMap Px w d)) (d : ℤ)
    {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (thetaOfChartMaps Px P hχ d) =
      (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.map
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
        (chartTargetIso w d).hom :=
  modulePullback_map_pointHom_thetaOfFamily_chartMap P hχ d w

/-- **The chart maps of `θ` form a compatible family in every degree**
(`AlgebraicGeometry.Space.PointFamilyNatural`): the squares of `θ` of [Stacks, Tag 01O9] on the
schemes are `…InvertibleTwistingRestriction.chartSchemeTheta_square`. -/
theorem pointFamilyNatural_chartMap (d : ℤ) :
    PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj (thetaTarget s f L ψ d).obj
      (fun _ w => chartMap Px w d) :=
  pointFamilyNatural_chartMap_of_squares Px chartSchemeTheta_square d

/-- **`θ` of [Stacks, Tag 0D2Z] on `U(ψ)`**, in every degree `d`: the morphism
`r^*𝒪(d) ⟶ ℒ^{⊗ d}|_{U(ψ)}` of quasi-coherent `𝒪_{U(ψ)}`-modules descended along the presentation
`P` of `U(ψ)` from the chart maps `χ_w` at the scheme points (Stacks 03M3), which form a compatible
family by `…InvertibleTwistingRestriction.pointFamilyNatural_chartMap`. -/
def descendedTheta (d : ℤ) :
    (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj :=
  thetaOfChartMaps Px P (pointFamilyNatural_chartMap Px) d

/-- **Clause (3) of [Stacks, Tag 0D2Z] at the scheme points**: the restriction of `θ` on `U(ψ)`
to a scheme point `w : W ⟶ U(ψ)` is `θ` of [Stacks, Tag 01O9] on `W` for `w^*ψ`
(`…InvertibleTwistingRestriction.chartSchemeTheta`), read through the identifications
`…chartSourceIso` and `…chartTargetIso` of its source and target. -/
theorem modulePullback_map_pointHom_descendedTheta (d : ℤ)
    {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (descendedTheta Px P d) =
      (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.map
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d)).hom ≫
        (chartTargetIso w d).hom :=
  modulePullback_map_pointHom_thetaOfChartMaps Px P (pointFamilyNatural_chartMap Px) d w

/-- **`θ` of [Stacks, Tag 0D2Z] and clause (1) for a pair `(ℒ, ψ)` on the algebraic space `X`,
from clause (1) at the scheme points**, with no presentation among the arguments and the
compatibility of the chart maps discharged:
`…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_square` with the squares of `θ`
on the schemes supplied by `…InvertibleTwistingRestriction.chartSchemeTheta_square`. -/
theorem exists_theta_clauseOneSections_of_points
    (hone : ∀ (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
      (d : ℕ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    type_of% (exists_theta_clauseOneSections_of_square s f L ψ chartSchemeTheta_square hone) :=
  exists_theta_clauseOneSections_of_square s f L ψ chartSchemeTheta_square hone

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
