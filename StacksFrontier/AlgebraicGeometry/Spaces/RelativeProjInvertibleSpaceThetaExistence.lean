module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMapNatural

/-!
# `θ` of Stacks 0D2Z on the algebraic space `U(ψ)`, with no presentation supplied

For a pair `(ℒ, ψ)` on the small étale site of an algebraic space `X` over the algebraic space `Y`
of Situation 0849, the map `θ` of [Stacks, Tag 0D2Z] and its clause (1) are built from two étale
presentations (Stacks 0263): one of `Y`, which names the twists `𝒪_{Proj_Y(𝒜)}(d)` of
[Stacks, Tag 084D] and so the source of `θ`, and one of `U(ψ)`, along whose atlas the chart maps of
`θ` are descended (`…InvertibleTwistingRestriction.thetaOfFamily`).  Neither is a datum of the
tag: every algebraic space has one (`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`), and
`U(ψ)` is an algebraic space because it is an open subspace of `X`
(`…InvertibleTwistingRestriction.isOpenSubspace_locus_ofUnitalHom`, already read into
`…InvertibleTwistingRestriction.locusSpaceOfUnitalHom`).

This file takes both presentations inside the proof, so that the statement of `θ` together with
clause (1) and clause (3) carries no presentation: `θ` is asserted to exist, for *some* naming of
the twists, with clause (1) in its morphism form and in the section form the tag states, and with
the chart maps as its restrictions to the scheme points of `U(ψ)`.

## Main results

* `…InvertibleTwistingRestriction.exists_theta_clauseOneSections`: **`θ` and clause (1) of
  [Stacks, Tag 0D2Z] for a pair `(ℒ, ψ)` on an algebraic space `X`, with no presentation of `Y`
  and none of `U(ψ)` among the arguments.**
* `…InvertibleTwistingRestriction.exists_theta_clauseOneSections_of_square`: the same from the
  square of `θ` of [Stacks, Tag 01O9] on the scheme points, the form in which the compatibility of
  the chart maps is proved
  (`…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_square`).

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))

/-- **The chosen étale presentation of the base `Y`** (Stacks 0263): the presentation
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace` attaches to the algebraic space
`s.space`.  It names the twists `𝒪_{Proj_Y(𝒜)}(d)` of [Stacks, Tag 084D], hence the source of
`θ`. -/
def basePresentation :
    Presentation s.site s.base s.containsBase s.space.obj s.space.property :=
  letI : HasSheafify (BigFppfOver.topology s.site s.base s.containsBase) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver s.site s.base s.containsBase
  presentationOfIsAlgebraicSpace s.site s.base s.containsBase s.space.obj s.space.property

/-- **The chosen étale presentation of `U(ψ)`** (Stacks 0263), along whose atlas the chart maps of
`θ` are descended.  `U(ψ)` is an algebraic space because it is an open subspace of `X`
(`…InvertibleTwistingRestriction.isOpenSubspace_locus_ofUnitalHom`), which is what
`…InvertibleTwistingRestriction.locusSpaceOfUnitalHom` records. -/
def locusPresentation :
    Presentation s.shrink.site s.shrink.base s.shrink.containsBase
      (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property :=
  letI : HasSheafify (BigFppfOver.topology s.shrink.site s.shrink.base s.shrink.containsBase)
      (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase
  presentationOfIsAlgebraicSpace s.shrink.site s.shrink.base s.shrink.containsBase
    (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property

/-- **`θ` and clause (1) of [Stacks, Tag 0D2Z] for a pair `(ℒ, ψ)` on the algebraic space `X`,
with no presentation among the arguments.**  Given that the chart maps `χ_w` of `θ` form a
compatible family (`AlgebraicGeometry.Space.PointFamilyNatural`) and that clause (1) holds at
every scheme point `w : T ⟶ U(ψ)` with `χ_w` in place of `θ`, there are a naming of the twists
`𝒪_{Proj_Y(𝒜)}(d)` — that is, a presentation of `Y` — and a map
`θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d ℒ^{⊗ d}|_{U(ψ)}` of quasi-coherent `𝒪_{U(ψ)}`-modules such that

* clause (1) holds for `θ` in the morphism form
  (`…InvertibleTwistingRestriction.ClauseOneHom`) and in the section form the tag states
  (`…InvertibleTwistingRestriction.ClauseOneSections`), and
* clause (3) holds: the inverse image of `θ` along a scheme point `w` of `U(ψ)` is `χ_w`.

Both presentations the construction needs are taken inside the proof:
`…InvertibleTwistingRestriction.basePresentation` for `Y` and
`…InvertibleTwistingRestriction.locusPresentation` for `U(ψ)`. -/
theorem exists_theta_clauseOneSections
    (hχ : ∀ (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
      (d : ℤ), PointFamilyNatural (thetaSourceOfUnitalHom s f L ψ Px d).obj
        (thetaTarget s f L ψ d).obj (fun _ w => chartMap Px w d))
    (hone : ∀ (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
      (d : ℕ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    ∃ (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
      (θ : ∀ d : ℤ, (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj),
      ClauseOneHom s f L ψ Px θ ∧ ClauseOneSections s f L ψ Px θ ∧
      ∀ (d : ℤ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
        (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map (θ d) =
          chartMap Px w d :=
  ⟨basePresentation s, thetaOfFamily (locusPresentation s f L ψ) (hχ (basePresentation s)),
    clauseOneHom_thetaOfFamily (locusPresentation s f L ψ) (hχ (basePresentation s))
      (hone (basePresentation s)),
    clauseOneSections_thetaOfFamily (locusPresentation s f L ψ) (hχ (basePresentation s))
      (hone (basePresentation s)),
    fun d _ w => modulePullback_map_pointHom_thetaOfFamily (locusPresentation s f L ψ)
      (hχ (basePresentation s)) d w⟩

/-- **`θ` and clause (1) of [Stacks, Tag 0D2Z] for a pair `(ℒ, ψ)` on the algebraic space `X`,
from the square of `θ` of [Stacks, Tag 01O9] on the scheme points**, with no presentation among
the arguments: `…InvertibleTwistingRestriction.exists_theta_clauseOneSections` with the
compatibility of the chart maps supplied by
`…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_square`, whose hypothesis `hm`
names no presentation. -/
theorem exists_theta_clauseOneSections_of_square
    (hm : ∀ (d : ℤ) ⦃T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase⦄
      (τ : T' ⟶ T) {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
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
    (hone : ∀ (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
      (d : ℕ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
      (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
      (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOneProjLeg s f L ψ Px d) ≫ chartMap Px w (d : ℤ) =
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
          (clauseOnePsiLeg s f L ψ d)) :
    ∃ (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
      (θ : ∀ d : ℤ, (thetaSourceOfUnitalHom s f L ψ Px d).obj ⟶ (thetaTarget s f L ψ d).obj),
      ClauseOneHom s f L ψ Px θ ∧ ClauseOneSections s f L ψ Px θ ∧
      ∀ (d : ℤ) (T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase)
        (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj),
        (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map (θ d) =
          chartMap Px w d :=
  exists_theta_clauseOneSections s f L ψ
    (fun Px d => pointFamilyNatural_chartMap_of_square Px d (hm d)) hone

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
