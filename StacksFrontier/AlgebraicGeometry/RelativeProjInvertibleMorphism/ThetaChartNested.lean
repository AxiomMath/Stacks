module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartDatum

/-!
# The source identifications of the relative `θ` over a nested pair of affine opens of the base

`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/ThetaChartDatum.lean` builds, over
the piece `O_V = U(ψ) ∩ f^{-1}(V)` of `U(ψ)` over an affine open `V` of the base, the
identification `…GradedPowerMap.chartSourceLegIso` of the source of the relative `θ` of
[Stacks, Tag 01O9] with the inverse image of the absolute twist along the leg
`O_V ⟶ Proj 𝒜(V)`. **This file proves that those identifications are compatible along an
inclusion `Z ≤ V` of affine opens of the base**, with [Stacks, Tag 01MY]'s comparison map for the
restriction `𝒜(V) → 𝒜(Z)` as the tail.

That is the `hsrc` hypothesis of `…Tag07ZGTwist.nested_of_comp_target`, the variable-level
assembly out of which the nested compatibility of a chart datum is built; it is the same
hypothesis `…Tag07ZGTwist.relativeTwistChart_nested` discharges for [Stacks, Tag 07ZG], and the
content is identical, the source of the two constructions being the same relative twist pulled
back along a morphism into `Proj_S(𝒜)`.

## Main definitions

* `…GradedPowerMap.nestedPresent`: the leg presenting the smaller piece inside the domain of
  definition of the restriction `𝒜(V) → 𝒜(Z)` — the `p` of
  `…Tag07ZGTwist.chartTwistIso_hom_nested`.

## Main results

* `…GradedPowerMap.pieceLeg_comp_projInclusionMap`: **the leg out of the smaller piece followed by
  [Stacks, Tag 01NP]'s transition is the inclusion of the smaller piece into the larger followed
  by the leg out of the larger.** Appending the chart over `V` makes both composites the inclusion
  of the smaller piece followed by `r_{ℒ,ψ}`, and that chart is a monomorphism.
* `…GradedPowerMap.pieceTargetLeg_comp_homOfLE`: the same for the legs into `f^{-1}(V)` along
  which the nested comparison of the **targets** is taken.
* `…GradedPowerMap.chartSourceLegIso_hom_nested`: **the source identifications are
  nested-compatible.**

## What is not done here

The target half and the splice are not here. The nested compatibility of the chart datum needs
three inputs: this one; the same statement for the **target** identification, whose tail is
[Stacks, Tag 01CU]'s comparison of the integer tensor powers under pullback
(`…ProjChartIntPullbackMul.intPullIso`) rather than a chart identification of a relative twist;
and the splice, which is the nested compatibility of [Stacks, Tag 01NK]'s `θ` itself at the level
of **morphisms**. The two halves of that last one are proved at the level of sections over a
standard open — `…ProjChartGradedThetaSheafRingFunctoriality.pushTheta_comap_app_basicOpen` and
`…GradedPowerMap.pushTheta_nestedDatum` — and the passage from there to morphisms is not. See
`…GradedPowerMap.IsNestedThetaChart`.

No attribute is claimed.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjInclusionTwist (projInclusionTopSection_comp_mapHom)
open Stacks.AlgebraicGeometry.ProjShared (mapDomain)
open Stacks.AlgebraicGeometry.ProjTwistChain (mapHom)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.Tag07ZGTwist (relativeTwist chartTwistIso twistMapAt
  chartTwistIso_hom_nested comp_congr_right prefix_nested_rearrange)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

variable {Z V : S.affineOpens} (h : (Z.1 : S.Opens) ≤ (V.1 : S.Opens))

/-- **The leg out of the smaller piece, followed by [Stacks, Tag 01NP]'s transition, is the
inclusion of the smaller piece into the larger followed by the leg out of the larger.** Appending
the chart over `V` makes both composites the inclusion of the smaller piece followed by
`r_{ℒ,ψ}` — by `…GradedPowerMap.pieceLeg_comp_chart` on each side and the compatibility of the
charts with the transitions — and that chart is a monomorphism. -/
public theorem pieceLeg_comp_projInclusionMap :
    P.pieceLeg (Z.1 : S.Opens) Z.2
        ≫ projInclusionMap A (Z.1 : S.Opens) (V.1 : S.Opens) h Z.2 V.2
      = P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h)
          ≫ P.pieceLeg (V.1 : S.Opens) V.2 := by
  rw [← cancel_mono ((relativeProj A).chart (V.1 : S.Opens) V.2), Category.assoc,
    (relativeProj A).chart_transition (Z.1 : S.Opens) (V.1 : S.Opens) h Z.2 V.2,
    P.pieceLeg_comp_chart (relativeProj A) Z, Category.assoc,
    P.pieceLeg_comp_chart (relativeProj A) V, ← Category.assoc,
    P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h)]

/-- **The leg out of the smaller piece into `f^{-1}(Z)`, followed by the inclusion of
`f^{-1}(Z)` in `f^{-1}(V)`, is the inclusion of the smaller piece into the larger followed by the
leg out of the larger.** Appending the inclusion of `f^{-1}(V)` in `X` makes both composites the
inclusion of the smaller piece followed by that of `U(ψ)`, by
`…GradedPowerMap.pieceTargetLeg_comp_ι` on each side, and that inclusion is a monomorphism.

This is for the target of the chart datum what `…GradedPowerMap.pieceLeg_comp_projInclusionMap` is
for its source: the identification of the two legs along which the nested comparison of the
targets is taken. -/
public theorem pieceTargetLeg_comp_homOfLE :
    P.pieceTargetLeg (Z.1 : S.Opens) Z.2 ≫ T.homOfLE (f.preimage_mono h)
      = P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h)
          ≫ P.pieceTargetLeg (V.1 : S.Opens) V.2 := by
  rw [← cancel_mono (f ⁻¹ᵁ (V.1 : S.Opens)).ι, Category.assoc,
    T.homOfLE_ι (f.preimage_mono h), P.pieceTargetLeg_comp_ι (Z.1 : S.Opens) Z.2,
    Category.assoc, P.pieceTargetLeg_comp_ι (V.1 : S.Opens) V.2, ← Category.assoc,
    P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h)]

/-- **The leg presenting the smaller piece inside the domain of definition of the restriction
`𝒜(V) → 𝒜(Z)`.** This is the `p` of `…Tag07ZGTwist.chartTwistIso_hom_nested`: the leg out of the
smaller piece followed by [Stacks, Tag 01NO]'s identification of `Proj 𝒜(Z)` with that domain. -/
public def nestedPresent : (P.toBase ⁻¹ᵁ (Z.1 : S.Opens)).toScheme
    ⟶ (mapDomain (A.grading (V.1 : S.Opens)) (A.grading (Z.1 : S.Opens)) (A.res h)).toScheme :=
  P.pieceLeg (Z.1 : S.Opens) Z.2
    ≫ projInclusionTopSection A (Z.1 : S.Opens) (V.1 : S.Opens) h Z.2 V.2

/-- The presenting leg composed with [Stacks, Tag 01MY]'s morphism is the inclusion of the smaller
piece followed by the leg out of the larger. -/
public theorem nestedPresent_comp_mapHom :
    P.nestedPresent h
        ≫ mapHom (A.grading (V.1 : S.Opens)) (A.grading (Z.1 : S.Opens)) (A.res h)
      = P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h)
          ≫ P.pieceLeg (V.1 : S.Opens) V.2 :=
  by rw [nestedPresent, Category.assoc,
    projInclusionTopSection_comp_mapHom A (Z.1 : S.Opens) (V.1 : S.Opens) h Z.2 V.2]
     exact P.pieceLeg_comp_projInclusionMap h

/-- The presenting leg composed with the inclusion of the domain of definition is the leg out of
the smaller piece. -/
public theorem nestedPresent_comp_ι :
    P.nestedPresent h
        ≫ (mapDomain (A.grading (V.1 : S.Opens)) (A.grading (Z.1 : S.Opens)) (A.res h)).ι
      = P.pieceLeg (Z.1 : S.Opens) Z.2 :=
  by rw [nestedPresent, Category.assoc,
    projInclusionTopSection_ι A (Z.1 : S.Opens) (V.1 : S.Opens) h Z.2 V.2, Category.comp_id]

/-- **The source identifications over a nested pair of affine opens of the base are compatible**,
with [Stacks, Tag 01MY]'s comparison map for the restriction `𝒜(V) → 𝒜(Z)`, read at the presenting
leg, as the tail.

This is the `hsrc` hypothesis of `…Tag07ZGTwist.nested_of_comp_target` for the relative `θ`. The
content is `…Tag07ZGTwist.chartTwistIso_hom_nested` — [Stacks, Tag 01NR]'s two-chart
compatibility at arbitrary legs — with the leading pseudofunctoriality factor of the inclusion of
the piece and of `r_{ℒ,ψ}` moved across by `…Tag07ZGTwist.prefix_nested_rearrange`. -/
public theorem chartSourceLegIso_hom_nested (n : ℤ) :
    (P.chartSourceLegIso Z n).hom
      = (Scheme.Modules.pullbackCongr
            (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h))).inv.app
          ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj
            (relativeTwist A n))
        ≫ (Scheme.Modules.pullbackComp
              (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
              (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).inv.app
            ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj
              (relativeTwist A n))
        ≫ (Scheme.Modules.pullback
              (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))).map
            ((P.chartSourceLegIso V n).hom)
        ≫ (Scheme.Modules.pullbackComp
              (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
              (P.pieceLeg (V.1 : S.Opens) V.2)).hom.app
            (twistM (A.grading (V.1 : S.Opens)) n)
        ≫ twistMapAt (A.grading (V.1 : S.Opens)) (A.grading (Z.1 : S.Opens)) (A.res h) n
            (P.nestedPresent h) (P.nestedPresent_comp_mapHom h) (P.nestedPresent_comp_ι h) := by
  have hkc : P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h)
        ≫ (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ P.globalMorphism (relativeProj A)
      = (P.toBase ⁻¹ᵁ (Z.1 : S.Opens)).ι ≫ P.globalMorphism (relativeProj A) :=
    by rw [← Category.assoc, P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h)]
  rw [P.chartSourceLegIso_hom V n]
  refine Eq.trans ((P.chartSourceLegIso_hom Z n).trans (comp_congr_right _
    (chartTwistIso_hom_nested A n Z V h
      (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
      (P.pieceLeg_comp_chart (relativeProj A) V) (P.pieceLeg_comp_chart (relativeProj A) Z)
      hkc (P.nestedPresent h) rfl
      (P.nestedPresent_comp_mapHom h) (P.nestedPresent_comp_ι h)))) ?_
  exact prefix_nested_rearrange (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
    (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι (P.globalMorphism (relativeProj A))
    (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h)) hkc (relativeTwist A n) _ _

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
