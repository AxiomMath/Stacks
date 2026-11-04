module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart

/-!
# The morphism of relative projective spectra induced by a surjection, and its closed immersion

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras which is surjective on
homogeneous local sections over the affine opens of the base. This file glues the chart maps of
the sibling file into a single morphism

`Proj_S(B) ⟶ Proj_S(A)`

over `S`, and proves it is a **closed immersion**. This is the functoriality of the relative
homogeneous spectrum: Tag 07ZG's assertion (2) in the case where the domain of definition is
everything, together with the relative form of Tag 01N1 part (2).

## Main definitions

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.map`: **the morphism of relative projective
  spectra.**

## Main results

* `Stacks.AlgebraicGeometry.ProjBundleSurjection.chart_comp_map`: its defining equation — on the
  chart over an affine open of the base it is the chart map.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.map_comp_toBase`: it is a morphism **over `S`**.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.isPullback_chart`: the chart over an affine open
  of the base is the inverse image of the corresponding chart of the target. This is the statement
  that makes the closed immersion affine-local.
* `Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_map`: **the morphism is a
  closed immersion.**

## The route

The relative homogeneous spectrum is a *colimit* — `relativeProj A` is the colimit of the chart
functor on the small affine Zariski site of `S`, and `RelativeProjData.chart` is its colimit
inclusion — so a morphism **out of** `Proj_S(B)` is exactly a compatible family of morphisms out
of the charts of `B`. The family is `chartMap` followed by the chart of `A`, and its
compatibility is `chartMap_comp_projInclusionMap`. Nothing about glueing has to be redone.

Being over `S` and being a closed immersion both follow from the colimit as well: the first by
`CategoryTheory.Limits.colimit.hom_ext`, the second because the chart images cover
`Proj_S(A)` and the square

```
Proj Γ(U, B) ⟶ Proj Γ(U, A)
     |               |
Proj_S(B)     ⟶ Proj_S(A)
```

is cartesian, so the restriction of the glued morphism over each chart image *is* the chart map,
which is a closed immersion by Tag 01N1 part (2). Cartesianness is `CategoryTheory.IsPullback`'s
bottom-cancellation applied to the two chart squares of Tag 01NQ and the fact that the glued
morphism is over `S`: both `Proj Γ(U, B)` and `Proj Γ(U, A)` are inverse images of `U`, so
`Proj Γ(U, B) = Proj_S(B) ×_S U = Proj_S(B) ×_{Proj_S(A)} (Proj_S(A) ×_S U)`.

## Implementation notes

The colimit index is `AlgebraicGeometry.Scheme.AffineZariskiSite`, a `def` for the subtype of
affine opens, and `RelativeProjData.chart` is stated for an open together with a proof of
affineness. The two are the same data, and `colimit.ι … V` and
`(relativeProj B).chart V.toOpens V.2` are equal by `rfl`; those identifications are made
explicit as `have … := rfl` rather than left to `rw`, which cannot see through the `def`.

The restriction of the glued morphism over a chart image is compared with the chart map by
`CategoryTheory.IsPullback.isoIsPullback` and
`AlgebraicGeometry.morphismRestrictOpensRange`, exactly as
`Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase` compares the restriction of
the structure morphism with the chart's structure morphism.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)

## Not done here

The hypothesis is surjectivity in every degree, not the eventual surjectivity of Tag 01N1; see
the sibling file for why, which is that the composition law used for the glueing needs Mathlib's
`AlgebraicGeometry.Proj.map`.

Tag 07ZG's assertion (2) in general — a morphism on
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.relativeMapDomain`
for an arbitrary
homomorphism — is not here; it needs the same composition law on the domains of definition. No
project tag is attached: an input to a tagged statement is not one of its clauses, and the
clauses of 07ZG quantify over the full triple of that tag.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.ProjBundleSurjection

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} {ψ : SheafGradedAlgebraHom A B}

/-- The compatibility of the descent family, with every argument a variable.

Stated this way on purpose: the colimit index is
`(AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover S).I₀`, so inside the naturality
obligation the affineness proof appears as a projection `V.2` out of two `def`s, which makes the
goal ill-typed at implicit transparency and defeats every `rw`. With the open, the inclusion and
the affineness as variables there is nothing to see through. -/
public theorem projInclusionMap_comp_chartMap_comp_chart (hψ : SurjectiveOnAffineSections ψ)
    (U V : S.Opens) (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap B U V h hU hV ≫ chartMap hψ V hV ≫ (relativeProj A).chart V hV =
      chartMap hψ U hU ≫ (relativeProj A).chart U hU := by
  rw [← Category.assoc, ← chartMap_comp_projInclusionMap hψ U V h hU hV, Category.assoc,
    (relativeProj A).chart_transition U V h hU hV]

/-- **The morphism of relative projective spectra induced by a surjection of graded algebras.**

`Proj_S(B)` is the colimit of its charts, so the morphism is the descent of the compatible family
whose member over an affine open `U` of the base is the chart map
`Proj Γ(U, B) ⟶ Proj Γ(U, A)` followed by the chart of `A` over `U`. -/
public def map (hψ : SurjectiveOnAffineSections ψ) :
    (relativeProj B).scheme ⟶ (relativeProj A).scheme :=
  colimit.desc (RelativeProjGlue.relativeGluingData B.toGradedAlgebra).functor
    { pt := (relativeProj A).scheme
      ι :=
        { app := fun V => chartMap hψ V.toOpens V.2 ≫ (relativeProj A).chart V.toOpens V.2
          naturality := fun {V W} f => by
            refine Eq.trans ?_ (Category.comp_id _).symm
            exact projInclusionMap_comp_chartMap_comp_chart hψ _ _
              (Scheme.AffineZariskiSite.toOpens_mono f.le) _ _ } }

/-- **The defining equation of the induced morphism**: over the chart of an affine open of the
base it is the chart map. -/
@[reassoc]
public theorem chart_comp_map (hψ : SurjectiveOnAffineSections ψ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    (relativeProj B).chart U hU ≫ map hψ =
      chartMap hψ U hU ≫ (relativeProj A).chart U hU := by
  rw [map]
  exact colimit.ι_desc _ _

/-- The induced morphism is over the base, read on a single chart. -/
public theorem chart_comp_map_comp_toBase (hψ : SurjectiveOnAffineSections ψ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    (relativeProj B).chart U hU ≫ map hψ ≫ (relativeProj A).toBase =
      (relativeProj B).chart U hU ≫ (relativeProj B).toBase := by
  rw [chart_comp_map_assoc hψ U hU, chart_comp_toBase A U hU,
    chartMap_comp_projInclusionToOpen_assoc hψ U hU]
  exact (chart_comp_toBase B U hU).symm

/-- **The induced morphism is a morphism over the base.** -/
@[reassoc]
public theorem map_comp_toBase (hψ : SurjectiveOnAffineSections ψ) :
    map hψ ≫ (relativeProj A).toBase = (relativeProj B).toBase := by
  refine colimit.hom_ext
    (F := (RelativeProjGlue.relativeGluingData B.toGradedAlgebra).functor) fun V => ?_
  exact chart_comp_map_comp_toBase hψ _ _

/-- **The chart over an affine open of the base is the inverse image of the chart of the
target.** Both charts are inverse images of that affine open and the induced morphism is over the
base, so this is the cancellation of the two chart squares of Tag 01NQ. -/
public theorem isPullback_chart (hψ : SurjectiveOnAffineSections ψ) (U : S.Opens)
    (hU : IsAffineOpen U) :
    IsPullback ((relativeProj B).chart U hU) (chartMap hψ U hU) (map hψ)
      ((relativeProj A).chart U hU) := by
  refine IsPullback.of_bot ?_ (chart_comp_map hψ U hU)
    ((relativeProj A).chart_isPullback U hU)
  rw [chartMap_comp_projInclusionToOpen hψ U hU, map_comp_toBase hψ]
  exact (relativeProj B).chart_isPullback U hU

/-- The chart images of the affine opens of the base cover the relative projective spectrum,
stated on the ranges rather than on the inverse images. -/
public theorem iSup_opensRange_chart_eq_top (P : RelativeProjData A) :
    (⨆ U : AffineOpen S, (P.chart U.1 U.2).opensRange) = ⊤ := by
  refine Eq.trans (iSup_congr fun U : AffineOpen S => ?_)
    (iSup_toBase_preimage_eq_top' A P)
  rw [← Scheme.Hom.image_top_eq_opensRange, chart_image_top P U.1 U.2]

/-- **The induced morphism is a closed immersion.**

Being a closed immersion is local at the target; the chart images cover the target; and over the
chart image of an affine open `U` of the base the morphism is the chart map
`Proj Γ(U, B) ⟶ Proj Γ(U, A)`, which is a closed immersion because `Γ(U, A) ⟶ Γ(U, B)` is a
surjection of graded rings. -/
public theorem isClosedImmersion_map (hψ : SurjectiveOnAffineSections ψ) :
    IsClosedImmersion (map hψ) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : AffineOpen S => ((relativeProj A).chart U.1 U.2).opensRange)
    (iSup_opensRange_chart_eq_top (relativeProj A)) fun U => ?_
  have h₂ := isPullback_chart hψ U.1 U.2
  have h₁ : IsPullback (pullback.fst (map hψ) ((relativeProj A).chart U.1 U.2))
      (pullback.snd (map hψ) ((relativeProj A).chart U.1 U.2)) (map hψ)
      ((relativeProj A).chart U.1 U.2) := IsPullback.of_hasPullback _ _
  have e₁ : Arrow.mk (chartMap hψ U.1 U.2) ≅
      Arrow.mk (pullback.snd (map hψ) ((relativeProj A).chart U.1 U.2)) :=
    Arrow.isoMk (h₂.isoIsPullback _ _ h₁) (Iso.refl _)
  have e₂ := morphismRestrictOpensRange (map hψ) ((relativeProj A).chart U.1 U.2)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (e₁.trans e₂.symm)).mp (isClosedImmersion_chartMap hψ U.1 U.2)

end Stacks.AlgebraicGeometry.ProjBundleSurjection

end
