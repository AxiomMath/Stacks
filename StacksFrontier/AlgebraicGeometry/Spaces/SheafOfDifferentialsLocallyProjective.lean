module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyProjectiveEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Relative differentials of a formally smooth morphism of algebraic spaces are locally projective

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`.
Stacks 061I asserts that if `f` is formally smooth then the sheaf of relative differentials
`Ω_{X/Y}` of Stacks 04CT is locally projective on `X`, in the sense of Stacks 060R.

The proof is the source's.  A commuting square of étale scheme charts

```
U --α--> V
|        |
a        b
v        v
X --f--> Y
```

with `a` surjective is produced from the formal smoothness of `f`, and in it the morphism of
schemes underlying `α` is affine-locally formally smooth — this is the implication (1) ⟹ (3) of
Stacks 061K in the affine-open reading, `holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally`,
which is unconditional.  A formally smooth ring map has projective module of differentials
(Algebra, Lemma 10.138.7), so `Ω_{U/V}` is locally projective on the scheme `U`
(`Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally`).  The
restriction of `Ω_{X/Y}` to the Zariski site of `U` *is* `Ω_{U/V}`, which is the final sentence
of Stacks 04CU read through Stacks 04CS, and Stacks 060Q propagates local projectivity from the
one surjective chart to every chart, which is the chartwise condition of Stacks 060R.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartSchemeRepresentedAssociatedModuleIso`: the restriction
  to the identity chart of the small-étale module attached to a quasi-coherent module on the
  representing scheme is that module again.
* `AlgebraicGeometry.Space.restrictToChartSchemeMapIso`: restriction to a chart scheme carries
  an isomorphism of `𝒪_X`-modules to an isomorphism of modules on the chart scheme.
* `AlgebraicGeometry.Space.restrictToChartSchemeSheafOfDifferentialsIso`: **the identification
  `Ω_{X/Y}|_U = Ω_{U/V}` on the Zariski site of the chart scheme**, at a commuting square of
  étale charts.

## Main results

* `AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials`: **Stacks 061I**.

## Implementation notes

Nothing is carried.  The two inputs the proof needs are both available:

* the sheaf of relative differentials of a morphism of algebraic spaces is quasi-coherent,
  Stacks 04CV, `AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsQuasicoherent.lean`, which is what
  bundles `Ω_{X/Y}` into the `AlgebraicGeometry.Space.QuasicoherentSheaves` that Stacks 060R
  asks for; and
* the invertibility clause of Stacks 04CS for a morphism of schemes of the site, read on the
  small étale site of the represented algebraic space,
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`.

The chart identification is assembled rather than quoted because the two restrictions of a
module to a chart are indexed differently.  `AlgebraicGeometry.Space.IsLocallyProjective` is
defined through `AlgebraicGeometry.Space.restrictToChart`, while Stacks 060Q is stated for
`AlgebraicGeometry.Space.restrictToChartScheme`; the two are identified by
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`.  On the chart itself,
`AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback_idEtaleChart` turns the
restriction at the chart into the identity-chart restriction of the étale pullback — an
*equality*, so it is used by `rw` — after which Stacks 04CU identifies that pullback with the
sheaf of differentials of `α` and Stacks 04CS with the small-étale module of `Ω_{U/V}`.  The
last step, that the identity-chart restriction of such a module is `Ω_{U/V}` again, is
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` followed by the unit of the
associated-module adjunction of Stacks 03DU, which is an isomorphism at a quasi-coherent module
by Stacks 070S (2) — `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, proved here with no
hypothesis — and `Ω_{U/V}` is quasi-coherent by Stacks 08S2.

Local projectivity is transported across these isomorphisms by
`AlgebraicGeometry.Scheme.Modules.isLocallyProjective_of_iso`; it is a property of the sections
over affine opens and carries no quasi-coherence requirement of its own.

The formal-smoothness input is the affine-open reading of condition (3) of Stacks 061K, not
condition (2): `Stacks.Smooth.FormallySmoothAffineLocally` is exactly what
`Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally`
consumes, and `AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally`
supplies it with no hypothesis.  Routing through
`AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothScheme'` instead would import
that statement's `h0D0F`, the implication (3) ⟹ (1) of Stacks 0D0F, for nothing: the lifting
property of the morphism of schemes is never used, only the formal smoothness of its ring maps
on affine opens.

## References

* [Stacks Project, Tag 061I](https://stacks.math.columbia.edu/tag/061I)
* [Stacks Project, Tag 060R](https://stacks.math.columbia.edu/tag/060R), local projectivity of a
  quasi-coherent module on an algebraic space, and
  [Tag 060Q](https://stacks.math.columbia.edu/tag/060Q), that one surjective chart tests it.
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K), formal smoothness as an
  étale-chart condition.
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F), the affine-open reading
  of formal smoothness of a morphism of schemes.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces, and
  [Tag 04CV](https://stacks.math.columbia.edu/tag/04CV), its quasi-coherence.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the identification
  `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` on a square of étale charts, and
  [Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the differentials of a
  morphism of schemes on its small Zariski and small étale sites.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module on
  the small étale site, and [Tag 070S](https://stacks.math.columbia.edu/tag/070S), its sections.
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2), quasi-coherence of the
  sheaf of relative differentials of a morphism of schemes.
* [Stacks Project, Tag 05JP](https://stacks.math.columbia.edu/tag/05JP), locally projective
  modules on a scheme.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The restriction to the identity chart of the small-étale module attached to a quasi-coherent
module on the representing scheme is that module again. -/
def restrictToChartSchemeRepresentedAssociatedModuleIso (U : BigFppfOver B S hS)
    (N : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hN : SheafOfModules.IsQuasicoherent N) :
    restrictToChartScheme B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
        ((representedAssociatedModule B S hS U
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)).obj N)
        (idEtaleChart B S hS U) ≅ N := by
  refine restrictToChartSchemeIdEtaleChartIso B S hS U _ ≪≫ ?_
  refine (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS U).unitIso.app
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj N)).symm ≪≫ ?_
  exact (@asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ⟨N, hN⟩)).symm

/-- Restriction to the scheme of an étale chart carries an isomorphism of `𝒪_X`-modules to an
isomorphism of modules on the chart scheme. -/
def restrictToChartSchemeMapIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N)
    (A : SmallEtale B S hS F) :
    restrictToChartScheme B S hS F hF M A ≅ restrictToChartScheme B S hS F hF N A :=
  (restrictToChartSchemeFunctor B S hS F hF A).mapIso e

/-- **At a commuting square of étale charts the restriction of `Ω_{X/Y}` to the scheme of the
chart of the source is the Zariski sheaf of relative differentials of the morphism of schemes.**

This is the final sentence of Stacks 04CU: the étale-chart localization of Stacks 04CU reads the
pullback of `Ω_{X/Y}` along the chart as the sheaf of differentials of the morphism of schemes,
Stacks 04CS identifies that with the small-étale module associated to `Ω_{U/V}`, and the
restriction of such a module to the Zariski site of the chart scheme is `Ω_{U/V}` again. -/
def restrictToChartSchemeSheafOfDifferentialsIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1) (α : U ⟶ V)
    (ha : IsEtaleChart B S hS X.1 (CostructuredArrow.mk a))
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : yoneda.map α ≫ b = a ≫ f.hom) :
    restrictToChartScheme B S hS X.1 X.2 (sheafOfDifferentials B S hS f)
        ⟨CostructuredArrow.mk a, ha⟩ ≅
      Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α) := by
  set A : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, ha⟩
  set p : schemeSpace U ⟶ X := ObjectProperty.homMk a
  set q : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  have hpE : IsEtale B S hS p.hom := isEtale_of_presheaf_etale B S hS ha
  have hqE : IsEtale B S hS q.hom := isEtale_of_presheaf_etale B S hS hb
  have hcomm : p ≫ f = schemeSpaceMap α ≫ q := ObjectProperty.hom_ext _ hsq.symm
  -- `Ω_{X/Y}` pulled back along the chart is the sheaf of differentials of `α`, and that is the
  -- small-étale module of `Ω_{U/V}`.
  have echart := (sheafOfDifferentialsSchemeComparison B S hS U V α).some
  have epull : (etaleModulePullback B S hS (chartToSpace B S hS X A)
        (isEtale_chartToSpace B S hS X A)).obj (sheafOfDifferentials B S hS f) ≅
      (representedAssociatedModule B S hS (chartFppfObject B S hS X A)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS X A))).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)) :=
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
        (isEtale_chartToSpace B S hS X A)).app (sheafOfDifferentials B S hS f)).symm ≪≫
      sheafOfDifferentialsEtaleLocalizationIso B S hS f p (schemeSpaceMap α) q hpE hqE hcomm ≪≫
      echart
  rw [← restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS X
    (sheafOfDifferentials B S hS f) A]
  exact restrictToChartSchemeMapIso B S hS _ epull
      (idEtaleChart B S hS (chartFppfObject B S hS X A)) ≪≫
    restrictToChartSchemeRepresentedAssociatedModuleIso B S hS
      (chartFppfObject B S hS X A) _ (Scheme.Hom.isQuasicoherent_relativeDifferentials _)

/-- **Stacks 061I.**  The sheaf of relative differentials `Ω_{X/Y}` of a formally smooth
morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is locally projective on `X`. -/
@[stacks 061I]
theorem isLocallyProjective_sheafOfDifferentials {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : FormallySmooth f.hom) :
    IsLocallyProjective B S hS X.2
      ⟨sheafOfDifferentials B S hS f, isQuasicoherentOnSite_sheafOfDifferentials B S hS f⟩ := by
  obtain ⟨U, V, a, b, α, ha, hb, haS, hsq, hα⟩ :=
    holdsOnSurjectiveEtaleChart_formallySmoothAffineLocally X.2 Y.2 hf
  set A : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, ha⟩
  have hchart : Scheme.Modules.IsLocallyProjective
      (restrictToChartScheme B S hS X.1 X.2 (sheafOfDifferentials B S hS f) A) :=
    Scheme.Modules.isLocallyProjective_of_iso
      (restrictToChartSchemeSheafOfDifferentialsIso B S hS f U V a b α ha hb hsq).symm
      (Stacks.Smooth.isLocallyProjective_relativeDifferentials_of_formallySmoothAffineLocally
        ((BigFppfOver.toScheme B S hS).map α) hα)
  have hall := (exists_surjective_isLocallyProjective_iff_forall B S hS X.1 X.2
    (sheafOfDifferentials B S hS f) (isQuasicoherentOnSite_sheafOfDifferentials B S hS f)).1
    ⟨A, isSurjective_of_presheafSurjective B S hS a haS, hchart⟩
  exact fun W => Scheme.Modules.isLocallyProjective_of_iso
    (restrictToChartIsoRestrictToChartScheme B S hS X.2 _ W).symm (hall W)

end AlgebraicGeometry.Space

end
