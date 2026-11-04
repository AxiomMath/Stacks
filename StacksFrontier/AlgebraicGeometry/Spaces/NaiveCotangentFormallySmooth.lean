module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Main061K
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentEtaleChartVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentHomologyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsLocallyProjective
public import StacksFrontier.Cotangent.Spaces.NaiveCotangentComparison
public import StacksFrontier.Cotangent.Spaces.RepresentableStalkH1
import StacksCore.Tactic.StacksAttribute

/-!
# Formal smoothness of a morphism of algebraic spaces via the naive cotangent complex

**[Stacks, Tag 0D10].** Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over
`S`. Then `f` is formally smooth if and only if `H⁻¹(NL_{X/Y}) = 0` and
`H⁰(NL_{X/Y}) = Ω_{X/Y}` is locally projective.

Here `NL_{X/Y}` is the naive cotangent complex of Stacks 0D0V on the small étale site of `X`,
`AlgebraicGeometry.Space.naiveCotangentComplex`, `Ω_{X/Y}` is the sheaf of differentials of
Stacks 04CT, `AlgebraicGeometry.Space.sheafOfDifferentials`, which is quasi-coherent by
Stacks 04CV, and local projectivity is that of Stacks 060R,
`AlgebraicGeometry.Space.IsLocallyProjective`.

## Proof

The source's proof: Stacks 061K, 0D0W, 0D0X and the case of schemes, Stacks 0D0L. Choose, by
Stacks 02X1, a commuting square of étale scheme charts `a : U ⟶ X`, `b : V ⟶ Y` of `f` with `a`
surjective, and let `ψ : U ⟶ V` be its morphism of schemes. Then:

* `f` is formally smooth exactly when `ψ` is (Stacks 061K: formal smoothness holds on every
  étale chart, `AlgebraicGeometry.Space.formallySmooth_iff_holdsOnEveryEtaleChart`, and is
  detected on one whose source chart is surjective,
  `AlgebraicGeometry.Space.formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme`);
* `H⁻¹(NL_{X/Y}) = 0` exactly when `H⁻¹(NL_{U/V}) = 0`, by restriction to the chart (Stacks
  0D0W), exactly when `H¹` of the naive cotangent complex of every stalk map
  `𝒪_{V,ψ u} ⟶ 𝒪_{U,u}` vanishes (comparison with the scheme `U`, the content of Stacks 0D0X
  in degree `-1`);
* `Ω_{X/Y}` is locally projective exactly when `Ω_{U/V}` is
  (`AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials_iff_chart`: Stacks 04CU and
  04CS identify the restriction of `Ω_{X/Y}` to `U` with `Ω_{U/V}`, and Stacks 060Q reads local
  projectivity on the one surjective chart);

and the case of schemes, Stacks 0D0L in the stalkwise form
`Stacks.Smooth.formallySmoothScheme_iff_subsingleton_h1Cotangent_and_isLocallyProjective`,
concludes.

## Main results

* `AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials_iff_chart`: local
  projectivity of `Ω_{X/Y}` read on an étale chart.
* `AlgebraicGeometry.Space.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective`:
  **Stacks 0D10**.

## Implementation notes

The second condition is read on `Ω_{X/Y}`, as in the source's own `H⁰(NL_{X/Y}) = Ω_{X/Y}`.
The identification of `H⁰(NL_{X/Y})` with `Ω_{X/Y}` is the degree-zero clause of Stacks 0D0Y,
`AlgebraicGeometry.Space.naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials`. The sections
of `NL_{X/Y}` lie in the universe `u + 1` of the small étale site while those of `Ω_{X/Y}` lie in
`u`, so the two are isomorphic only after the universe lift of the sections that this
isomorphism carries.

`CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat` is demoted in this file, as in
`StacksFrontier/AlgebraicGeometry/Spaces/NaiveCotangentSmoothCriterion.lean`.

## References

* [Stacks Project, Tag 0D10](https://stacks.math.columbia.edu/tag/0D10), Lemma 76.21.6.
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L), the case of schemes.
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K), formal smoothness on
  étale charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local projectivity of `Ω_{X/Y}` is read on an étale chart.** In a commuting square of
étale scheme charts `a : U ⟶ X`, `b : V ⟶ Y` of a morphism `f : X ⟶ Y` of algebraic spaces, with
`a` surjective and morphism of schemes `ψ : U ⟶ V`, the sheaf of differentials `Ω_{X/Y}` is
locally projective exactly when `Ω_{U/V}` is.

The restriction of `Ω_{X/Y}` to the chart `U` is `Ω_{U/V}`
(`AlgebraicGeometry.Space.restrictToChartSchemeSheafOfDifferentialsIso`, Stacks 04CU and 04CS),
and local projectivity on the one surjective chart is local projectivity on every chart
(Stacks 060Q). -/
theorem isLocallyProjective_sheafOfDifferentials_iff_chart {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1)
    (ψ : U ⟶ V)
    (haEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hbEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hdiag : yoneda.map ψ ≫ b = a ≫ f.hom) :
    IsLocallyProjective B S hS X.2
        ⟨sheafOfDifferentials B S hS f, isQuasicoherentOnSite_sheafOfDifferentials B S hS f⟩ ↔
      Scheme.Modules.IsLocallyProjective
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)) := by
  let A : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, haEtale⟩
  let e := restrictToChartSchemeSheafOfDifferentialsIso B S hS f U V a b ψ haEtale hbEtale hdiag
  refine ⟨fun h ↦ Scheme.Modules.isLocallyProjective_of_iso e
    (Scheme.Modules.isLocallyProjective_of_iso
      (restrictToChartIsoRestrictToChartScheme B S hS X.2 _ A) (h A)), fun h W ↦ ?_⟩
  exact Scheme.Modules.isLocallyProjective_of_iso
    (restrictToChartIsoRestrictToChartScheme B S hS X.2 _ W).symm
    ((exists_surjective_isLocallyProjective_iff_forall B S hS X.1 X.2
      (sheafOfDifferentials B S hS f) (isQuasicoherentOnSite_sheafOfDifferentials B S hS f)).1
      ⟨A, isSurjective_of_presheafSurjective B S hS a haSurj,
        Scheme.Modules.isLocallyProjective_of_iso e.symm h⟩ W)

/-- **Stacks 0D10.** A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is formally
smooth if and only if the cohomology sheaf `H⁻¹(NL_{X/Y})` of its naive cotangent complex
vanishes and its sheaf of differentials `Ω_{X/Y} = H⁰(NL_{X/Y})` is locally projective.

`Ω_{X/Y}` is the degree-zero cohomology sheaf of `NL_{X/Y}` by Stacks 0D0Y,
`AlgebraicGeometry.Space.naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials`, and is
quasi-coherent by Stacks 04CV, which is the standing hypothesis of local projectivity
(Stacks 060R). -/
@[stacks 0D10 "the second condition read on the sheaf of differentials Ω_{X/Y} of 04CT, which
  the source identifies with H⁰(NL_{X/Y}) (0D0Y)"]
theorem formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    FormallySmooth f.hom ↔
      (IsZero ((naiveCotangentComplex B S hS f).homology (-1)) ∧
        IsLocallyProjective B S hS X.2
          ⟨sheafOfDifferentials B S hS f,
            isQuasicoherentOnSite_sheafOfDifferentials B S hS f⟩) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.2.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V b hbSurj hbEtale
  have haEt : IsEtale B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X).hom :=
    isEtale_of_presheaf_etale B S hS haEtale
  have hbEt : IsEtale B S hS (ObjectProperty.homMk b : schemeSpace V ⟶ Y).hom :=
    isEtale_of_presheaf_etale B S hS hbEtale
  have hsq : (ObjectProperty.homMk a : schemeSpace U ⟶ X) ≫ f =
      schemeSpaceMap ψ ≫ (ObjectProperty.homMk b : schemeSpace V ⟶ Y) :=
    ObjectProperty.hom_ext _ hdiag
  have hR1 := (isZero_homology_negOne_naiveCotangentComplex_iff_of_etale_surjective B S hS U hsq
    haEt hbEt haSurj).trans
    ((isZero_homology_negOne_naiveCotangentComplex_iff_cotangentComplex B S hS
      (schemeSpaceMap ψ)).trans
      (isZero_homology_negOne_cotangentComplex_representedSpaceMap_iff_stalkMap B S hS ψ))
  have hR2 := isLocallyProjective_sheafOfDifferentials_iff_chart B S hS f U V a b ψ
    haEtale hbEtale haSurj hdiag.symm
  have hψ : FormallySmooth f.hom ↔
      Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ) :=
    ⟨fun hf ↦ (formallySmooth_iff_holdsOnEveryEtaleChart B S hS X.2 Y.2 f.hom).1 hf U V a b ψ
        haEtale hbEtale hdiag.symm,
      fun h ↦ formallySmooth_of_surjectiveEtaleChart_of_formallySmoothScheme B S hS X.2 Y.2
        a b ψ haEtale hbEtale haSurj hdiag h⟩
  exact hψ.trans
    ((Stacks.Smooth.formallySmoothScheme_iff_subsingleton_h1Cotangent_and_isLocallyProjective
      _).trans (and_congr hR1.symm hR2.symm))

end AlgebraicGeometry.Space

end
