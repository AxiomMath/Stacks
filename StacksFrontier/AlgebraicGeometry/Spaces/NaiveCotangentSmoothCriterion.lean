module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentSmoothStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentEtaleChartVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.Cotangent.Spaces.NaiveCotangentComparison
public import StacksFrontier.Cotangent.Spaces.RepresentableStalkH1

/-!
# Smoothness of a morphism of algebraic spaces via the naive cotangent complex

**[Stacks, Tag 0D12].** Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over
`S`. Then `f` is smooth if and only if it is locally of finite presentation,
`H⁻¹(NL_{X/Y}) = 0`, and `H⁰(NL_{X/Y}) = Ω_{X/Y}` is finite locally free.

Here `NL_{X/Y}` is the naive cotangent complex of Stacks 0D0V on the small étale site of `X`,
`AlgebraicGeometry.Space.naiveCotangentComplex`, and `Ω_{X/Y}` is the sheaf of differentials of
Stacks 04CT, `AlgebraicGeometry.Space.sheafOfDifferentials`.

## Proof

Choose, by Stacks 02X1, a commuting square of étale scheme charts `U ⟶ X`, `V ⟶ Y` of `f` whose
chart of the source is surjective, with scheme morphism `ψ : U ⟶ V`. Then:

* `f` is smooth exactly when `ψ` is (Stacks 03ZC: smoothness holds on every étale chart, and is
  detected on one whose source chart is surjective, `AlgebraicGeometry.Space.isSmooth_tfae`);
* if `f` is locally of finite presentation so is `ψ`, and a smooth `f` is locally of finite
  presentation, its charts being smooth;
* `H⁻¹(NL_{X/Y}) = 0` exactly when `H⁻¹(NL_{U/V}) = 0`, by restriction to the chart (Stacks
  0D0W), exactly when `H⁻¹(L_{U/V}) = 0` (Stacks 08US), exactly when `H¹` of the naive cotangent
  complex of every stalk map `𝒪_{V,ψ u} → 𝒪_{U,u}` vanishes (Stacks 08VF, 08T0, 05V1);
* `Ω_{X/Y}` is finite locally free exactly when `Ω_{U/V}` is (Stacks 04CU, 04CS, 05VG);

and the case of schemes, Stacks 0D0N in the pointwise form
`Stacks.Smooth.smooth_iff_subsingleton_h1Cotangent_stalkMap`, concludes.

## Main results

* `AlgebraicGeometry.Space.isSmooth_iff_isZero_homology_negOne_and_isFiniteLocallyFreeOnSite`:
  Stacks 0D12.

## Implementation notes

The third clause is read on `Ω_{X/Y}`; the source states it on `H⁰(NL_{X/Y})` and identifies the
two in the same breath. The sections of `NL_{X/Y}` lie in the universe `u + 1` of the small étale
site while those of `Ω_{X/Y}` lie in `u`, so the two are not objects of one category here; the
clause is stated on `Ω_{X/Y}`, which is the sheaf the source names.

`CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat` is demoted in this file, as in
`StacksFrontier/AlgebraicGeometry/Spaces/NaiveCotangentEtaleRestriction.lean`: tried first at the
universe of the structure rings it poses a universe constraint instance search cannot solve.

## References

* [Stacks Project, Tag 0D12](https://stacks.math.columbia.edu/tag/0D12), Lemma 76.21.8.
* [Stacks Project, Tag 0D0N](https://stacks.math.columbia.edu/tag/0D0N), the case of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0D12.** A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is smooth if
and only if it is locally of finite presentation, the cohomology sheaf `H⁻¹(NL_{X/Y})` of its
naive cotangent complex vanishes, and its sheaf of differentials `Ω_{X/Y} = H⁰(NL_{X/Y})` is
finite locally free on the small étale site of `X`. -/
@[stacks 0D12 "the third clause read on the sheaf of differentials Ω_{X/Y} of 04CT, which the
  source identifies with H⁰(NL_{X/Y})"]
theorem isSmooth_iff_isZero_homology_negOne_and_isFiniteLocallyFreeOnSite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsSmooth B S hS f.hom ↔
      (IsLocallyOfFinitePresentation B S hS f.hom ∧
        IsZero ((naiveCotangentComplex B S hS f).homology (-1)) ∧
        SheafOfModules.IsFiniteLocallyFreeOnSite (sheafOfDifferentials B S hS f)) := by
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
  have hR2 := isFiniteLocallyFreeOnSite_sheafOfDifferentials_iff_chart B S hS f U V a b ψ
    haEtale hbEtale haSurj hdiag.symm
  rw [hR1, hR2]
  constructor
  · intro hf
    have hψ : Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
      hf U V a b ψ haEtale hbEtale hdiag.symm
    obtain ⟨-, hH1, hfree⟩ :=
      (Stacks.Smooth.smooth_iff_subsingleton_h1Cotangent_stalkMap _).1 hψ
    refine ⟨fun U' V' a' b' ψ' ha' hb' hd' ↦ ?_, hH1, hfree⟩
    have : Smooth ((BigFppfOver.toScheme B S hS).map ψ') := hf U' V' a' b' ψ' ha' hb' hd'
    infer_instance
  · rintro ⟨hlfp, hH1, hfree⟩
    have hψ : Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
      (Stacks.Smooth.smooth_iff_subsingleton_h1Cotangent_stalkMap _).2
        ⟨hlfp U V a b ψ haEtale hbEtale hdiag.symm, hH1, hfree⟩
    have htfae := (isSmooth_tfae B S hS X.2 Y.2 f.hom).out 1 8
    exact htfae.2 ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hdiag.symm, hψ⟩

end AlgebraicGeometry.Space

end
