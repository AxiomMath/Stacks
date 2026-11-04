module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.ComparisonChart
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.ComparisonComp

/-!
# The twist comparison across a composite, in the shapes a glueing consumes

Let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of nonnegatively graded rings and `χ` a
third one *equal* to `ψ.comp φ`. `Stacks.ProjTwistComparison.twistMap_comp_of_eq` says that the
three comparisons `θ n` of Tag 01MY compose. This file restates that law in the two shapes the
glueing of a comparison over a cover of charts asks for.

The first shape is for a cover whose charts *grow*: a sheaf `N₀` on an ambient scheme described on
a chart as the twisting sheaf of `𝒜` and on a smaller chart as the twisting sheaf of `ℬ`, pulled
back along one morphism from `Proj 𝒞`, has the same comparison with the twisting sheaf of `𝒞`
read either way. The second is for a cover whose charts *shrink*: the inverse image along
`Proj.map ψ` of the comparison across `φ`, followed by the comparison across `ψ`, is the
comparison across `χ` conjugated by the two pullback comparisons — the hypothesis `hmm` of
`AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq`.

This is the twist counterpart of
`StacksFrontier/AlgebraicGeometry/RelativeProj/ModuleSheaf/ComparisonChart.lean`, run with no
semilinear map to carry: the twisting sheaf is the ring with its grading shifted and the
comparison is induced by `φ` alone.

## Main results

* `Stacks.ProjTwistComparison.twistMap_comp_pullbackChartDesc`: **the two chart descriptions of an
  inverse image, composed with the two comparisons, agree.**
* `Stacks.ProjTwistComparison.map_twistMap_comp_eq`: the composition law solved for the inverse
  image along `Proj.map ψ` of the comparison across `φ`.
* `Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq`: **the nested case of a glueing of
  chart members over a cover whose charts shrink**, for the twisting sheaves.

## Implementation notes

The generic halves of both statements are already in the library and are reused:
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso_refine` for the first and
`AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` for the second, both of which quantify
over arbitrary sheaves of modules. What is twist-specific is only the composition law that
discharges their hypotheses, and the identification
`Stacks.ProjModuleComparison.projMapComp` of `Proj.map` of a composite, which mentions neither a
module nor a twist and is likewise reused.

Stating the nested case here, at bare graded data, is what keeps it checkable: the hypothesis
`hmm` carries three `twistMap`s and cannot be stated at the graded section rings of a relative
projective spectrum, while the conclusion carries two.

## Not done here

No tag is claimed: these are coherence laws of a comparison morphism, not clauses of a tag.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B C : Type u} {σ τ ρ : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
  {χ : 𝒜 →+*ᵍ 𝒞} (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (n : ℤ)

/-! ### Chart descriptions on a growing cover -/

section ChartDesc

variable {X : Scheme.{u}} (f₂ : AlgebraicGeometry.Proj 𝒜 ⟶ X) [IsOpenImmersion f₂]
  {N₀ : X.Modules} (e₂ : N₀.restrict f₂ ≅ twistingSheaf 𝒜 n)
  {f₁ : AlgebraicGeometry.Proj ℬ ⟶ X} [IsOpenImmersion f₁]
  (hl : f₁ = AlgebraicGeometry.Proj.map φ hφ ≫ f₂)
  (e₁ : N₀.restrict f₁ ≅ twistingSheaf ℬ n)
  (hν : (Scheme.Modules.pullbackIsoOfRestrictIso f₂ e₂
          (AlgebraicGeometry.Proj.map φ hφ) hl).hom ≫ twistMap φ hφ n
      = (((Scheme.Modules.restrictFunctorIsoPullback f₁).app N₀).symm ≪≫ e₁).hom)
  {hm : AlgebraicGeometry.Proj 𝒞 ⟶ X}
  (hfac₂ : hm = AlgebraicGeometry.Proj.map χ hχ ≫ f₂)
  (hfac₁ : hm = AlgebraicGeometry.Proj.map ψ hψ ≫ f₁)

include hν in
/-- **The two chart descriptions of an inverse image, composed with the two twist comparisons,
agree.** The sheaf `N₀` is described on the chart `f₂` as the twisting sheaf of `𝒜` and on the
smaller chart `f₁` as that of `ℬ`; pulled back along `hm`, either description followed by the
comparison with the twisting sheaf of `𝒞` gives the same morphism.

The comparison across `φ` occurs twice: in `hν`, the chart-refinement law, which
`AlgebraicGeometry.Scheme.Modules.pullbackIsoOfRestrictIso_refine` turns into the relation between
the two chart descriptions pulled back along `hm`, and in
`Stacks.ProjTwistComparison.twistMap_comp_of_eq`, which relates the two chart comparisons. The two
relations are inverse to each other on it, so composing them gives the identity. -/
public theorem twistMap_comp_pullbackChartDesc (hc : χ = ψ.comp φ) :
    (Scheme.Modules.pullbackIsoOfRestrictIso f₂ e₂
          (AlgebraicGeometry.Proj.map χ hχ) hfac₂).hom ≫ twistMap χ hχ n
      = (Scheme.Modules.pullbackIsoOfRestrictIso f₁ e₁
          (AlgebraicGeometry.Proj.map ψ hψ) hfac₁).hom ≫ twistMap ψ hψ n := by
  have hmap := twistMap_comp_of_eq φ hφ ψ hψ hχ n hc
  have hiso := Scheme.Modules.pullbackIsoOfRestrictIso_refine f₂ e₂
    (AlgebraicGeometry.Proj.map φ hφ) hl e₁ (twistMap φ hφ n) hν
    (AlgebraicGeometry.Proj.map ψ hψ)
    (Stacks.ProjModuleComparison.projMapComp φ hφ ψ hψ χ hχ hc) hfac₂ hfac₁
  exact (whisker_eq _ hmap.symm).trans
    (((Category.assoc _ _ _).trans (whisker_eq _
        ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))))).symm.trans
      (eq_whisker hiso _))

end ChartDesc

/-! ### The composition law as a glueing hypothesis -/

/-- **The two chart comparisons across `φ` and across `χ` are related by the comparisons of the
inverse image along a composite.** This is
`Stacks.ProjTwistComparison.twistMap_comp_of_eq` solved for the inverse image along `Proj.map ψ`
of the comparison across `φ`, which is the hypothesis `hmm` of
`AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` — the nested case of a glueing of chart
members over a cover whose charts shrink. -/
public theorem map_twistMap_comp_eq (hc : χ = ψ.comp φ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map (twistMap φ hφ n)
        ≫ twistMap ψ hψ n
      = (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ)
            (AlgebraicGeometry.Proj.map φ hφ)).hom.app (twistingSheaf 𝒜 n)
        ≫ (Scheme.Modules.pullbackCongr
            (Stacks.ProjModuleComparison.projMapComp φ hφ ψ hψ χ hχ hc)).hom.app
            (twistingSheaf 𝒜 n)
        ≫ twistMap χ hχ n :=
  (((whisker_eq _ (whisker_eq _
      (twistMap_comp_of_eq φ hφ ψ hψ hχ n hc).symm)).trans
    (whisker_eq _ (Iso.hom_inv_id_app_assoc _ _ _))).trans
    (Iso.hom_inv_id_app_assoc _ _ _)).symm

/-! ### The nested case for the chart comparisons -/

section MemberNested

variable {X' Y : Scheme.{u}} {M₀ : Y.Modules} (r : X' ⟶ Y)
  (d : AlgebraicGeometry.Proj 𝒜 ⟶ Y) [IsOpenImmersion d]
  (eB : M₀.restrict d ≅ twistingSheaf 𝒜 n)
  {N' : X'.Modules}
  (c₂ : AlgebraicGeometry.Proj ℬ ⟶ X') [IsOpenImmersion c₂]
  (e'₂ : N'.restrict c₂ ≅ twistingSheaf ℬ n)
  {c₁ : AlgebraicGeometry.Proj 𝒞 ⟶ X'} [IsOpenImmersion c₁]
  (hkc : AlgebraicGeometry.Proj.map ψ hψ ≫ c₂ = c₁)
  (e'₁ : N'.restrict c₁ ≅ twistingSheaf 𝒞 n)
  (hfac₂ : c₂ ≫ r = AlgebraicGeometry.Proj.map φ hφ ≫ d)
  (hfac₁ : c₁ ≫ r = AlgebraicGeometry.Proj.map χ hχ ≫ d)

include hkc in
/-- **The nested case of a glueing of chart members over a cover whose charts shrink**, for the
twisting sheaves.

This is `AlgebraicGeometry.Scheme.Modules.chartMember_pullback_eq` with its hypothesis `hmm`
discharged by `Stacks.ProjTwistComparison.map_twistMap_comp_eq`. -/
public theorem twistMap_chartMember_pullback_eq
    (hν : (Scheme.Modules.pullbackIsoOfRestrictIso c₂ e'₂
          (AlgebraicGeometry.Proj.map ψ hψ) hkc.symm).hom ≫ twistMap ψ hψ n
      = (((Scheme.Modules.restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).hom)
    (hc : χ = ψ.comp φ) :
    (Scheme.Modules.pullbackCongr hkc).inv.app ((Scheme.Modules.pullback r).obj M₀)
        ≫ (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ) c₂).inv.app
            ((Scheme.Modules.pullback r).obj M₀)
        ≫ (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
            ((Scheme.Modules.pullbackComp c₂ r).hom.app M₀
              ≫ (Scheme.Modules.pullbackIsoOfRestrictIso d eB
                  (AlgebraicGeometry.Proj.map φ hφ) hfac₂).hom
              ≫ twistMap φ hφ n
              ≫ (((Scheme.Modules.restrictFunctorIsoPullback c₂).app N').symm ≪≫ e'₂).inv)
        ≫ (Scheme.Modules.pullbackComp (AlgebraicGeometry.Proj.map ψ hψ) c₂).hom.app N'
        ≫ (Scheme.Modules.pullbackCongr hkc).hom.app N'
      = (Scheme.Modules.pullbackComp c₁ r).hom.app M₀
        ≫ (Scheme.Modules.pullbackIsoOfRestrictIso d eB
            (AlgebraicGeometry.Proj.map χ hχ) hfac₁).hom
        ≫ twistMap χ hχ n
        ≫ (((Scheme.Modules.restrictFunctorIsoPullback c₁).app N').symm ≪≫ e'₁).inv :=
  Scheme.Modules.chartMember_pullback_eq r d eB c₂ e'₂
    (AlgebraicGeometry.Proj.map ψ hψ) hkc e'₁
    (AlgebraicGeometry.Proj.map φ hφ) hfac₂
    (Stacks.ProjModuleComparison.projMapComp φ hφ ψ hψ χ hχ hc) hfac₁
    (twistMap φ hφ n) (twistMap χ hχ n) (twistMap ψ hψ n)
    hν (map_twistMap_comp_eq φ hφ ψ hψ hχ n hc)

end MemberNested

end Stacks.ProjTwistComparison

end
