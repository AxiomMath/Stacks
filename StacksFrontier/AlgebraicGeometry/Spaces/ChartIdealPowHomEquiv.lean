module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushComponentFormula

/-!
# Morphisms out of `ℐᵏ𝒢` at a chart and on the chart's scheme

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals, let `𝒢` and `ℱ` be quasi-coherent `𝒪_X`-modules and let `A` be an
étale scheme chart of `X`.  This file identifies the `k`-th term

`Hom_{𝒪_X|_A}(ℐᵏ𝒢|_A, ℱ|_A)`

of the direct system of the first display of [Stacks, Tag 07UM], restricted to the slice of the
small étale site of `X` at `A`, with the `k`-th term

`Hom_{𝒪_{chartScheme A}}(Iᵏ · 𝒢|_A, ℱ|_A)`

of the direct system of the first display of [Stacks, Tag 01YB] on the chart's scheme.  This is
Step 3 of [Stacks, Tag 07UM], degreewise.

The identification is the composite of three bijections: the Hom-set transport
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` of the chart restriction, conjugation by the
isomorphism `AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` between the chosen and the
direct-image spellings of the chart restriction, and conjugation by
`AlgebraicGeometry.Space.chartPushFactorIso`, which says that the chart restriction of `ℐᵏ𝒢` *is*
`Iᵏ` times the chart restriction of `𝒢`.

## Main definitions

* `AlgebraicGeometry.Space.chartIdealPowHomEquiv` is the identification above.

## Main results

* `AlgebraicGeometry.Space.chartIdealPowHomEquiv_symm_apply`: its inverse is
  `AlgebraicGeometry.Space.chartAlpha`, the map which reads a morphism out of `Iᵏ` times the chart
  restriction of `𝒢` as a morphism of the restrictions to the slice at the chart.
* `AlgebraicGeometry.Space.bijective_chartAlpha`: **`AlgebraicGeometry.Space.chartAlpha` is
  bijective.**  Together with `AlgebraicGeometry.Space.exists_homRestrict_eq_chartThetaOver` this
  is the chart half of the surjectivity clause of [Stacks, Tag 07UM] in the form the descent from
  the chart consumes, and it is the first consumer of
  `AlgebraicGeometry.Space.isIso_chartPushFactor`.

## Implementation notes

**The identification is degreewise, and that is not yet enough.**  The transition maps of the two
direct systems are precomposition with monomorphisms, hence not injective, so an agreement which
holds in the colimit does not hold at the degree a given `k` names; the compatibility of the two
systems' transition maps is `AlgebraicGeometry.Space.chartPushFactor_comp_idealPowSmulMap`, and
turning the degreewise bijections below into an isomorphism of direct systems additionally needs
the naturality of `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` under precomposition with a
morphism of quasi-coherent `𝒪_X`-modules, which the tree does not have.

**The two conjugations are taken in different categories, and that is deliberate.**
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` is an isomorphism of
`CategoryTheory.SheafOfModules` over the structure sheaf of the chart's scheme — the pinned
spelling which makes its components computable — whereas
`AlgebraicGeometry.Space.chartPushFactorIso` is one of `AlgebraicGeometry.Scheme.Modules`.  The
two `CategoryTheory.Category` instances are definitionally equal, and `CategoryTheory.Iso.homCongr`
composes across them without a transport; what must be avoided is a *rewrite* across them.
`AlgebraicGeometry.Space.chartIdealPowHomEquiv_symm_apply` therefore reassociates with
`CategoryTheory.Category.assoc` after a `change` that fixes the reading, rather than rewriting
inside the composite.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)

/-- **The `k`-th term of the direct system of [Stacks, Tag 07UM] at a chart is the `k`-th term of
the direct system of [Stacks, Tag 01YB] on the chart's scheme.**  A morphism `ℐᵏ𝒢|_A ⟶ ℱ|_A` of
the restrictions to the slice of the small étale site of `X` at an étale scheme chart `A` is the
same thing as a morphism `Iᵏ · 𝒢|_A ⟶ ℱ|_A` of modules on the chart's scheme. -/
def chartIdealPowHomEquiv (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hGq : G.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite) (k : ℕ)
    (hIGq : (idealPowModule I k G).IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) :
    ((idealPowModule I k G).over A ⟶ F.over A) ≃
      (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
          (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
        chartPush B S hS X F A) :=
  ((chartSchemeModuleHomEquiv B S hS X (idealPowModule I k G) F hIGq hFq A).trans
      (Iso.homCongr (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G) hIGq A)
        (chartSchemeModuleIsoChartPush B S hS X F hFq A))).trans
    (Iso.homCongr (chartPushFactorIso B S hS X I hIc G hIq hGq A k)
      (Iso.refl (chartPush B S hS X F A)))

/-- **The inverse of `AlgebraicGeometry.Space.chartIdealPowHomEquiv` is
`AlgebraicGeometry.Space.chartAlpha`.** -/
theorem chartIdealPowHomEquiv_symm_apply (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hFq : F.IsQuasicoherentOnSite) (hG : IsCoherent B S hS X.1 X.2 G)
    (A : SmallEtale B S hS X.1) (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A) :
    (chartIdealPowHomEquiv B S hS X I hIc G F hIq hG.toIsQuasicoherentOnSite hFq k
        (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) A).symm φ =
      chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A k φ := by
  refine congrArg (chartSchemeModuleHomEquiv B S hS X (idealPowModule I k G) F
    (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) hFq A).symm ?_
  show (chartSchemeModuleIsoChartPush B S hS X (idealPowModule I k G)
        (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) A).hom ≫
      ((chartPushFactorIso B S hS X I hIc G hIq hG.toIsQuasicoherentOnSite A k).hom ≫ φ ≫
        (Iso.refl (chartPush B S hS X F A)).inv) ≫
      (chartSchemeModuleIsoChartPush B S hS X F hFq A).inv = _
  rw [chartPushFactorIso_hom, Iso.refl_inv, Category.comp_id, Category.assoc]

/-- **`AlgebraicGeometry.Space.chartAlpha` is bijective**: every morphism `ℐᵏ𝒢|_A ⟶ ℱ|_A` of the
restrictions to the slice of the small étale site of `X` at an étale scheme chart comes from a
unique morphism `Iᵏ · 𝒢|_A ⟶ ℱ|_A` on the chart's scheme. -/
theorem bijective_chartAlpha (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (hFq : F.IsQuasicoherentOnSite) (hG : IsCoherent B S hS X.1 X.2 G)
    (A : SmallEtale B S hS X.1) (k : ℕ) :
    Function.Bijective (chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A k) :=
  have hfun : chartAlpha B S hS X I hIc G F hZ hN hIq hFq hG A k =
      (chartIdealPowHomEquiv B S hS X I hIc G F hIq hG.toIsQuasicoherentOnSite hFq k
        (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) A).symm :=
    funext fun φ =>
      (chartIdealPowHomEquiv_symm_apply B S hS X I hIc G F hZ hN hIq hFq hG A k φ).symm
  hfun ▸ (chartIdealPowHomEquiv B S hS X I hIc G F hIq hG.toIsQuasicoherentOnSite hFq k
    (isQuasicoherentOnSite_idealPowModule B S hS X I G hZ hN hIq hG k) A).symm.bijective

end AlgebraicGeometry.Space

end
