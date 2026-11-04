module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeLocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat

/-!
# The projective bundle of a module of rank `n + 1` is étale-locally `ℙⁿ`

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module which is
finite locally free of rank `n + 1` in the sense of the rank clause of Stacks 0409. The
projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle is étale locally on `X`, and then Zariski
locally, the projective space `ℙⁿ`: over every étale scheme chart `V` of `X` the projection of
the chart bundle `𝐏(ℰ|_V) ⟶ V` is Zariski-locally on `V` the projective space `ℙⁿ`, and over
the presenting chart `U` of `X` this chart bundle is the fibre product `𝐏(ℰ) ×_X U`. In
particular every fibre of `π` over a point of a chart is the projective space `ℙⁿ` over the
residue field of that point.

Over a chart this is the scheme statement
(`Stacks.ProjectiveBundle.isLocallyProjectiveSpace_toBase`) for the restriction `ℰ|_V`, which
has rank `n + 1` (`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_chartBundleModule`),
transported along the comparison of the two presentations of the scheme projective bundle.

## Main results

* `AlgebraicGeometry.Space.isLocallyProjectiveSpace_chartBundleToChart`: over every étale chart
  `V`, the chart bundle `𝐏(ℰ|_V) ⟶ V` is Zariski-locally `ℙⁿ`.
* `AlgebraicGeometry.Space.exists_etaleChart_isLocallyProjectiveSpace`: **there is a
  surjective étale scheme chart `U ⟶ X` over which `𝐏(ℰ) ×_X U ⟶ U` is Zariski-locally `ℙⁿ`.**

## References

* [Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite] (n : ℕ)
  (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E (n + 1))

include hr

/-- **Over every étale chart `V` of `X`, the projection of the chart bundle `𝐏(ℰ|_V) ⟶ V` is
Zariski-locally on `V` the projective space `ℙⁿ`.** -/
theorem isLocallyProjectiveSpace_chartBundleToChart (V : SmallEtale B S hS X.1) :
    Stacks.ProjectiveBundle.IsLocallyProjectiveSpace (chartBundleToChart E V) n := by
  have := isFiniteLocallyFreeOfRank_chartBundleModule E n hr V
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (chartBundleModule E V) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (n + 1)
  have hqc := Stacks.Chow.bundlePieces (chartBundleModule E V)
  obtain ⟨b, hb⟩ := projectiveBundlePresentationsAgree (chartBundleModule E V) hqc
  have heq : chartBundleToChart E V = b.symm.hom ≫ (Stacks.SymGraded.schemeProjectiveBundle
      (chartBundleModule E V) hqc).toBase := by
    rw [Iso.symm_hom, Iso.eq_inv_comp]
    exact hb
  rw [heq]
  exact (Stacks.ProjectiveBundle.isLocallyProjectiveSpace_toBase (chartBundleModule E V) hqc
    n).of_iso b.symm

/-- **The projective bundle of a module of rank `n + 1` is étale-locally on `X` and then
Zariski-locally the projective space `ℙⁿ`**: there is a surjective étale scheme chart
`a : U ⟶ X` and a cartesian square exhibiting a scheme `P'` as `𝐏(ℰ) ×_X U`, whose projection
`P' ⟶ U` is Zariski-locally on `U` the projective space `ℙⁿ`. -/
theorem exists_etaleChart_isLocallyProjectiveSpace
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    ∃ (U P' : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
      (a' : yoneda.obj P' ⟶ (projectiveBundle E hfree).1) (p : P' ⟶ U),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a ∧
        IsPullback a' (yoneda.map p) (projectiveBundleProj E hfree).hom a ∧
        Stacks.ProjectiveBundle.IsLocallyProjectiveSpace ((BigFppfOver.toScheme B S hS).map p) n :=
  ⟨_, _, (presentationChart (projectiveBundlePresentation X)).obj.hom,
    projectiveBundleChart E hfree,
    (projectiveBundleChartFamily E hfree).siteToChart
      (presentationChart (projectiveBundlePresentation X)),
    (presentationChart (projectiveBundlePresentation X)).property,
    surjective_projectiveBundlePresentation X,
    isPullback_projectiveBundleProj E hfree,
    isLocallyProjectiveSpace_chartBundleToChart E n hr _⟩

end AlgebraicGeometry.Space

end
