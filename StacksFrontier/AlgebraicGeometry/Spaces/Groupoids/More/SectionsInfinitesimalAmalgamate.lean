module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalLiftGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftSections

/-!
# The chartwise lifts of an infinitesimal section amalgamate into a global one

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `Γ₀` be the set of [Stacks Project, Tag 0CKB] of sections of the
source agreeing with the unit on `U₀`, let `δ ∈ Γ₀` and let `θ` be an `𝒪_{U₀}`-linear map
`e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`.

`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalLift.lean` shows that
the solution `g` of the lifting problem obtained by moving the transported comorphism of `δ` by
the derivation attached to `θ` induces, over every affine chart diagram, a section of the sheaf
of lifts, and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsInfinitesimalLiftGlue.lean` shows
that those sections are compatible.  This file **amalgamates them into an element of `Γ₀`**.

It is the groupoid instance of
`AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom`, read at the thickening
`U₀ ⊆ U`, the comorphism `δ`, the morphism `s : R ⟶ U`, the base `U` with `p = 𝟙_U` and
`q = s`, and the lift `e|_{U₀} : U₀ ⟶ R`: its sheaf of lifts is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsLiftSheaf` on the nose, so the
morphism `U ⟶ R` it produces is a section of the source agreeing with the unit on `U₀`, that is
an element of `Γ₀`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isChartLift_infinitesimalSectionLiftChartSiteHom`:
  the morphism of charts attached to the moved solution over an affine chart of `R` carrying an
  affine chart diagram over the source is a section of the sheaf of lifts — the two clauses of
  `AlgebraicGeometry.Space.IsChartLift` in the spelling the gluing asks for, with the index over
  a chart of `U` replaced by the chart diagram the chart carries.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_infinitesimalSection_eq_chartSiteHom`:
  **there is an element `ε` of `Γ₀` whose restriction to every chart of `U` carrying an index
  over an affine chart of `R` is the morphism of charts attached to the moved solution.**

## What this leaves

The existence clause of Equation [Stacks Project, Tag 0CKE] now needs only the identification of
the difference of `ε` from `δ` with `θ`: the comorphism of `ε` agrees with the moved solution `g`
over every affine chart diagram, hence everywhere, and the descended difference of `g` from the
comorphism of `δ` is `θ` by
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom`.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)
  (hU₀ : IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- **The morphism of charts attached to the moved solution is a section of the sheaf of lifts**,
stated over an affine chart `V` of `R` carrying an affine chart diagram over the source rather
than over an index of the base change of the source. -/
theorem isChartLift_infinitesimalSectionLiftChartSiteHom (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) (V : Space.SmallEtale C S hS G.arrows.1)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj V))]
    (j : StructuredArrow (op (chartBaseChange C S hS δ.1.1 V))
      (comparisonFunctor C S hS G.objects).op)
    (ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj j.right.unop ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.1).obj V)
    (hV : HasAffineChartDiagram C S hS G.source V)
    (hψ : (BigFppfOver.toScheme C S hS).map ψ =
      thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
        (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)) V j) :
    Space.IsChartLift C S hS (𝟙 G.objects) G.source
      (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom j.right.unop
      (yoneda.map ψ ≫ V.1.hom) := by
  obtain ⟨-, V', q, hq, hV'aff⟩ := hV
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
    ((Space.SmallEtale.toOver C S hS G.objects.1).obj V')) := hV'aff
  let i := indexOfChartDiagram C S hS G.source (⟨V, V', q, hq.symm⟩ :
    ChartDiagram C S hS G.arrows.1 G.objects.1 G.source.hom)
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj i.right.unop)) :=
    (inferInstance : IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj V)))
  exact ⟨comp_source_eq_of_infinitesimalSectionLiftChartSiteHom G U₀ hU₀ δ θ V' i j ψ hψ,
    fun Ww k t hkt ↦
      comp_restriction_eq_of_infinitesimalSectionLiftChartSiteHom G U₀ hU₀ δ θ V' i j ψ hψ Ww k t
        hkt⟩

include hU₀ in
/-- **The chartwise lifts of `δ` moved by `θ` amalgamate into an element of `Γ₀`.**

There is a section `ε` of the source agreeing with the unit on `U₀` whose restriction to any
étale chart of `U` carrying an index over any affine étale chart `V` of `R` is the morphism of
charts into `V` which the moved solution induces.

This is `AlgebraicGeometry.Space.exists_hom_eq_thickeningLiftChartSiteHom` at the thickening
`U₀ ⊆ U`, the comorphism `δ` and the morphism `s : R ⟶ U`: its hypothesis on the regular
functions read from `U` is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.app_infinitesimalSectionLiftComorphism_eq` and its
hypothesis on the chartwise morphisms being lifts is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isChartLift_infinitesimalSectionLiftChartSiteHom`.
The morphism it produces lies over `U` and restricts to the unit on `U₀`, which is exactly
membership in `Γ₀`. -/
theorem exists_infinitesimalSection_eq_chartSiteHom (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) :
    ∃ ε : InfinitesimalSections G U₀,
      ∀ (V : Space.SmallEtale C S hS G.arrows.1)
        [IsAffine ((BigFppfOver.toScheme C S hS).obj
          ((Space.SmallEtale.toOver C S hS G.arrows.1).obj V))]
        (j : StructuredArrow (op (chartBaseChange C S hS δ.1.1 V))
          (comparisonFunctor C S hS G.objects).op)
        (ψ : (Space.SmallEtale.toOver C S hS G.objects.1).obj j.right.unop ⟶
          (Space.SmallEtale.toOver C S hS G.arrows.1).obj V),
        (BigFppfOver.toScheme C S hS).map ψ =
          thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
            (thickeningLiftOfIndex C S hS U₀ δ.1.1
              (restrictedUnit G U₀ ≫
                subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
              (comp_eq_restrictedUnit_comp G U₀ δ.2)
              (liftRestrictedSharpThroughThickening C S hS U₀
                (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
                (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)) V j →
        j.right.unop.1.hom ≫ ε.1.1.hom = yoneda.map ψ ≫ V.1.hom := by
  obtain ⟨ε, hsrc, hres, hchart⟩ := Space.exists_hom_eq_thickeningLiftChartSiteHom C S hS U₀
    hU₀.1 δ.1.1
    (thickeningLiftOfIndex C S hS U₀ δ.1.1
      (restrictedUnit G U₀ ≫
        subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
      (comp_eq_restrictedUnit_comp G U₀ δ.2)
      (liftRestrictedSharpThroughThickening C S hS U₀
        (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
        (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g))
    G.source (app_infinitesimalSectionLiftComorphism_eq G U₀ hU₀ δ θ) (𝟙 G.objects) G.source
    (subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G).hom
    fun V _ j ψ hV hψ ↦
      isChartLift_infinitesimalSectionLiftChartSiteHom G U₀ hU₀ δ θ V j ψ hV hψ
  exact ⟨⟨⟨ObjectProperty.homMk ε, ObjectProperty.hom_ext _ hsrc⟩,
    ObjectProperty.hom_ext _ hres⟩, hchart⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
