module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftGlue

/-!
# The chartwise lifts of an infinitesimal section agree on a common refinement

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be a
first order thickening, let `Γ₀` be the set of [Stacks Project, Tag 0CKB] of sections of the
source agreeing with the unit on `U₀`, let `δ ∈ Γ₀` and let `θ` be an `𝒪_{U₀}`-linear map
`e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}`.

The moved solution `g` of the lifting problem, obtained from the transported comorphism of `δ`
and the derivation attached to `θ`, induces over every affine chart diagram a section of the sheaf
of lifts of Equation [Stacks Project, Tag 0CKE]. The section of `R` which it induces over an étale
chart of `U` does not depend on the affine chart diagram it is read on. This is the groupoid
instance of `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_eq`, whose hypothesis
is that the comorphism agrees with the transported comorphism of `δ` on the regular functions
read from `U` along the source.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.app_infinitesimalSectionLiftComorphism_eq`: the
  moved solution, read on the site of `R` at the tautological index, agrees with the comorphism
  of `δ` read through the thickening on every regular function read from `U` along the source.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.yoneda_map_infinitesimalSectionLiftChartSiteHom_eq`:
  **the chartwise lifts agree.**  Two affine chart diagrams over `δ` give one and the same
  morphism from any étale chart of `U` lying over both into `R`.

## References

* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
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
/-- **The moved solution agrees with the comorphism of `δ` read through the thickening on every
regular function read from `U` along the source.**

This is the hypothesis under which the chart morphism attached to a comorphism is a morphism of
the big fppf category over `S`, here in the spelling the chart reading uses — the transport of
`AlgebraicGeometry.Space.thickeningLiftOfIndex` being invertible on the value over a chart, by
`AlgebraicGeometry.Space.app_thickeningLiftOfIndex_congr`, and carrying the comorphism read at
the index `e₀ ≫ j` to the comorphism read at the composite, by
`AlgebraicGeometry.Space.thickeningLiftOfIndex_structureSharpThroughThickeningAt`. -/
theorem app_infinitesimalSectionLiftComorphism_eq (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀) (V : Space.SmallEtale C S hS G.arrows.1)
    (s : ToType ((structureRingSheafInverseImage C S hS G.source).obj.obj (op V))) :
    (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)).hom.app (op V)
        ((structureSharpRingInverseImage C S hS G.source).hom.app (op V) s) =
      (structureSharpThroughThickening C S hS U₀ δ.1.1).hom.app (op V)
        ((structureSharpRingInverseImage C S hS G.source).hom.app (op V) s) :=
  app_thickeningLiftOfIndex_eq_structureSharpThroughThickening C S hS U₀ δ.1.1
    (restrictedUnit G U₀ ≫
      subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
    (comp_eq_restrictedUnit_comp G U₀ δ.2)
    (liftRestrictedSharpThroughThickening C S hS U₀
      (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)
    G.source
    (fun V' s' ↦ app_liftRestrictedSharpThroughThickening_eq C S hS U₀
      (preimageSubspace C S hS G.source U₀) δ.1.1 (restrictedUnit G U₀)
      (comp_eq_restrictedUnit_comp G U₀ δ.2) G.source
      (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g
      (inverseImage_source_comp_infinitesimalSectionLiftData_g_eq G U₀ hU₀ δ θ)
      (op V') s')
    V s

include hU₀ in
/-- **The chartwise lifts of `δ` moved by `θ` agree on a common refinement.**

Let `V₁`, `V₂` be affine étale charts of `R`, let `j₁`, `j₂` be étale scheme charts of `U` above
`U ×_R V₁` and `U ×_R V₂`, and let `ψ₁`, `ψ₂` be the morphisms of the site which the moved
solution induces there — the morphisms whose existence
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_infinitesimalSectionLiftChartSiteHom`
asserts.  Then for any étale chart `K` of `U` lying over the two charts the indices carry, the
two morphisms `K ⟶ R` obtained by restriction are equal.

This is `AlgebraicGeometry.Space.yoneda_map_thickeningLiftChartSiteHom_eq` for the source
`s : R ⟶ U` and the comorphism
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionLiftComorphism`, whose
hypothesis is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.app_infinitesimalSectionLiftComorphism_eq`.

In particular the chartwise sections of the sheaf of lifts of
`mem_infinitesimalSectionsLiftSheaf_of_infinitesimalSectionLiftChartSiteHom` are a compatible
family. -/
theorem yoneda_map_infinitesimalSectionLiftChartSiteHom_eq (δ : InfinitesimalSections G U₀)
    (θ : InfinitesimalSectionsHom G U₀)
    {V₁ V₂ : Space.SmallEtale C S hS G.arrows.1}
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj V₁))]
    [IsAffine ((BigFppfOver.toScheme C S hS).obj
      ((Space.SmallEtale.toOver C S hS G.arrows.1).obj V₂))]
    (j₁ : StructuredArrow (op (chartBaseChange C S hS δ.1.1 V₁))
      (comparisonFunctor C S hS G.objects).op)
    (j₂ : StructuredArrow (op (chartBaseChange C S hS δ.1.1 V₂))
      (comparisonFunctor C S hS G.objects).op)
    (ψ₁ : (Space.SmallEtale.toOver C S hS G.objects.1).obj j₁.right.unop ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.1).obj V₁)
    (hψ₁ : (BigFppfOver.toScheme C S hS).map ψ₁ =
      thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
        (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)) V₁ j₁)
    (ψ₂ : (Space.SmallEtale.toOver C S hS G.objects.1).obj j₂.right.unop ⟶
      (Space.SmallEtale.toOver C S hS G.arrows.1).obj V₂)
    (hψ₂ : (BigFppfOver.toScheme C S hS).map ψ₂ =
      thickeningLiftChartHom C S hS U₀ hU₀.1 δ.1.1
        (thickeningLiftOfIndex C S hS U₀ δ.1.1
          (restrictedUnit G U₀ ≫
            subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
          (comp_eq_restrictedUnit_comp G U₀ δ.2)
          (liftRestrictedSharpThroughThickening C S hS U₀
            (preimageSubspace C S hS G.source U₀) (restrictedUnit G U₀)
            (infinitesimalSectionLiftData G U₀ hU₀ δ θ).g)) V₂ j₂)
    (K : Space.SmallEtale C S hS G.objects.1) (n₁ : K ⟶ j₁.right.unop)
    (n₂ : K ⟶ j₂.right.unop) :
    yoneda.map ((Space.SmallEtale.toOver C S hS G.objects.1).map n₁) ≫
        yoneda.map ψ₁ ≫ V₁.1.hom =
      yoneda.map ((Space.SmallEtale.toOver C S hS G.objects.1).map n₂) ≫
        yoneda.map ψ₂ ≫ V₂.1.hom :=
  yoneda_map_thickeningLiftChartSiteHom_eq C S hS U₀ hU₀.1 δ.1.1 _ G.source
    (app_infinitesimalSectionLiftComorphism_eq G U₀ hU₀ δ θ) j₁ j₂ ψ₁ hψ₁ ψ₂ hψ₂ K n₁ n₂

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
