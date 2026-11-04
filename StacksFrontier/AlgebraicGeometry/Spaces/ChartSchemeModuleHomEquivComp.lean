module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv

/-!
# The Hom-set transport of a chart restriction is multiplicative

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `A` be an étale scheme
chart of `X` and let `M`, `L`, `N` be quasi-coherent `𝒪_X`-modules.
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` identifies morphisms of the restrictions to
the slice of the small étale site of `X` at `A` with morphisms of the chart restrictions on the
chart's scheme.  This file proves that the identification carries a composite to the composite of
the identifications, and specializes that to precomposition with a morphism of quasi-coherent
`𝒪_X`-modules.

That specialization is what turns the degreewise identifications
`AlgebraicGeometry.Space.chartIdealPowHomEquiv` of the direct system `k ↦ Hom(ℐᵏ𝒢|_A, ℱ|_A)` with
the direct system of the first display of [Stacks, Tag 01YB] on the chart's scheme into an
identification *of direct systems*: the transition maps on both sides are precomposition with a
monomorphism, hence not injective, so an agreement which holds in the colimit does not hold at
the degree a given `k` names.

## Main results

* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv_comp`,
  `AlgebraicGeometry.Space.chartSmallEtaleQcohHomEquiv_symm_comp`,
  `AlgebraicGeometry.Space.chartSchemeQcohHomEquiv_comp` and
  `AlgebraicGeometry.Space.chartSchemeModuleObjHomEquiv_comp`: each of the four legs of the
  transport carries a composite to a composite.
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_comp`: **the Hom-set transport of the chart
  restriction carries a composite to the composite of the transports.**
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_overFunctor_map_comp`: **the naturality of
  the Hom-set transport under precomposition with a morphism of quasi-coherent `𝒪_X`-modules.**

## Implementation notes

**Every leg is the Hom-set bijection of a fully faithful functor, and that is the whole content.**
Three of the four legs are `CategoryTheory.Functor.FullyFaithful.homEquiv` in the forward
direction, where the bijection *is* the action on morphisms and
`CategoryTheory.Functor.map_comp` applies verbatim; the remaining one,
`AlgebraicGeometry.Space.chartSmallEtaleQcohHomEquiv`, is used backwards, and there the
multiplicativity is `CategoryTheory.Functor.FullyFaithful.preimage_comp`.  No naturality square
of any of the four equivalences is needed, and none is used.

**The three objects of the middle leg are supplied by name.**  The sources and targets of
`CategoryTheory.Functor.FullyFaithful.preimage_comp` are implicit and are not determined by the
two morphisms, whose types are stated at the definitionally equal spelling
`AlgebraicGeometry.Space.chartSmallEtaleRestriction` rather than as values of the inclusion of the
full subcategory.

No declaration here carries a `stacks` tag: this is an input to the reduction of
[Stacks, Tag 07UM] to a chart, not an assertion of any tag.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M L N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hL : L.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite)

/-! ### The four legs -/

/-- The restriction to the small étale site of a chart carries a composite to a composite: it is
the action on morphisms of the functor of
`AlgebraicGeometry.Space.chartModuleReindexEquivalence`. -/
theorem chartSmallEtaleRestrictionHomEquiv_comp (A : SmallEtale B S hS X.1)
    (u : M.over A ⟶ L.over A) (α : L.over A ⟶ N.over A) :
    chartSmallEtaleRestrictionHomEquiv B S hS X M N A (u ≫ α) =
      chartSmallEtaleRestrictionHomEquiv B S hS X M L A u ≫
        chartSmallEtaleRestrictionHomEquiv B S hS X L N A α :=
  (chartModuleReindexEquivalence B S hS X A).functor.map_comp u α

/-- The passage from a morphism of the restrictions to the small étale site of a chart to a
morphism of the quasi-coherent restrictions carries a composite to a composite: it is
`CategoryTheory.Functor.preimage` along the inclusion of a full subcategory. -/
theorem chartSmallEtaleQcohHomEquiv_symm_comp (A : SmallEtale B S hS X.1)
    (a : chartSmallEtaleRestriction B S hS X M A ⟶ chartSmallEtaleRestriction B S hS X L A)
    (b : chartSmallEtaleRestriction B S hS X L A ⟶ chartSmallEtaleRestriction B S hS X N A) :
    (chartSmallEtaleQcohHomEquiv B S hS X M N hM hN A).symm (a ≫ b) =
      (chartSmallEtaleQcohHomEquiv B S hS X M L hM hL A).symm a ≫
        (chartSmallEtaleQcohHomEquiv B S hS X L N hL hN A).symm b :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (chartStructureRingSheaf B S hS X A)).fullyFaithfulι.preimage_comp
      (X := chartSmallEtaleQcoh B S hS X M hM A) (Y := chartSmallEtaleQcoh B S hS X L hL A)
      (Z := chartSmallEtaleQcoh B S hS X N hN A) a b

/-- Descent, Proposition 03DX (2) and the representable case of Stacks 03ED carry a composite to a
composite: the leg is the action on morphisms of the inverse of an equivalence. -/
theorem chartSchemeQcohHomEquiv_comp (A : SmallEtale B S hS X.1)
    (a : chartSmallEtaleQcoh B S hS X M hM A ⟶ chartSmallEtaleQcoh B S hS X L hL A)
    (b : chartSmallEtaleQcoh B S hS X L hL A ⟶ chartSmallEtaleQcoh B S hS X N hN A) :
    chartSchemeQcohHomEquiv B S hS X M N hM hN A (a ≫ b) =
      chartSchemeQcohHomEquiv B S hS X M L hM hL A a ≫
        chartSchemeQcohHomEquiv B S hS X L N hL hN A b :=
  (representedQuasicoherentSchemeEquivalence B S hS
    ((SmallEtale.toOver B S hS X.1).obj A)).inverse.map_comp a b

/-- The inclusion of the quasi-coherent modules on the chart's scheme carries a composite to a
composite. -/
theorem chartSchemeModuleObjHomEquiv_comp (A : SmallEtale B S hS X.1)
    (a : chartSchemeQcoh B S hS X M hM A ⟶ chartSchemeQcoh B S hS X L hL A)
    (b : chartSchemeQcoh B S hS X L hL A ⟶ chartSchemeQcoh B S hS X N hN A) :
    chartSchemeModuleObjHomEquiv B S hS X M N hM hN A (a ≫ b) =
      chartSchemeModuleObjHomEquiv B S hS X M L hM hL A a ≫
        chartSchemeModuleObjHomEquiv B S hS X L N hL hN A b :=
  (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).ι.map_comp a b

/-! ### The transport -/

/-- **The Hom-set transport of the chart restriction carries a composite to the composite of the
transports.**  Each of its four legs does, and the transport is their composite. -/
theorem chartSchemeModuleHomEquiv_comp (A : SmallEtale B S hS X.1)
    (u : M.over A ⟶ L.over A) (α : L.over A ⟶ N.over A) :
    chartSchemeModuleHomEquiv B S hS X M N hM hN A (u ≫ α) =
      chartSchemeModuleHomEquiv B S hS X M L hM hL A u ≫
        chartSchemeModuleHomEquiv B S hS X L N hL hN A α :=
  (congrArg (fun z : chartSmallEtaleRestriction B S hS X M A ⟶
          chartSmallEtaleRestriction B S hS X N A =>
        chartSchemeModuleObjHomEquiv B S hS X M N hM hN A
          (chartSchemeQcohHomEquiv B S hS X M N hM hN A
            ((chartSmallEtaleQcohHomEquiv B S hS X M N hM hN A).symm z)))
      (chartSmallEtaleRestrictionHomEquiv_comp B S hS X M L N A u α)).trans
    ((congrArg (fun z : chartSmallEtaleQcoh B S hS X M hM A ⟶
            chartSmallEtaleQcoh B S hS X N hN A =>
          chartSchemeModuleObjHomEquiv B S hS X M N hM hN A
            (chartSchemeQcohHomEquiv B S hS X M N hM hN A z))
        (chartSmallEtaleQcohHomEquiv_symm_comp B S hS X M L N hM hL hN A _ _)).trans
      ((congrArg (fun z : chartSchemeQcoh B S hS X M hM A ⟶ chartSchemeQcoh B S hS X N hN A =>
            chartSchemeModuleObjHomEquiv B S hS X M N hM hN A z)
          (chartSchemeQcohHomEquiv_comp B S hS X M L N hM hL hN A _ _)).trans
        (chartSchemeModuleObjHomEquiv_comp B S hS X M L N hM hL hN A _ _)))

/-- **The naturality of the Hom-set transport of the chart restriction under precomposition with a
morphism of quasi-coherent `𝒪_X`-modules.**  Restricting `u : M ⟶ L` to the slice at a chart,
precomposing with it and transporting is transporting and then precomposing with the chart
restriction of `u`.

This is `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_comp` with the first factor coming from
a global morphism, where `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_restrictionFunctor_map`
identifies its transport with the action of
`AlgebraicGeometry.Space.chartSchemeModuleFunctor` on morphisms. -/
theorem chartSchemeModuleHomEquiv_overFunctor_map_comp (A : SmallEtale B S hS X.1)
    {M' L' : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (u : M' ⟶ L')
    (α : L'.obj.over A ⟶ N.over A) :
    chartSchemeModuleHomEquiv B S hS X M'.obj N M'.property hN A
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) A).map u.hom ≫ α) =
      (chartSchemeModuleFunctor B S hS X A).map u ≫
        chartSchemeModuleHomEquiv B S hS X L'.obj N L'.property hN A α :=
  (chartSchemeModuleHomEquiv_comp B S hS X M'.obj L'.obj N M'.property L'.property hN A _ α).trans
    (congrArg
      (fun z : chartSchemeModule B S hS X M'.obj M'.property A ⟶
            chartSchemeModule B S hS X L'.obj L'.property A =>
        z ≫ chartSchemeModuleHomEquiv B S hS X L'.obj N L'.property hN A α)
      (chartSchemeModuleHomEquiv_restrictionFunctor_map B S hS X A u))

end AlgebraicGeometry.Space

end
