module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleFunctorial

/-!
# The Hom-sets of the chart restriction of a quasi-coherent module on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `A` be an
étale scheme chart of `X` and let `M`, `N` be quasi-coherent `𝒪_X`-modules.
`AlgebraicGeometry.Space.chartSchemeModule` transports a quasi-coherent `𝒪_X`-module to a
quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the chart's scheme, by composing the
localization of Stacks 04M0 at the chart with Descent, Proposition 03DX (2) for a scheme.

This file identifies the Hom-sets across that transport: morphisms of the restrictions of `M`
and `N` to the slice of the small étale site of `X` at `A` are exactly morphisms of the
`AlgebraicGeometry.Scheme.Modules` which `M` and `N` become on the chart's scheme.  This is the
transport along which a statement about morphisms of quasi-coherent modules on a *scheme* — such
as the scheme case of Stacks 01YB — becomes a statement about morphisms of the restrictions to a
chart of an algebraic space.

## Main definitions

* `Stacks.SheafOfModules.reindexHomEquiv`: reindexing along an equivalence of ringed sites is a
  bijection on Hom-sets.
* `AlgebraicGeometry.Space.chartModuleReindexEquivalence`: the equivalence of Stacks 04M0 at a
  chart, read on the module categories.
* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv`,
  `AlgebraicGeometry.Space.chartSmallEtaleQcohHomEquiv`,
  `AlgebraicGeometry.Space.chartSchemeQcohHomEquiv`,
  `AlgebraicGeometry.Space.chartSchemeModuleObjHomEquiv`: the four legs of the transport.
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv`: **the Hom-sets of the chart restriction
  agree with the Hom-sets on the slice of the small étale site of `X` at the chart.**

## Main results

* `Stacks.SheafOfModules.reindexEquivalence_functor`,
  `Stacks.SheafOfModules.reindexEquivalence_inverse`,
  `Stacks.SheafOfModules.reindexEquivalence_functor_obj` and
  `Stacks.SheafOfModules.reindexEquivalence_functor_map`: the two directions of
  `Stacks.SheafOfModules.reindexEquivalence` are the two pushforwards, definitionally.
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_restrictionFunctor_map`: the forward
  direction of the transport is the action on morphisms of
  `AlgebraicGeometry.Space.chartSchemeModuleFunctor`.
* `AlgebraicGeometry.Space.exists_chartSchemeModuleHomEquiv`: **every morphism of the chart
  restrictions comes from a morphism on the slice at the chart**, which is the direction in which
  a surjectivity statement proved on the chart's scheme is transported back.

## Implementation notes

**Every leg after the restriction to the slice is an equivalence, and that is the whole content.**
`AlgebraicGeometry.Space.chartSchemeRestrictionFunctor` is the composite of
`CategoryTheory.SheafOfModules.overFunctor`, which restricts to the slice at the chart and is
*not* fully faithful, with the reindexing along the comparison equivalence of Stacks 04M0, which
is.  So the transport is a bijection on Hom-sets only after the restriction to the slice has been
taken, and the statements below are therefore indexed by `M.over A` and `N.over A` rather than by
`M` and `N`.  No fullness statement for
`AlgebraicGeometry.Space.chartSchemeRestrictionFunctor` or
`AlgebraicGeometry.Space.chartSchemeQcohFunctor` is possible, and none is claimed.

The three remaining legs are: the reindexing of Stacks 04M0
(`Stacks.SheafOfModules.reindexEquivalence`, whose functor is a pushforward on the nose, so that
its value at a module is `AlgebraicGeometry.Space.chartSmallEtaleRestriction` definitionally),
the comparison equivalence of the representable case of Stacks 03ED composed with Descent,
Proposition 03DX (2) for the chart scheme
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`), and the two inclusions of
a full subcategory.

**The inclusions of the full subcategories are not optional.**  A morphism in
`CategoryTheory.ObjectProperty.FullSubcategory` is a one-field structure wrapping a morphism of
the ambient category — `CategoryTheory.InducedCategory.Hom` — not that morphism itself, so the
Hom-set of the quasi-coherent modules is not the Hom-set of the underlying sheaves of modules and
the passage between them is `CategoryTheory.ObjectProperty.fullyFaithfulι`.

No declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM to
a chart, not an assertion of any tag, and the clauses of Stacks 03DX, 03ED and 04M0 used are
already covered in the tree.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- The functor of `Stacks.SheafOfModules.reindexEquivalence` is the direct image along
`e.functor` with the identity structure map. -/
theorem reindexEquivalence_functor :
    (reindexEquivalence e R).functor =
      SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R)) := rfl

/-- The inverse of `Stacks.SheafOfModules.reindexEquivalence` is the direct image along
`e.inverse` with the structure map `Stacks.SheafOfModules.reindexBackSharp`. -/
theorem reindexEquivalence_inverse :
    (reindexEquivalence e R).inverse =
      SheafOfModules.pushforward.{m} (reindexBackSharp (J' := J') e R) := rfl

/-- The value of `Stacks.SheafOfModules.reindexEquivalence` at a sheaf of modules is its direct
image along `e.functor`. -/
theorem reindexEquivalence_functor_obj (M : SheafOfModules.{m} R) :
    (reindexEquivalence e R).functor.obj M =
      (SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj M := rfl

/-- The action of `Stacks.SheafOfModules.reindexEquivalence` on a morphism is its direct image
along `e.functor`. -/
theorem reindexEquivalence_functor_map {M N : SheafOfModules.{m} R} (f : M ⟶ N) :
    (reindexEquivalence e R).functor.map f =
      (SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).map f := rfl

/-- **Reindexing along an equivalence of ringed sites is a bijection on Hom-sets.**  The direct
image along `e.functor`, with the identity structure map, is the functor of an equivalence of
module categories, hence fully faithful. -/
noncomputable def reindexHomEquiv (M N : SheafOfModules.{m} R) :
    (M ⟶ N) ≃
      ((SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj M ⟶
        (SheafOfModules.pushforward.{m} (𝟙 (reindexRing J' e R))).obj N) :=
  (reindexEquivalence e R).fullyFaithfulFunctor.homEquiv

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The comparison of Stacks 04M0 on modules -/

/-- **The comparison equivalence of Stacks 04M0 at a chart, read on the module categories.**
Reindexing along the comparison of the slice of the small étale site of `X` at an étale chart
with the small étale site of the chart is an equivalence of the two categories of sheaves of
modules; its functor is `AlgebraicGeometry.Space.chartSmallEtaleRestriction`, definitionally. -/
noncomputable def chartModuleReindexEquivalence (A : SmallEtale B S hS X.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over A) ≌
      SheafOfModules.{u} (chartStructureRingSheaf B S hS X A) :=
  @Stacks.SheafOfModules.reindexEquivalence _ _ _ _
    ((SmallEtale.topology B S hS X.1).over A)
    (SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 A)
    (isContinuous_chartLocalization_chartSpace B S hS X A)
    inferInstance
    ((structureRingSheaf B S hS X).over A)

/-- The functor of `AlgebraicGeometry.Space.chartModuleReindexEquivalence` sends the restriction
of an `𝒪_X`-module to the slice at a chart to its restriction to the small étale site of the
chart. -/
theorem chartModuleReindexEquivalence_functor_obj
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1) :
    (chartModuleReindexEquivalence B S hS X A).functor.obj (M.over A) =
      chartSmallEtaleRestriction B S hS X M A := rfl

/-! ### The four legs of the transport -/

/-- **The restriction to the small étale site of a chart is a bijection on Hom-sets.**  Morphisms
of the restrictions of `M` and `N` to the slice of the small étale site of `X` at an étale chart
are exactly morphisms of their restrictions to the small étale site of the chart. -/
noncomputable def chartSmallEtaleRestrictionHomEquiv
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1) :
    (M.over A ⟶ N.over A) ≃
      (chartSmallEtaleRestriction B S hS X M A ⟶ chartSmallEtaleRestriction B S hS X N A) :=
  (chartModuleReindexEquivalence B S hS X A).fullyFaithfulFunctor.homEquiv

/-- Morphisms of the quasi-coherent restrictions of `M` and `N` to the small étale site of a
chart are morphisms of the underlying sheaves of modules: the inclusion of the quasi-coherent
modules is fully faithful. -/
noncomputable def chartSmallEtaleQcohHomEquiv
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (chartSmallEtaleQcoh B S hS X M hM A ⟶ chartSmallEtaleQcoh B S hS X N hN A) ≃
      (chartSmallEtaleRestriction B S hS X M A ⟶ chartSmallEtaleRestriction B S hS X N A) :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (chartStructureRingSheaf B S hS X A)).fullyFaithfulι.homEquiv

/-- **Descent, Proposition 03DX (2) and the representable case of Stacks 03ED are a bijection on
Hom-sets.**  Morphisms of the quasi-coherent restrictions of `M` and `N` to the small étale site
of a chart are exactly morphisms of the quasi-coherent modules they become on the chart's
scheme. -/
noncomputable def chartSchemeQcohHomEquiv
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (chartSmallEtaleQcoh B S hS X M hM A ⟶ chartSmallEtaleQcoh B S hS X N hN A) ≃
      (chartSchemeQcoh B S hS X M hM A ⟶ chartSchemeQcoh B S hS X N hN A) :=
  (representedQuasicoherentSchemeEquivalence B S hS
    ((SmallEtale.toOver B S hS X.1).obj A)).fullyFaithfulInverse.homEquiv

/-- Morphisms of the quasi-coherent chart restrictions are morphisms of the underlying
`AlgebraicGeometry.Scheme.Modules`: the inclusion of the quasi-coherent modules on the chart's
scheme is fully faithful. -/
noncomputable def chartSchemeModuleObjHomEquiv
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (chartSchemeQcoh B S hS X M hM A ⟶ chartSchemeQcoh B S hS X N hN A) ≃
      (chartSchemeModule B S hS X M hM A ⟶ chartSchemeModule B S hS X N hN A) :=
  (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).fullyFaithfulι.homEquiv

/-! ### The transport -/

/-- **The Hom-sets of the chart restriction of a quasi-coherent `𝒪_X`-module agree with the
Hom-sets on the slice of the small étale site of `X` at the chart.**

Morphisms `M|_A ⟶ N|_A` of the restrictions of two quasi-coherent `𝒪_X`-modules to the slice of
the small étale site of `X` at an étale scheme chart `A` are exactly morphisms of the
quasi-coherent `AlgebraicGeometry.Scheme.Modules` which `M` and `N` become on the chart's scheme.

This is the transport along which a statement about morphisms of quasi-coherent modules on a
scheme becomes a statement about morphisms of the restrictions to a chart of an algebraic
space. -/
noncomputable def chartSchemeModuleHomEquiv
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :
    (M.over A ⟶ N.over A) ≃
      (chartSchemeModule B S hS X M hM A ⟶ chartSchemeModule B S hS X N hN A) :=
  ((chartSmallEtaleRestrictionHomEquiv B S hS X M N A).trans
      (chartSmallEtaleQcohHomEquiv B S hS X M N hM hN A).symm).trans
    ((chartSchemeQcohHomEquiv B S hS X M N hM hN A).trans
      (chartSchemeModuleObjHomEquiv B S hS X M N hM hN A))

/-- **The forward direction of the transport is the chart restriction functor.**  On a morphism
coming from a morphism of quasi-coherent `𝒪_X`-modules, the bijection of
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` is the action of
`AlgebraicGeometry.Space.chartSchemeModuleFunctor` on morphisms. -/
theorem chartSchemeModuleHomEquiv_restrictionFunctor_map (A : SmallEtale B S hS X.1)
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (φ : M ⟶ N) :
    chartSchemeModuleHomEquiv B S hS X M.obj N.obj M.property N.property A
        ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) A).map φ.hom) =
      (chartSchemeModuleFunctor B S hS X A).map φ := rfl

/-- **Every morphism of the chart restrictions comes from a morphism on the slice at the chart.**
This is the direction of `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` in which a
surjectivity statement proved for quasi-coherent modules on the chart's scheme is transported
back to the small étale site of the algebraic space. -/
theorem exists_chartSchemeModuleHomEquiv
    (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1)
    (g : chartSchemeModule B S hS X M hM A ⟶ chartSchemeModule B S hS X N hN A) :
    ∃ f : M.over A ⟶ N.over A, chartSchemeModuleHomEquiv B S hS X M N hM hN A f = g :=
  (chartSchemeModuleHomEquiv B S hS X M N hM hN A).surjective g

end AlgebraicGeometry.Space

end
