module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartSections

/-!
# A section of the acting sheaf, read on a chart into the conormal data of the thickening

Let `X ⊆ X'` be a first-order thickening of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, let `q : Y ⟶ B` be a morphism of algebraic spaces and let `a : X ⟶ Y` be a
morphism over `B`.  The sheaf acting on the lifts of `a` over the étale charts of `X'` is
`AlgebraicGeometry.Space.liftActionSheaf`, the internal Hom
`SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` of [Stacks Project, Tag 061D], and the action is
constructed over an étale scheme chart in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`, where the acting object is
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — a `Γ(U, ⊤)`-linear map
`Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}` into the conormal data `RingHom.ker i^♯` of the chart thickening
`i : U ⟶ U'`.

This file composes the two halves of the comparison of those two descriptions that are available:
the reading of a section of the internal Hom on a chart
(`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartSections`) and the
identification of the conormal sections with `RingHom.ker i^♯`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartSections`).  The result,
`AlgebraicGeometry.Space.liftActionSheafChartKerEval`, reads a section of the acting sheaf over
the base-changed chart `X ×_{X'} U'` as a map into `RingHom.ker i^♯` — the codomain of
`ActionSection`, for *any* presentation of the chart thickening by a cartesian square.

## Main definitions

* `AlgebraicGeometry.Space.liftActionSheafChartKerEval`: **a section of the acting sheaf of
  [Stacks Project, Tag 061D] over the base-changed chart, applied to a section of `a^*Ω_{Y/B}`
  there, as an element of `RingHom.ker i^♯`.**

## What this does not do

The remaining gap is the **source** of the two linear maps, and it is a single identification:
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` has the *Zariski* module
`Γ(a^*Ω_{W/V}, ⊤)` of the chart square as its source, and
`AlgebraicGeometry.Space.liftActionSheafChartKerEval` has the sections of the small-étale
`a^*Ω_{Y/B}` over the chart.  Both geometric comparisons it needs are proved in this tree:

* [Stacks Project, Tag 04CU],
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, identifies
  `Ω_{Y/B}` restricted to a chart `W` of `Y` with `Ω_{W/V}` for a commuting square of étale
  charts `W ⟶ V`;
* [Stacks Project, Tag 04CS],
  `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` (the *named* form — the tag's
  own `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` produces its isomorphism
  inside a `Nonempty`, which a consumer reading a derivation through it cannot use), identifies
  the spaces-level `Ω` of a morphism of schemes of the site with the associated module of the
  Zariski `Ω_{W/V}`.

**The composite of those two is now written down**, in the spelling a chart presentation
produces: `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso`
(`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsAssociated`) exhibits
`c^*Ω_{Y/B}`, for a `c : T ⟶ Y` factoring as a morphism of the site into the chart `W` followed
by `w`, as the associated module of the Zariski `(r_{sch})^*Ω_{W/V}`.

The passage from an isomorphism of *sheaves* to a bijection on *morphisms* carries **nothing
either**.  It does not need [Stacks Project, Tag 0GN7] read on the slice at an affine chart,
`AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice`, and so does not carry
the fpqc sheaf condition of [Stacks Project, Tag 03DT].  That condition is in any case
proved, `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, and its instance
on the slice at a chart is proved as
`AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent`, with the
hypothesis-free slice statement
`AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice_unconditional`.  But the
slice is not needed at all: the small étale half of Tag 0GN7 holds over an **arbitrary** scheme,
unconditionally, as `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'` — Tag 070S
part (2) for the small étale site being proved in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity` — and its
hom-set form on a represented algebraic space is
`AlgebraicGeometry.Space.bijective_representedAssociatedModule_map`
(`StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleFullyFaithful`), which asks
quasi-coherence of the target module only.

The Zariski side is proved as well — `Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ`,
that morphisms of quasi-coherent modules on an affine are the `Γ(U, ⊤)`-linear maps of their
global sections — and the composite is
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`, whose right-hand side is
character-for-character the shape of
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.

**The source comparison is now complete**, and so is the whole identification: the sections of
the acting sheaf at a chart are morphisms of the restrictions to the *slice* at that chart,
whereas the isomorphism above is about the inverse image to the small étale site of the chart
space, and the two are matched by [Stacks Project, Tag 04M0] in the form
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv` together with Equation
[Stacks Project, Tag 03LW] in the form
`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction`.  That matching is
packaged as `AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLinearMaps`), and the finished
identification — the sections of the acting sheaf over the chart presented by a chart
presentation are `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — is
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection`).

`AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence` is **not** the piece that
matches them.  That is the *slice-to-slice* comparison for an étale morphism of algebraic spaces,
whereas what is needed is the slice at a chart compared with the small étale site
of the chart *space*, which is `AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`,
already carried on modules by
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv`.

Nothing below asserts that
`AlgebraicGeometry.Space.liftActionSheafChartKerEval` is bijective in its section.  Neither does
anything below assert that it is additive: it is additive in `x` and in `α` through
`AlgebraicGeometry.Space.liftActionSheafChartEval`, which is a morphism of modules and is
additive in the section by
`PresheafOfModules.InternalHom.internalHomEvalHom_add`, but
`AlgebraicGeometry.Space.conormalChartKerEquiv` is a bare bijection — the linear form of that
identification is `AlgebraicGeometry.Space.conormalChartSectionsIso`, an isomorphism of
`Γ(U', ⊤)`-modules, together with the equality of ideals
`AlgebraicGeometry.Space.definingIdealAt_eq_ker_of_isPullback`, and a consumer needing linearity
should compose those two instead.

No `@[stacks]` attribute is placed.  [Stacks Project, Tag 061D]'s acting sheaf is registered on
`AlgebraicGeometry.Space.liftActionSheaf` and its action on the lifts in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`; this file is one input to
the comparison of the two descriptions of that action, not an assertion of the tag.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Bb X' Y : AlgebraicSpaces B S hS}

/-- **A section of the acting sheaf of [Stacks Project, Tag 061D], read on a chart into the
conormal data of the chart thickening.**  Let `Z ⊆ X'` be a first-order thickening with
inclusion `i`, let `U` be an étale scheme chart of `X'`, and let `incl : T ⟶ U` be a morphism of
the big fppf site presenting `Z ×_{X'} U` by a cartesian square.  A section `α` of
`SheafHom_{𝒪_Z}(a^*Ω_{Y/B}, 𝒞_{Z/X'})` over the base-changed chart `Z ×_{X'} U`, applied to a
section `x` of `a^*Ω_{Y/B}` there, is an element of `RingHom.ker incl^♯` — the conormal data of
the presented chart thickening, which is the codomain of
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.

The two steps are `AlgebraicGeometry.Space.liftActionSheafChartEval`, which reads `α` on the
chart as a morphism of modules, and `AlgebraicGeometry.Space.conormalChartKerEquiv`, which
identifies the conormal sections there with the kernel. -/
def liftActionSheafChartKerEval (Z : ClosedSubspaces B S hS X'.1)
    (hZ : IsFirstOrderThickening B S hS X' Z.1) (q : Y ⟶ Bb)
    (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (U : SmallEtale B S hS X'.1) {T : BigFppfOver B S hS}
    (incl : T ⟶ (SmallEtale.toOver B S hS X'.1).obj U)
    (c : yoneda.obj T ⟶ Z.1.toFunctor)
    (hsq : IsPullback (yoneda.map incl) c U.1.hom Z.1.ι)
    (α : (liftActionSheaf B S hS Z q a).val.obj
      (op ((smallBaseChange B S hS (subspaceInclusion B S hS X' Z) Z.2.2.rep).obj U)))
    (x : ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS q)).val.obj
      (op ((smallBaseChange B S hS (subspaceInclusion B S hS X' Z) Z.2.2.rep).obj U))) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map incl).appTop.hom :=
  (conormalChartKerEquiv B S hS Z hZ U incl c hsq).symm
    ((liftActionSheafChartEval B S hS Z q a _ α).hom x)

end AlgebraicGeometry.Space

end
