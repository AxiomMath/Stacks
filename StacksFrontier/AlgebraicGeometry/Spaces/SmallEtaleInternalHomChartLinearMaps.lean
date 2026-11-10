module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartHom

/-!
# A section of the internal Hom at an affine chart is a linear map of global sections

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G`,
`G'` be quasi-coherent `𝒪_X`-modules on its small étale site.  A section over an étale chart `A`
of the internal Hom sheaf `𝓗om_{𝒪_X}(G, G')` of [Stacks Project, Tag 04TT] is, by the definition
of that sheaf, a *morphism of the restrictions to the slice* of the small étale site at `A`.
This file identifies that description with the Zariski one: when the scheme underlying `A` is
affine, such a section is exactly a `Γ(A, ⊤)`-linear map of the global sections of the two
modules read on the chart's scheme.

Three identifications from the library compose to give it, and nothing else is needed:

* a section of the internal Hom over `A` *is* a morphism of the two restrictions to the slice,
  which is a morphism of sheaves of modules on the slice because the two restrictions are
  sheaves — `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv` of
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartHom`, used here at the
  algebraic
  space `X`, which is the full faithfulness of `CategoryTheory.SheafOfModules.forget` and so only
  wraps and unwraps the one-field structure `CategoryTheory.SheafOfModules.Hom`;
* morphisms on the slice at a chart are morphisms of the quasi-coherent modules the two become
  on the chart's scheme, `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` — the transport of
  [Stacks Project, Tag 04M0] at the chart followed by Descent, Proposition
  [Stacks Project, Tag 03DX] (2) for the chart scheme;
* morphisms of quasi-coherent sheaves of modules on an affine scheme are the `Γ(A, ⊤)`-linear
  maps of their global sections, `Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ`.

## Why this is wanted

It is the step of [Stacks Project, Tag 04AM] which reads the acting sheaf of
[Stacks Project, Tag 061D] on an étale scheme chart.  That sheaf is an internal Hom, so its
sections at a chart are morphisms of *restrictions to a slice*, while the action constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` is by
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, a linear map of *Zariski global
sections* on the chart.  What is proved here is the passage between the two descriptions, for an
arbitrary internal Hom of quasi-coherent modules; the instantiation at the acting sheaf is
`StacksDraft.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartLinearMaps`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv`: **the same section, read
  as a morphism of the inverse images of `G` and `G'` to the small étale site of the chart
  space** — the description under which a comparison of the two modules proved on the chart
  space applies to it.  This carries nothing at all: no quasi-coherence and no affineness.
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartLinearEquiv`: **a section of
  `𝓗om_{𝒪_X}(G, G')` over an étale chart with affine underlying scheme is a `Γ(A, ⊤)`-linear
  map of the global sections of the chart restrictions of `G` and `G'`.**
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv`: the same with the
  two chart restrictions presented as the associated modules of *given* quasi-coherent Zariski
  modules on the chart's scheme, which is the form in which a geometric comparison on the chart
  space is consumed.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_apply_val`: the identification of
  a section with a morphism on the slice changes nothing — the underlying morphism of presheaves
  of modules is the section itself.
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartLinearEquiv_apply`: the linear map attached
  to a section is the action on global sections of the chart transport of the corresponding
  morphism on the slice, so the identification is the composite of the three and
  introduces no twist of its own.

## Implementation notes

The modules are taken as `CategoryTheory.SheafOfModules` over
`AlgebraicGeometry.Space.structureRingSheaf`, not as `AlgebraicGeometry.Space.Modules`, although
the two are the same category.  The reason is the one recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent`:
`AlgebraicGeometry.Space.structureRingSheaf` is typed at
`AlgebraicGeometry.Space.SmallEtale.topology` whereas `AlgebraicGeometry.Space.Modules` forces
the projection `(AlgebraicGeometry.Space.smallEtaleRingedSite ‹_›).J`, and with the latter
spelling instance search does not find `CategoryTheory.Category (Over A)`, so
`CategoryTheory.SheafOfModules.over` does not even elaborate.

A section of the internal Hom over `A` is *definitionally* a morphism of the restrictions of the
underlying presheaves of modules, and a morphism of sheaves of modules is a one-field structure
on such a morphism; so `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv`, the inverse
of the bijection on morphisms of the fully faithful `CategoryTheory.SheafOfModules.forget`, is the
constructor and the projection, and both round trips are `Eq.refl`.  Nothing has to be said about
the sheaf condition: the restriction of a sheaf of modules to a slice is the restriction of its
underlying presheaf of modules, again definitionally.

No `@[stacks]` attribute is claimed.  Tag 04TT is the internal Hom presheaf, registered where it
is built; Tag 04M0 and Tag 03DX (2) are registered at the transports composed here.

## References

* [Stacks Project, Tag 01PC](https://stacks.math.columbia.edu/tag/01PC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Reading a section of the internal Hom as a morphism on the slice changes nothing: the
underlying morphism of presheaves of modules of the result is the section itself.

The result of `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv` is typed at the
spelling `(AlgebraicGeometry.Space.smallEtaleRingedSite …).C` of the chart, where instance search
does not find `CategoryTheory.Category (Over A)` for a chart `A` of
`AlgebraicGeometry.Space.SmallEtale`; the `show` restates it at the spelling of
`AlgebraicGeometry.Space.structureRingSheaf`, where `.val` elaborates. -/
theorem smallEtaleInternalHomChartHomEquiv_apply_val
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A)) :
    (show G.over A ⟶ G'.over A from
      smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A α).val = α :=
  rfl

/-- **A section of the internal Hom over an étale chart is a morphism of the inverse images to
the small étale site of the chart space.**  This is the second description of a chart-level
section: the sheaf is built so that its sections at `A` are morphisms of the restrictions to the
*slice* at `A`, while a geometric comparison of modules proved on the chart space compares their
inverse images along the structure morphism `chartSpace A ⟶ X` of the chart.  The two are matched
by the slice form of [Stacks Project, Tag 04M0] together with Equation
[Stacks Project, Tag 03LW]: restriction to the slice at `A` is the inverse image to the small
étale site of the chart space,
`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction`.

Nothing is carried: neither module has to be quasi-coherent and the chart's scheme need not be
affine. -/
noncomputable def smallEtaleInternalHomChartPullbackHomEquiv
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1) :
    (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A) ≃
      ((modulePullback B S hS (chartToSpace B S hS X A)).obj G ⟶
        (modulePullback B S hS (chartToSpace B S hS X A)).obj G') :=
  (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A).trans
    ((chartSmallEtaleRestrictionHomEquiv B S hS X G G' A).trans
      (Iso.homCongr (chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X G A).symm
        (chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X G' A).symm))

/-- **A section of the internal Hom of two quasi-coherent `𝒪_X`-modules over an étale chart with
affine underlying scheme is a `Γ(A, ⊤)`-linear map of global sections.**  For quasi-coherent
`𝒪_X`-modules `G` and `G'` and an étale scheme chart `A` of `X` whose underlying scheme is
affine, the sections of `𝓗om_{𝒪_X}(G, G')` over `A` are exactly the `Γ(A, ⊤)`-linear maps
`Γ(G|_A, ⊤) ⟶ Γ(G'|_A, ⊤)` of the global sections of the chart restrictions of `G` and `G'` to
the chart's scheme.

This is the identification of the two descriptions of a chart-level section of an internal Hom:
the one by morphisms of the restrictions to the *slice* of the small étale site, which is how the
sheaf is built, and the Zariski one by linear maps on the chart's scheme, which is how an action
constructed in a chart is indexed.  It is the three identifications composed —
`AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv`,
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` and
`Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ` — and carries nothing beyond
quasi-coherence of the two modules and affineness of the chart. -/
noncomputable def smallEtaleInternalHomChartLinearEquiv
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) [IsAffine (chartScheme A)] :
    (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A) ≃
      (↑Γ(chartSchemeModule B S hS X G hG A, (⊤ : (chartScheme A).Opens)) →ₗ[
          Γ(chartScheme A, (⊤ : (chartScheme A).Opens))]
        ↑Γ(chartSchemeModule B S hS X G' hG' A, (⊤ : (chartScheme A).Opens))) :=
  haveI := isQuasicoherent_chartSchemeModule B S hS X G hG A
  haveI := isQuasicoherent_chartSchemeModule B S hS X G' hG' A
  ((smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A).trans
      (chartSchemeModuleHomEquiv B S hS X G G' hG hG' A)).trans
    (Equiv.ofBijective _ Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ)

/-- The linear map attached to a section of the internal Hom is the action on global sections of
the chart transport of the corresponding morphism on the slice: the identification introduces no
twist of its own beyond the three it is composed of. -/
theorem smallEtaleInternalHomChartLinearEquiv_apply
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hG : G.IsQuasicoherentOnSite) (hG' : G'.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) [IsAffine (chartScheme A)]
    (α : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A)) :
    smallEtaleInternalHomChartLinearEquiv B S hS X G G' hG hG' A α =
      Stacks.AlgebraicGeometry.ModuleLimits.appTopₗ
        (chartSchemeModuleHomEquiv B S hS X G G' hG hG' A
          (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A α)) :=
  rfl

/-- **A section of the internal Hom at an affine chart, read through given presentations of the
two chart restrictions as associated modules.**  Suppose the inverse images of `G` and `G'` to
the small étale site of the chart space are exhibited as the modules `M₀ᵃ` and `N₀ᵃ` of
[Stacks Project, Tag 03DU] (4) of quasi-coherent Zariski modules `M₀`, `N₀` on the chart's
scheme, which is affine.  Then a section of `𝓗om_{𝒪_X}(G, G')` over the chart is exactly a
`Γ(A, ⊤)`-linear map `Γ(M₀, ⊤) ⟶ Γ(N₀, ⊤)`.

This is the form in which a geometric comparison proved on the chart space — such as the
composite of [Stacks Project, Tag 04CU] and [Stacks Project, Tag 04CS] for the sheaf of
differentials — turns a chart-level section of an internal Hom into a linear map of Zariski
global sections.  The passage from the isomorphisms to the bijection of morphisms is
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`, the small étale half of
[Stacks Project, Tag 0GN7] composed with the affine case of
[Stacks Project, Tag 01PC]; it carries only quasi-coherence of `M₀` and `N₀`. -/
noncomputable def smallEtaleInternalHomChartAssociatedLinearEquiv
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X)) (A : SmallEtale B S hS X.1)
    [IsAffine (chartScheme A)]
    (M₀ N₀ : (chartScheme A).Modules) [M₀.IsQuasicoherent] [N₀.IsQuasicoherent]
    (eG : (modulePullback B S hS (chartToSpace B S hS X A)).obj G ≅
      (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj A)
        (chartSpace B S hS X A).2).obj M₀)
    (eG' : (modulePullback B S hS (chartToSpace B S hS X A)).obj G' ≅
      (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj A)
        (chartSpace B S hS X A).2).obj N₀) :
    (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A) ≃
      (↑Γ(M₀, (⊤ : (chartScheme A).Opens)) →ₗ[Γ(chartScheme A, (⊤ : (chartScheme A).Opens))]
        ↑Γ(N₀, (⊤ : (chartScheme A).Opens))) :=
  (smallEtaleInternalHomChartPullbackHomEquiv B S hS X G G' A).trans
    ((Iso.homCongr eG eG').trans
      (representedAssociatedModuleHomEquivLinearMap B S hS
        ((SmallEtale.toOver B S hS X.1).obj A) (chartSpace B S hS X A).2 M₀ N₀))

end AlgebraicGeometry.Space

end
