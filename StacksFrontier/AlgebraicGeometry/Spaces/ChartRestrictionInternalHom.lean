module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom

/-!
# The internal Hom and the chart restriction of Stacks 04M0 commute

The source proof of clause (6) of Stacks 03M1 reads the internal Hom
`𝓗om_{𝒪_X}(G, G')` on an étale chart: "restriction is a localization (Stacks 04LX, formula
04M1) and formation of internal hom commutes with localization (Stacks 0E8H)".  The tree carries
each half separately — `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` is Stacks 0E8H on
the small étale ringed site, and
`AlgebraicGeometry.Space.chartSmallEtaleRestriction'` reads a module on the slice as a module on
the small étale site of the chart through the comparison of Stacks 04M0 — and this file joins
them:

`𝓗om_{𝒪_X}(G, G')|_U = 𝓗om_{𝒪_U}(G|_U, G'|_U)` as modules on the small étale site of `U`.

Both steps are isomorphisms of sheaves of modules over the restricted structure sheaf, which is
not the structure sheaf of any *ringed site* as the tree spells one; that is what
`AlgebraicGeometry.RingedSite.localizationAtObject` supplies, and with it the slice half of Stacks
0E8H becomes an identity of internal Hom *sheaves* and the chart half is
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso`, the invariance of the internal
Hom sheaf under an equivalence of ringed sites.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleLocalization`: the small étale ringed site of an algebraic
  space localized at an étale chart.
* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionInternalHomIso`: **the chart restriction of
  the internal Hom is the internal Hom of the chart restrictions.**

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHom_eq_internalHomSheaf` and
  `AlgebraicGeometry.Space.smallEtaleInternalHomOver_eq_internalHomSheaf`: the two internal Homs
  of `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom` are the internal Hom sheaf of
  Stacks 03EM at the small étale ringed site and at its localization, on the nose.

## Implementation notes

The structure map `φ` of the equivalence of ringed sites is the identity, not merely an
isomorphism: the reindexing of the restricted structure sheaf along the comparison of
Stacks 04M0 *is* the structure sheaf of the chart, which is
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`, itself an `rfl`.  So
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` applies with no structure-map
comparison to build, and its `IsIso` hypothesis is discharged by `inferInstance`.

The module universe is free, as it is for
`AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` and
`AlgebraicGeometry.Space.chartSmallEtaleRestriction'`: both sides of the isomorphism have their
sections in `max (u + 1) m`, since the internal Hom of modules with sections in `m` on a site
with objects in `Type (u + 1)` has sections in `max (u + 1) m` and the chart restriction does not
move them.

No `@[stacks]` attribute is carried.  Stacks 0E8H sits on the general statement in
`StacksDraft.Ch18.Sec27.InternalHomRestriction` and Stacks 04M0 on
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`; what is below is their composite at one
ringed site, and no clause of Stacks 03M1 is proved here.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 04M1](https://stacks.math.columbia.edu/tag/04M1)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The small étale ringed site of an algebraic space localized at an étale chart `U`: the slice
`(X_étale/U, 𝒪_X|_U)`.  Its objects live in `Type (u + 1)`, as those of the small étale site
itself do. -/
noncomputable abbrev smallEtaleLocalization (U : SmallEtale B S hS X.1) :
    RingedSite.{u + 1, u, u} :=
  (smallEtaleRingedSite B S hS X.1 X.2).localizationAtObject U

/-- The internal Hom of `𝒪_X`-modules is the internal Hom sheaf of Stacks 03EM at the small
étale ringed site, on the nose. -/
theorem smallEtaleInternalHom_eq_internalHomSheaf (G G' : Modules.{u, m} B S hS X.1 X.2) :
    smallEtaleInternalHom B S hS X.1 X.2 G G' =
      RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS X.1 X.2) G G' := rfl

/-- The internal Hom of the restrictions of two `𝒪_X`-modules to the slice at an étale chart is
the internal Hom sheaf of Stacks 03EM at the localized ringed site, on the nose. -/
theorem smallEtaleInternalHomOver_eq_internalHomSheaf (G G' : Modules.{u, m} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) :
    smallEtaleInternalHomOver B S hS X.1 X.2 G G' U =
      RingedSite.internalHomSheaf (smallEtaleLocalization B S hS X U)
        (G.over U) (G'.over U) := rfl

/-- The small étale ringed site of the algebraic space represented by an étale scheme chart. -/
noncomputable abbrev chartRingedSite (U : SmallEtale B S hS X.1) : RingedSite.{u + 1, u, u} :=
  smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2

/-- **Stacks 0E8H at the localized ringed site.**  The restriction of the internal Hom of two
`𝒪_X`-modules to the slice at an étale chart `U` is the internal Hom sheaf of the localization of
the small étale ringed site at `U`.

This is `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` with its target read through
`AlgebraicGeometry.Space.smallEtaleInternalHomOver_eq_internalHomSheaf`, which is an `rfl`; the
spelling matters because it is the one
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` consumes. -/
noncomputable def smallEtaleInternalHomLocalizationIso (G G' : Modules.{u, m} B S hS X.1 X.2)
    (U : SmallEtale B S hS X.1) :
    (smallEtaleInternalHom B S hS X.1 X.2 G G').over U ≅
      RingedSite.internalHomSheaf (smallEtaleLocalization B S hS X U)
        (G.over U) (G'.over U) :=
  smallEtaleInternalHomOverIso B S hS X.1 X.2 G G' U

/-- **The chart restriction of the internal Hom is the internal Hom of the chart restrictions.**
For `𝒪_X`-modules `G`, `G'` on an algebraic space and an étale scheme chart `U` of `X`,

`𝓗om_{𝒪_X}(G, G')|_U ≅ 𝓗om_{𝒪_U}(G|_U, G'|_U)`

as modules on the small étale site of the algebraic space represented by `U`, both sides read
through the comparison of Stacks 04M0.

This is the step of the source proof of Stacks 03M1(6) which says that restriction to an étale
chart is a localization and that formation of internal Hom commutes with localization: the first
half is `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso`, Stacks 0E8H on the small étale
ringed site, and the second is
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` for the equivalence of ringed
sites of Stacks 04M0, whose structure map is the identity by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`. -/
noncomputable def chartSmallEtaleRestrictionInternalHomIso
    (G G' : Modules.{u, m} B S hS X.1 X.2) (U : SmallEtale B S hS X.1) :
    chartSmallEtaleRestriction' B S hS X (smallEtaleInternalHom B S hS X.1 X.2 G G') U ≅
      smallEtaleInternalHom B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2
        (chartSmallEtaleRestriction' B S hS X G U)
        (chartSmallEtaleRestriction' B S hS X G' U) :=
  by
  let Xs : RingedSite.{u + 1, u, u} := smallEtaleLocalization B S hS X U
  let Ych : RingedSite.{u + 1, u, u} := chartRingedSite B S hS X U
  let eqv : Ych.C ≌ Xs.C := SmallEtale.chartLocalizationEquivalence B S hS X.1 U
  haveI : eqv.functor.IsContinuous Ych.J Xs.J :=
    isContinuous_chartLocalization_chartSpace B S hS X U
  haveI : eqv.inverse.IsContinuous Xs.J Ych.J :=
    @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
      (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)
  let φ : (Stacks.SheafOfModules.Tensor.ringSheaf Ych.O) ⟶
      (eqv.functor.sheafPushforwardContinuous RingCat.{u} Ych.J Xs.J).obj
        ((Stacks.SheafOfModules.Tensor.ringSheaf Xs.O)) := 𝟙 _
  haveI : IsIso φ := inferInstanceAs (IsIso (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf Ych.O))))
  exact (SheafOfModules.pushforward.{max (u + 1) m} φ).mapIso
      (smallEtaleInternalHomLocalizationIso B S hS X G G' U) ≪≫
    Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso
      eqv φ (G.over U) (G'.over U)

end AlgebraicGeometry.Space

end
