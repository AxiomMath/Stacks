module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartHomRestrSliceBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLinearMaps

/-!
# The restriction map of the internal Hom, read at the two charts

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `G`, `G'` be
`𝒪_X`-modules on its small étale site and let `g : A' ⟶ A` be a morphism of étale scheme charts
of `X`.  A section of the internal Hom sheaf `𝓗om_{𝒪_X}(G, G')` of [Stacks Project, Tag 04TT]
over `A` restricts along `g` to a section over `A'`, by the restriction map of that presheaf.
The same section is read by `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv` as a
morphism `G|_A ⟶ G'|_A` of sheaves of modules on the slice of the small étale site at `A`, and
such a morphism relocalizes along `g` by `Stacks.PresheafOfModules.homRestr`.

**This file identifies the two**: the restriction map of the internal Hom *is* relocalization of
the slice morphism.  It is the sections-level half of the naturality in the chart of the
chart-level readings of a section of an internal Hom, which is the step of
[Stacks Project, Tag 04AM] recorded as the small-étale compatibility in the docstring of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_map_val_app_apply`: **the component
  on a section.**  Over an object `Z` of the slice at the smaller chart, the slice morphism of
  the restricted section is the slice morphism of the section itself over
  `Over.mk (Z.hom ≫ g)`.  This is
  `Stacks.PresheafOfModules.homRestr_app_apply` read at the restriction map of the internal Hom,
  and it holds by `rfl`.
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_map_val_eq_homRestr`: **the
  restriction map of the internal Hom is relocalization of the slice morphism**, as an equality
  of morphisms of presheaves of modules on the slice at the smaller chart.

## Implementation notes

**The morphism-level identification is reached only through its components.**  Both sides are
definitionally equal — the restriction map of
`Stacks.PresheafOfModules.internalHom` is built by applying
`Stacks.PresheafOfModules.homRestr`, and
`AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv` is the constructor and the
projection of a one-field structure — but `rfl` on the equality of the two *morphisms* is a
`whnf` timeout at 200 000 heartbeats, whichever of the two spellings
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).O.obj` and
`AlgebraicGeometry.Space.smallEtaleStructurePresheaf` of the structure presheaf is written (the
two are themselves `rfl`, cheaply).  The same `rfl` on a *component applied to a section* is
instant.  The morphism-level statement is therefore proved by
`PresheafOfModules.hom_ext` from the component statement, with
`AlgebraicGeometry.Space.val_app_homRestr_apply` evaluating the right-hand side; that is the
route recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartHomRestrSliceBridge`, where the same effect is
observed for the ext principle.

**The slice morphisms are restated with `show`.**
`AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv` types its result at the spelling
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).C` of the chart, and for a chart of
`AlgebraicGeometry.Space.SmallEtale` instance search then finds no
`CategoryTheory.Category (Over A)`, so `.val` does not elaborate on it.  Each slice morphism is
therefore restated by `show` at the spelling of `AlgebraicGeometry.Space.structureRingSheaf`,
which is the same type definitionally.

No `@[stacks]` attribute is claimed.  Tag 04TT is the internal Hom presheaf, registered where it
is built, and Tag 04M0 is registered at the comparison equivalence; this is an interior step of
[Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The component on a section of the slice morphism of a restricted section of the internal
Hom.**  Restrict a section `α` of `𝓗om_{𝒪_X}(G, G')` over an étale chart `A` along a morphism
`g : A' ⟶ A` of charts and read the result as a morphism of the restrictions of `G` and `G'` to
the slice of the small étale site at `A'`.  Over an object `Z` of that slice its component is the
component of the slice morphism of `α` itself over `Over.mk (Z.hom ≫ g)`, the image of `Z` in the
slice at `A`.

This holds by `rfl`: the restriction map of the internal Hom presheaf of
[Stacks Project, Tag 04TT] applies `Stacks.PresheafOfModules.homRestr`, whose components are
given by `Stacks.PresheafOfModules.homRestr_app_apply` with no base change, and reading a section
as a morphism on the slice is the constructor of a one-field structure. -/
theorem smallEtaleInternalHomChartHomEquiv_map_val_app_apply
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X))
    {A' A : SmallEtale B S hS X.1} (g : A' ⟶ A)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A))
    (Z : (Over A')ᵒᵖ)
    (x : ((restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) A').obj G.val).obj Z) :
    ((show G.over A' ⟶ G'.over A' from smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A'
          ((smallEtaleInternalHom B S hS X.1 X.2 G G').val.map g.op α)).val.app Z).hom x =
      ((show G.over A ⟶ G'.over A from
          smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A α).val.app
        (op (Over.mk (Z.unop.hom ≫ g)))).hom x :=
  rfl

/-- **The restriction map of the internal Hom is relocalization of the slice morphism.**  The
morphism of the slice restrictions attached to the restriction of a section `α` of
`𝓗om_{𝒪_X}(G, G')` along a morphism `g : A' ⟶ A` of étale scheme charts is the relocalization
along `g` of the morphism of the slice restrictions attached to `α`.

This is the sections-level input of the naturality in the chart of the chart-level readings of a
section of an internal Hom: the left-hand side is how the internal Hom sheaf itself restricts a
section, the right-hand side is how a morphism on the slice is carried to the smaller slice, and
the two agree with no transport.

Proved from `AlgebraicGeometry.Space.smallEtaleInternalHomChartHomEquiv_map_val_app_apply`
componentwise; see the implementation notes for why the direct `rfl` is not affordable. -/
theorem smallEtaleInternalHomChartHomEquiv_map_val_eq_homRestr
    (G G' : SheafOfModules.{u} (structureRingSheaf B S hS X))
    {A' A : SmallEtale B S hS X.1} (g : A' ⟶ A)
    (α : (smallEtaleInternalHom B S hS X.1 X.2 G G').val.obj (op A)) :
    (show G.over A' ⟶ G'.over A' from smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A'
        ((smallEtaleInternalHom B S hS X.1 X.2 G G').val.map g.op α)).val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) G.val G'.val g
        (show G.over A ⟶ G'.over A from
          smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A α).val :=
  _root_.PresheafOfModules.hom_ext fun Z =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      (smallEtaleInternalHomChartHomEquiv_map_val_app_apply B S hS X G G' g α Z x).trans
        (val_app_homRestr_apply B S hS X G G' g
          (smallEtaleInternalHomChartHomEquiv B S hS X.1 X.2 G G' A α) Z x).symm)

end AlgebraicGeometry.Space

end
