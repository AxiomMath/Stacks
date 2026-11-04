module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijectiveCovering

/-!
# The base change map of a square is invertible as soon as it is bijective on affine charts

Let

```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`
and let `F` be an `𝒪_X`-module.  `AlgebraicGeometry.Space.moduleBaseChangeMap` is the base change
map `g^*f_*F ⟶ f'_*((g')^*F)` of the square, and its invertibility at a quasi-coherent `F` is
what the base-change clause of Stacks 07U8 — Stacks 02KG for an affine morphism of algebraic
spaces — and part (1) of Stacks 073K in degree zero assert.  The first of those is proved, for a
cartesian square whose two vertical morphisms are affine, in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeAffineChartBijective.lean`, by supplying
this file's chartwise hypothesis; part (1) of Stacks 073K in degree zero, for a flat `g` and a
quasi-compact separated `f`, is carried as a hypothesis in this development, as
`AlgebraicGeometry.Space.FlatBaseChangeZero`, and so is
`AlgebraicGeometry.Space.HasModuleFlatBaseChange`.

**This file reduces that invertibility to a chartwise statement, unconditionally.**  It is enough
that the base change map be bijective on the sections over the chart of `Y'` of every diagram of
*affine* étale scheme charts over `g`.  Nothing else is assumed: the square need not be
cartesian, `F` need not be quasi-coherent and no morphism of the square carries a hypothesis.

The two inputs are cofinality of the affine chart diagrams,
`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`, which is Stacks 03G2 in sieve
form, and `Stacks.SheafOfModules.isIso_of_bijective_val_app_on`, which turns bijectivity on the
objects of a sieve-generating family into invertibility.

## Main results

* `Space.isIso_moduleBaseChangeMap_app_of_bijective_affineChartDiagram`:
  **the base change map of a commutative square is invertible at `F` as soon as it is bijective
  on the sections over the chart of `Y'` of every diagram of affine étale charts over `g`.**
* `Space.nonempty_iso_modulePushforward_modulePullback_of_bijective_affineChartDiagram`:
  the same conclusion in the shape `Nonempty (f'_*((g')^*F) ≅ g^*(f_*F))` in which
  `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformAffinePushforward.lean` consumes it for
  Stacks 0866.

## Implementation notes

The predicate fed to `Stacks.SheafOfModules.isIso_of_bijective_val_app_on` is literally the one
`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology` generates its sieve by, with
the free side condition `Q` on the chart of `Y` taken to be `True`; the chart of `Y'` of the
diagram is then the generating object itself, so the hypothesis is applied after substituting it
and no transport appears.

The hypothesis is stated on `d.U`, the chart of `Y'`, and not on an arbitrary affine chart of
`Y'`: an affine chart of `Y'` need not map into a single affine chart of `Y`, which is exactly
why the cofinality statement is about *diagrams* and not about charts.

**The chartwise hypothesis, and where it is discharged.**  The chartwise bijectivity is not
supplied here.  For a *cartesian* square whose two vertical morphisms are affine and a
quasi-coherent module it is
`AlgebraicGeometry.Space.bijective_moduleBaseChangeMap_val_app_of_affineChartDiagram`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeAffineChartBijective.lean`), which feeds
this file's two theorems and so proves the base-change clause of Stacks 07U8 in that generality.
Over a diagram of affine charts of such a square it exhibits both sides as the two ends of a
chain of four bijections:

* the source `(g^*f_*F)(d.U)` is the base change of the sections of `f_*F` over `d.V`, by
  `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`
  applied to `f_*F`, which is quasi-coherent for an affine `f` by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom`;
* the sections of a direct image along a representable morphism over a chart are the sections
  over the base-changed chart: the chart component
  `AlgebraicGeometry.Space.modulePushforwardCounitApp` at the diagram
  `AlgebraicGeometry.Space.smallBaseChangeDiagram` of the base-changed chart is a bijection, by
  `AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_smallBaseChangeDiagram`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModuleAffineBaseChangeIso.lean`), with no
  hypothesis on the module; and that base-changed chart is again affine for an affine morphism,
  by `AlgebraicGeometry.Space.isAffine_smallBaseChange_obj`.  This replaces the route through
  `AlgebraicGeometry.Space.modulePushforwardChartIso`, which would have to be transported as an
  isomorphism of functors; the chart component is the map the chartwise formulas are written in
  already;
* the square of chart rings *is* a pushout:
  `AlgebraicGeometry.Space.isPushout_appTop_chartSquare_of_isAffineHom`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeChartSquare.lean`) proves it, from
  cartesianness of the square of base-changed charts,
  `AlgebraicGeometry.Space.isPullback_baseChangeChartSquare_scheme`, and
  `AlgebraicGeometry.isPushout_appTop_of_isPullback`.  That file also builds the diagram of
  étale charts over the upper horizontal morphism which the chart square is,
  `AlgebraicGeometry.Space.chartDiagramOfSquare`;
* and `Algebra.IsPushout.cancelBaseChange` turns the two base changes into one.

What makes the chain a chain is the identification of the base change map itself with the
comparison those four assemble.  The map is pinned down on chart sections by
`AlgebraicGeometry.Space.val_app_modulePullbackUnitSection_moduleBaseChangeMap`, whose
right-hand side is the chart component of the direct image of a unit followed by the comparison
of composite direct images.  Composing that with the chart component along `f'` at the
base-changed chart turns both sides into chart components of the two composite direct images
around the square, one along `i ≫ f` and one along `f' ≫ g`, and
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeChartIdentification.lean` carries that
through to
`AlgebraicGeometry.Space.counitApp_val_app_moduleBaseChangeMap_modulePullbackUnitSection`.

No declaration identifies `AlgebraicGeometry.Space.moduleBaseChangeMap` over a represented chart
with `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, for which the scheme-level
Stacks 02KG is proved as
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom`; the only
space-to-scheme module bridges in the development,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap_iff` and
the comparisons of `StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSchemeModuleComparison.lean`,
are at the level of objects and of quasi-coherence, not of this morphism.  The chartwise route
above does not pass through that identification.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- **The base change map of a commutative square of algebraic spaces is invertible at a module
as soon as it is bijective on the sections over the chart of `Y'` of every diagram of affine
étale scheme charts over `g`.**

Nothing else is assumed: the square is only required to commute, the module carries no
quasi-coherence hypothesis and none of the four morphisms carries one.  Invertibility of this
map at a quasi-coherent module is the base-change clause of Stacks 07U8 and part (1) of
Stacks 073K in degree zero, so this is the reduction of those clauses to a chartwise statement.

The affine chart diagrams over `g` are cofinal, by
`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`, and a morphism of sheaves of
modules bijective on the sections over the objects of a sieve-generating family is invertible, by
`Stacks.SheafOfModules.isIso_of_bijective_val_app_on`. -/
theorem isIso_moduleBaseChangeMap_app_of_bijective_affineChartDiagram
    (comm : g' ≫ f = f' ≫ g) (F : Modules.{u, u} B S hS X.1 X.2)
    (hchart : ∀ d : ChartDiagram B S hS Y'.1 Y.1 g.hom,
      IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      Function.Bijective
        (((moduleBaseChangeMap f g f' g' comm).app F).val.app (op d.U))) :
    IsIso ((moduleBaseChangeMap f g f' g' comm).app F) :=
  Stacks.SheafOfModules.isIso_of_bijective_val_app_on
    ((moduleBaseChangeMap f g f' g' comm).app F)
    (fun Z ↦ IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj Z) ∧
      ∃ d : ChartDiagram B S hS Y'.1 Y.1 g.hom, ∃ _ : d.U = Z,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) ∧ True)
    (generate_affineChartDiagram_mem_topology B S hS g (fun _ ↦ True) fun _ _ ↦ trivial)
    (by rintro Z ⟨hZ, d, rfl, hV, -⟩; exact hchart d hZ hV)

/-- The conclusion of
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_bijective_affineChartDiagram` in the
shape `Nonempty (f'_*((g')^*F) ≅ g^*(f_*F))`, which is the shape in which
`AlgebraicGeometry.Space.exists_modulePushforward_strictTransformSheaf_iso` carries the
base-change isomorphism as its hypothesis `hloc`. -/
theorem nonempty_iso_modulePushforward_modulePullback_of_bijective_affineChartDiagram
    (comm : g' ≫ f = f' ≫ g) (F : Modules.{u, u} B S hS X.1 X.2)
    (hchart : ∀ d : ChartDiagram B S hS Y'.1 Y.1 g.hom,
      IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      Function.Bijective
        (((moduleBaseChangeMap f g f' g' comm).app F).val.app (op d.U))) :
    Nonempty ((modulePushforward B S hS f').obj ((modulePullback B S hS g').obj F) ≅
      (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj F)) :=
  have := isIso_moduleBaseChangeMap_app_of_bijective_affineChartDiagram B S hS f g f' g' comm F
    hchart
  ⟨(asIso ((moduleBaseChangeMap f g f' g' comm).app F)).symm⟩

end AlgebraicGeometry.Space

end
