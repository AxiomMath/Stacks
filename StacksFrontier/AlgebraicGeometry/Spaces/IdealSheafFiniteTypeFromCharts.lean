module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# Finite type of a sheaf of ideals from finite generation on the affine charts

Let `X` be an algebraic space and `N` a sheaf of ideals of `𝒪_X` on the small étale site, that
is, a `SheafOfModules.Submodule` of the unit.  Its sections over an étale chart `A` are the ideal
`AlgebraicGeometry.Space.chartIdeal`, and that ideal *is* the module of sections of the
associated sheaf of modules: the two are the same type, definitionally, so `Module.Finite` of the
one is `Submodule.FG` of the other with no transport.

This file records that dictionary and reads
`AlgebraicGeometry.Space.isFiniteTypeOnSite_of_coversTop_module_finite_sections` through it: a
sheaf of ideals cartesian on affine charts is of finite type on the small étale site as soon as
the ideal of its sections is finitely generated over the members of one covering family of affine
charts.

This is the form the chartwise readings consume.  The ideal cut out on a chart scheme by a closed
immersion is `AlgebraicGeometry.Space.idealSheafDataOfChart` of the defining ideal sheaf, whose
ideal over an affine open is `AlgebraicGeometry.Space.openChartIdeal`, the chart ideal of the
étale chart that open cuts out, transported along `AlgebraicGeometry.Scheme.Opens.topIso`; and
the kernel of the base-changed closed immersion of schemes is that ideal sheaf, by
`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`.

## Main results

* `AlgebraicGeometry.Space.module_finite_chartIdeal_iff_fg`: finiteness of the sections of the
  sheaf of modules of a sheaf of ideals over a chart is finite generation of the chart ideal.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_of_coversTop_fg_chartIdeal`: **a sheaf of ideals
  cartesian on affine charts whose chart ideals are finitely generated over one covering family
  of affine charts is of finite type on the small étale site.**
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_forall_fg_chartIdeal`: the equivalence with
  finite generation over *every* affine chart.

## Implementation notes

`AlgebraicGeometry.Space.chartIdeal` is the repository's spelling of `N.obj (op A)` as an ideal of
`AlgebraicGeometry.Space.chartRing`; its own implementation note records that the two spellings
are definitionally but not syntactically equal and that instance search is syntactic.  That is
exactly why the dictionary below is stated with `chartIdeal` on both sides: written against the
`structureRingSheaf` spelling of the ring of sections, the `Module` instance on the sections of
`N.toSheafOfModules` is not found at all, while `Module.Finite.iff_fg` applies on the nose once
the ideal is spelled through `chartIdeal`.

No declaration here carries a `stacks` attribute: this is the chartwise reading of a clause of
Stacks 03DL, an input to the tags that consume it, and not an assertion of a tag of its own.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The sections of the sheaf of modules of a sheaf of ideals over a chart form a finite module
exactly when the chart ideal is finitely generated.**  The two types are definitionally equal —
the sections of `N.toSheafOfModules` over `A` are the ideal `N.obj (op A)` — so this is
`Module.Finite.iff_fg`. -/
theorem module_finite_chartIdeal_iff_fg
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (A : SmallEtale B S hS X.1) :
    Module.Finite (chartRing B S hS X.1 X.2 A) (chartIdeal B S hS X N A) ↔
      (chartIdeal B S hS X N A).FG :=
  Module.Finite.iff_fg

/-- **A sheaf of ideals cartesian on affine charts whose chart ideals are finitely generated over
one covering family of affine charts is of finite type on the small étale site.**

This is `AlgebraicGeometry.Space.isFiniteTypeOnSite_of_coversTop_module_finite_sections` read
through `AlgebraicGeometry.Space.module_finite_chartIdeal_iff_fg`.  The covering family need not
be all of the affine charts: the affine opens of one surjective étale chart cover the site, by
`Stacks.Sites.coversTop_bind` applied to
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`, and that is the family the
chartwise readings supply. -/
theorem isFiniteTypeOnSite_of_coversTop_fg_chartIdeal
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    {I : Type (u + 1)} {Y : I → SmallEtale B S hS X.1}
    (hcov : (SmallEtale.topology B S hS X.1).CoversTop Y)
    (hYaff : ∀ j, IsAffine
      ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj (Y j)))
    (hfg : ∀ j, (chartIdeal B S hS X N (Y j)).FG) :
    SheafOfModules.IsFiniteTypeOnSite N.toSheafOfModules :=
  isFiniteTypeOnSite_of_coversTop_module_finite_sections N.toSheafOfModules hN hcov hYaff
    fun j => (module_finite_chartIdeal_iff_fg B S hS X N (Y j)).2 (hfg j)

/-- **Clause (5) of Stacks 03DL for a sheaf of ideals, read on the affine étale charts.**  For a
sheaf of ideals cartesian on affine charts, finite type on the small étale site is exactly finite
generation of the chart ideal over every affine étale chart. -/
theorem isFiniteTypeOnSite_iff_forall_fg_chartIdeal
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules) :
    SheafOfModules.IsFiniteTypeOnSite N.toSheafOfModules ↔
      ∀ A : SmallEtale B S hS X.1,
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
          (chartIdeal B S hS X N A).FG := by
  refine Iff.trans (isFiniteTypeOnSite_iff_module_finite_sections N.toSheafOfModules hN) ?_
  exact forall_congr' fun A => forall_congr' fun _ =>
    module_finite_chartIdeal_iff_fg B S hS X N A

end AlgebraicGeometry.Space

end
