module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealFiniteType

/-!
# The Fitting closed subspaces of a module of finite presentation are of finite presentation

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be
a quasi-coherent `𝒪_X`-module of finite presentation.  The closed subspace `Z_r ⊆ X` cut out by
the `r`-th Fitting ideal sheaf of `G` is then of finite presentation over `X`.  This is the
closed-subspace half of the finite-presentation clause of Stacks 0CZ9 and of Stacks 0CZA.

## Main results

* `AlgebraicGeometry.Space.fg_definingIdealAt_of_isFinitePresentationOnSite`: over an affine
  étale chart the defining ideal of a Fitting closed subspace is finitely generated.
* `AlgebraicGeometry.Space.isFinitePresentation_fittingClosedSubspace`: **the finite-presentation
  clause of Stacks 0CZ9 for the closed subspaces `Z_r`.**

## Implementation notes

Over an affine étale chart the sections of the Fitting ideal sheaf are the module-theoretic
Fitting ideal of the sections of `G` there, which is
`AlgebraicGeometry.Space.fittingIdeal_obj_eq_fittingIdealOnChart` (Stacks 0CZ3), and that ideal
is finitely generated because the sections of a module of finite presentation over an affine
chart are a finitely presented module, which is
`AlgebraicGeometry.Space.fg_fittingIdealOnChart` (Stacks 07ZA).  Finite generation over the
affine charts is exactly what
`AlgebraicGeometry.Space.isFinitePresentation_subspaceInclusion_of_forall_fg_definingIdealAt`
asks for, so no comparison of finite type of the ideal sheaf on the small étale site with the
chart-level ideals is needed; in particular the hypothesis `hchart` of
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`
is not used here.

## References

* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 0CZA](https://stacks.math.columbia.edu/tag/0CZA)
* [Stacks Project, Tag 0CZ3](https://stacks.math.columbia.edu/tag/0CZ3)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The defining ideal of a Fitting closed subspace is finitely generated over every affine
étale chart.**  Over such a chart the sections of the `r`-th Fitting ideal sheaf of `G` are the
module-theoretic Fitting ideal of the sections of `G`, which is finitely generated because those
sections form a finitely presented module. -/
theorem fg_definingIdealAt_of_isFinitePresentationOnSite
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Y : ClosedSubspaces B S hS X.1) (r : ℕ)
    (hY : definingIdealSheaf B S hS X Y = fittingIdeal B S hS X.1 X.2 G r)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    (definingIdealAt B S hS X Y (op U)).FG := by
  have hfp := module_finitePresentation_sections_of_isFinitePresentationOnSite G hGqc hGfp
  have hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)) :=
    fun W hW => have := hfp W hW; inferInstance
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G hGqc
  have hfgchart : (@fittingIdealOnChart B S hS X.1 X.2 G r U (hfin U hU)).FG :=
    fg_fittingIdealOnChart G r (hfp U hU)
  rw [← fittingIdeal_obj_eq_fittingIdealOnChart G hcart hfin r hU] at hfgchart
  rw [show definingIdealAt B S hS X Y (op U) =
      (definingIdealSheaf B S hS X Y).toSubmodule.obj (op U) from rfl, hY]
  exact hfgchart

/-- **The finite-presentation clause of Stacks 0CZ9 for the closed subspaces of the chain.**  Let
`X` be an algebraic space over `S` and let `G` be a quasi-coherent `𝒪_X`-module of finite
presentation.  Then the inclusion of the closed subspace `Z_r ⊆ X` cut out by the `r`-th Fitting
ideal sheaf of `G` is a morphism of finite presentation.

Nothing beyond quasi-coherence and finite presentation of `G` is asked for.  Over an affine étale
chart the defining ideal of `Z_r` is the module-theoretic Fitting ideal of the sections of `G`,
hence finitely generated, and finite generation over the affine charts is exactly the criterion
`AlgebraicGeometry.Space.isFinitePresentation_subspaceInclusion_of_forall_fg_definingIdealAt`
deduces finite presentation from. -/
@[ega "IV 1.4.5" "closed subspace case"]
theorem isFinitePresentation_fittingClosedSubspace
    (X : AlgebraicSpaces B S hS) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGqc : G.IsQuasicoherentOnSite) (hGfp : SheafOfModules.IsFinitePresentationOnSite G)
    (Y : ClosedSubspaces B S hS X.1) (r : ℕ)
    (hY : definingIdealSheaf B S hS X Y = fittingIdeal B S hS X.1 X.2 G r) :
    IsFinitePresentation B S hS (subspaceInclusion B S hS X Y).hom :=
  isFinitePresentation_subspaceInclusion_of_forall_fg_definingIdealAt B S hS X Y
    fun U hU => fg_definingIdealAt_of_isFinitePresentationOnSite B S hS X G hGqc hGfp Y r hY U hU

end AlgebraicGeometry.Space

end
