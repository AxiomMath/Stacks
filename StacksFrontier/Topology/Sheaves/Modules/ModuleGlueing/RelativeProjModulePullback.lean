module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChart
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjQuasicoherent

/-!
# Pulling the sheaves on a relative projective spectrum back along a morphism into a chart

The sheaf `ℳ̃` attached to a graded module on a relative projective spectrum, and the twisting
sheaves `𝒪(n)`, are glued from the sheaves attached to graded modules on the charts. So whenever a
morphism `h : T ⟶ Proj_S(𝒜)` out of a test scheme factors as `g ≫ chart W` through the chart over
an affine open `W` of the base, the pullback `h^*ℳ̃` is `g^*` of the sheaf of Tag 01M6 attached to
the graded module of sections of `ℳ` over `W`, and likewise for `𝒪(n)`.

Every morphism into the relative projective spectrum factors through a chart on a neighbourhood of
each point of its source, because the charts cover the spectrum; so the two comparisons describe
`h^*ℳ̃` and `h^*𝒪(n)` on a cover of `T` for an arbitrary `h`.

## Main definitions

* `Stacks.RelativeProj.Situation.moduleSheafPullbackChartIso`: **`h^*ℳ̃` is `g^*` of the chart
  sheaf**, for a factorization `h = g ≫ chart W` through the chart over `W`.
* `Stacks.RelativeProj.Situation.twistSheafPullbackChartIso`: the same for `𝒪(n)`.

## Main results

* `Stacks.RelativeProj.Situation.exists_chart_factorization`: **a morphism into the relative
  projective spectrum factors through a chart on a neighbourhood of each point of its source.**

## Implementation notes

This file identifies `h^*ℳ̃` with the pullback of the *chart* sheaf, the sheaf of Tag 01M6 of the
graded module of sections over an affine open of the base, not with the module `ℳ̃_T` of Tag 01O6
of a quadruple classifying `h`; the factorization through a chart is only local on `T`.
Property (1) of Tag 01O7 compares `h^*ℳ̃` with `ℳ̃_T`: on a chart datum that comparison is
`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`, the comparison
`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.chartIso` of `ℳ̃_T` with the pulled-back
chart sheaf followed by the inverse of `moduleSheafPullbackChartIso`.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules
open scoped Stacks.GradedLocalization

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} {T : Scheme.{u}}

/-- **A morphism into a relative projective spectrum factors through a chart on a neighbourhood of
each point of its source.** The neighbourhood is the preimage of the chart over any affine open of
the base whose chart contains the image of the point. -/
public theorem exists_chart_factorization (h : T ⟶ relativeProj s) (t : T) :
    ∃ (W : s.base.affineOpens) (V : T.Opens)
      (g : (V : Scheme.{u}) ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1)),
      t ∈ V ∧ V.ι ≫ h = g ≫ relativeProjChart s W :=
  Scheme.Modules.exists_factorization_of_iSup_opensRange_eq_top (relativeProjChart s)
    (iSup_opensRange_relativeProjChart s) h t

/-- **The `n`-th twisting sheaf of a relative projective spectrum, pulled back along a morphism
factoring through a chart.** If `h : T ⟶ Proj_S(𝒜)` factors as `g ≫ chart W`, then `h^*𝒪(n)` is
`g^*` of the absolute twisting sheaf `𝒪(n)` of `Proj 𝒜(W)`. -/
public def twistSheafPullbackChartIso (s : Situation.{u}) (n : ℤ) (W : s.base.affineOpens)
    (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) {h : T ⟶ relativeProj s}
    (hfac : h = g ≫ relativeProjChart s W) :
    (Scheme.Modules.pullback h).obj (twistSheaf s n)
      ≅ (Scheme.Modules.pullback g).obj (twistChart s n W) :=
  (twistGlueData (twistTransition s n)).pullbackChartIso W g hfac

variable (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- **`ℳ̃` pulled back along a morphism factoring through a chart.** If `h : T ⟶ Proj_S(𝒜)`
factors as `g ≫ chart W`, then `h^*ℳ̃` is `g^*` of the sheaf of Tag 01M6 attached to the graded
module of sections of `ℳ` over `W`.

The right-hand side is the chart sheaf, not the module `ℳ̃_T` of Tag 01O6 of a quadruple
classifying `h`. This isomorphism is the second factor of the comparison `ℳ̃_T ≅ h^*ℳ̃` of
property (1) of Tag 01O7 on a chart datum,
`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso`. -/
public def moduleSheafPullbackChartIso (W : s.base.affineOpens)
    (g : T ⟶ AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) {h : T ⟶ relativeProj s}
    (hfac : h = g ≫ relativeProjChart s W) :
    (Scheme.Modules.pullback h).obj (moduleSheaf ℳ)
      ≅ (Scheme.Modules.pullback g).obj (moduleChart ℳ W) :=
  (modulesDirectedGlueData ℳ).pullbackChartIso W g hfac

end Stacks.RelativeProj.Situation

end
