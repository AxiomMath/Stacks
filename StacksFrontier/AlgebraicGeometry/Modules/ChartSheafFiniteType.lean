module

public import StacksFrontier.AlgebraicGeometry.Modules.AffineChartSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison

/-!
# The chart sheaf of a finite module is of finite type on its chart

`Stacks.Modules.chartSheaf V M` is the sheaf of `𝒪_Y`-modules determined by a module `M` over
the ring of functions on an affine open `V` of a scheme `Y`. That file records that its
restriction to the open subscheme `V` is quasi-coherent; this one records the other half of what
a construction by glueing asks of a chart, namely that the restriction is of finite type as soon
as `M` is a finite module.

Both facts are proved the same way, from the identification of that restriction with a pullback
of Serre's sheaf `M^~` along the isomorphism `V ≅ Spec Γ(Y, V)`
(`Stacks.Modules.restrictChartSheafIso`): finite type of `M^~` is finiteness of `M`
(`AlgebraicGeometry.tilde_isFiniteType_iff`), finite type is preserved by pullback along a
morphism of ringed spaces (Tag 01B6), and it is invariant under isomorphism.

Together with `Stacks.Modules.isQuasicoherent_restrict_chartSheaf` this discharges both local
hypotheses of `Stacks.Modules.exists_coherent_glued_of_basisComparison` for a family of chart
sheaves, leaving only the comparison data on the adapted opens.

## Main results

* `Stacks.Modules.isFiniteType_restrict_chartSheaf`.

## References

* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Modules

/-- **The chart sheaf of a finite module is of finite type on its chart.** For an affine open `V`
of a scheme `Y` and a finite `Γ(Y, V)`-module `M`, the restriction of `chartSheaf V M` to the open
subscheme `V` is a sheaf of modules of finite type. -/
public theorem isFiniteType_restrict_chartSheaf {Y : Scheme.{u}} (V : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, V.1)) (hM : Module.Finite Γ(Y, V.1) M) :
    ((chartSheaf V M).restrict V.1.ι).IsFiniteType := by
  have htilde : (AlgebraicGeometry.tilde M).IsFiniteType :=
    (AlgebraicGeometry.tilde_isFiniteType_iff M).2 hM
  have hpull : ((Scheme.Modules.pullback V.2.isoSpec.hom).obj
      (AlgebraicGeometry.tilde M)).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
      V.2.isoSpec.hom.toLRSHom.toShHom (AlgebraicGeometry.tilde M)
  exact Stacks.Coherent.isFiniteType_of_iso_local (restrictChartSheafIso V M).symm hpull

end Stacks.Modules

end
