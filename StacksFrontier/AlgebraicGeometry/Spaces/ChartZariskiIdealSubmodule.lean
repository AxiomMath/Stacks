module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealSheafSubmoduleBridge

/-!
# The Zariski restriction of a sheaf of ideals of an algebraic space, as a submodule of `𝒪_A`

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`N ⊆ 𝒪_X` be a sheaf of ideals on the small étale site of `X` and let `A` be an étale scheme
chart of `X`. This file defines the restriction of `N` to the small Zariski site of the chart's
scheme as a submodule of `𝒪_A`.

The sections of the chart restriction over a Zariski open `W` of the chart's scheme are the
sections of `N` over the étale chart which `W` cuts out, a module over `Γ(A, W)` through the
comparison of scalars `AlgebraicGeometry.Space.chartSectionsRingHom`, which is a ring
isomorphism. Pulling the ideal of sections back along it gives the ideal
`AlgebraicGeometry.Space.openChartIdeal` of `Γ(A, W)`, at every Zariski open `W`.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiIdealSheaf`: the Zariski restriction of a sheaf of ideals
  of `𝒪_X` to an étale scheme chart, as a submodule of `𝒪_A`, with ideal of sections
  `AlgebraicGeometry.Space.openChartIdeal` over a Zariski open `W`.

## Main results

* `AlgebraicGeometry.Space.chartSectionsRingHom_restrict`: the comparison of scalars is natural
  in the Zariski open.
* `AlgebraicGeometry.Space.mem_openChartIdeal_iff_chartSectionsRingHom_mem`: a regular function
  on `W` lies in the ideal which the chart inherits exactly when its image under the comparison
  of scalars is a section of `N` over the étale chart cut out by `W`.
* `AlgebraicGeometry.Space.chartZariskiIdealSheaf_eq_unitSubmodule_idealSheafDataOfChart`: for a
  sheaf of ideals cartesian on affine charts, `AlgebraicGeometry.Space.chartZariskiIdealSheaf` is
  `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` of
  `AlgebraicGeometry.Space.idealSheafDataOfChart`.

## Implementation notes

The restriction is taken at `AlgebraicGeometry.Space.openChartOfComparison`, the chart which `W`
becomes under the two comparison equivalences. It is equal, but not definitionally, to
`AlgebraicGeometry.Space.openChart`
(`AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`).

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Naturality of the comparison of scalars -/

/-- The comparison of scalars `AlgebraicGeometry.Space.chartSectionsRingHom` is natural in the
Zariski open: restricting a regular function on `W` to a smaller open `W'` and then comparing
scalars is the same as comparing scalars and then restricting along the morphism of étale charts
which the inclusion induces. -/
theorem chartSectionsRingHom_restrict (A : SmallEtale B S hS X.1)
    {W' W : (chartScheme A).Opens} (f : W' ⟶ W)
    (r : (chartScheme A).ringCatSheaf.obj.obj (op W)) :
    chartSectionsRingHom B S hS X A W'
        (((chartScheme A).ringCatSheaf.obj.map f.op).hom r) =
      ((structureRingSheaf B S hS X).obj.map
          ((chartComparisonFunctor B S hS X A).map f).op).hom
        (chartSectionsRingHom B S hS X A W r) :=
  congrArg (fun φ : (chartScheme A).ringCatSheaf.obj.obj (op W) ⟶
      (structureRingSheaf B S hS X).obj.obj (op (openChartOfComparison B S hS X A W')) =>
    φ.hom r) ((chartComparisonRingMap B S hS X A).hom.naturality f.op)

/-! ### The ideal which a Zariski open of the chart inherits -/

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-- A regular function on a Zariski open `W` of the chart's scheme lies in
`AlgebraicGeometry.Space.openChartIdeal` exactly when the comparison of scalars carries it into
the ideal of sections of `N` over the étale chart which `W` cuts out. -/
theorem mem_openChartIdeal_iff_chartSectionsRingHom_mem (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens)
    (r : Γ(chartScheme A, W)) :
    r ∈ openChartIdeal B S hS X N A W ↔
      chartSectionsRingHom B S hS X A W r ∈
        N.obj (op (openChartOfComparison B S hS X A W)) := by
  refine ⟨fun hr => (map_chartSectionsRingHom_openChartIdeal B S hS X N A W).le
    (Ideal.mem_map_of_mem _ hr), fun hr => ?_⟩
  have hmem := Ideal.mem_map_of_mem (openChartTopRingHom B S hS X A W) hr
  rw [openChartTopRingHom_chartSectionsRingHom B S hS X A W r] at hmem
  rwa [openChartIdeal_eq_map_chartSectionIdeal B S hS X N A W]

/-- The ideal `AlgebraicGeometry.Space.openChartIdeal` which a Zariski open of the chart's scheme
inherits from `N` is stable under restriction. -/
theorem mem_openChartIdeal_restrict (A : SmallEtale B S hS X.1)
    {W' W : (chartScheme A).Opens} (f : W' ⟶ W) (r : Γ(chartScheme A, W))
    (hr : r ∈ openChartIdeal B S hS X N A W) :
    ((chartScheme A).ringCatSheaf.obj.map f.op).hom r ∈ openChartIdeal B S hS X N A W' := by
  refine (mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W' _).2 ?_
  rw [chartSectionsRingHom_restrict B S hS X A f r]
  exact N.map_mem ((chartComparisonFunctor B S hS X A).map f).op
    ((mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W r).1 hr)

/-- If the restriction of a regular function `r` on `W` to a smaller open `W'` lies in the
inherited ideal there, then the comparison of scalars of `r`, restricted along the induced
morphism of étale charts, is a section of `N`. -/
theorem chartSectionsRingHom_restrict_mem (A : SmallEtale B S hS X.1)
    {W' W : (chartScheme A).Opens} (f : W' ⟶ W) (r : Γ(chartScheme A, W))
    (hr : ((chartScheme A).ringCatSheaf.obj.map f.op).hom r ∈
      openChartIdeal B S hS X N A W') :
    ((structureRingSheaf B S hS X).obj.map
        ((chartComparisonFunctor B S hS X A).map f).op).hom
          (chartSectionsRingHom B S hS X A W r) ∈
      N.obj (op (openChartOfComparison B S hS X A W')) := by
  rw [← chartSectionsRingHom_restrict B S hS X A f r]
  exact (mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W' _).1 hr

/-! ### The restriction as a submodule of the structure sheaf of the chart -/

/-- The Zariski restriction of a sheaf of ideals `N` of `𝒪_X` to an étale scheme chart `A`, as a
submodule of `𝒪_A`. Its ideal of sections over a Zariski open `W` of the chart's scheme is
`AlgebraicGeometry.Space.openChartIdeal`: the ideal of sections of `N` over the étale chart which
`W` cuts out, pulled back along the comparison of scalars
`AlgebraicGeometry.Space.chartSectionsRingHom`. -/
noncomputable def chartZariskiIdealSheaf (A : SmallEtale B S hS X.1) :
    (SheafOfModules.unit (chartScheme A).ringCatSheaf).Submodule where
  obj W := openChartIdeal B S hS X N A W.unop
  map g := fun r hr => mem_openChartIdeal_restrict B S hS X N A g.unop r hr
  isSheaf {W} s hs :=
    (mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W.unop s).2
      (N.isSheaf _
        (SmallEtale.mem_topology_openChartOfComparison_of_forall_nbhd B S hS X A _
          fun x hx =>
            let ⟨V, f, hf, hxV⟩ := hs x hx
            ⟨V, leOfHom f, hxV,
              chartSectionsRingHom_restrict_mem B S hS X N A f s hf⟩))

/-- The ideal of sections of the Zariski restriction over a Zariski open of the chart's scheme is
`AlgebraicGeometry.Space.openChartIdeal`. -/
theorem chartZariskiIdealSheaf_obj (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) :
    (chartZariskiIdealSheaf B S hS X N A).toSubmodule.obj (op W) =
      openChartIdeal B S hS X N A W :=
  rfl

/-- A regular function on a Zariski open `W` of the chart's scheme is a section of the
restriction exactly when the comparison of scalars carries it into the sections of `N` over the
étale chart which `W` cuts out. -/
theorem mem_chartZariskiIdealSheaf_iff (A : SmallEtale B S hS X.1)
    (W : (chartScheme A).Opens) (r : Γ(chartScheme A, W)) :
    r ∈ (chartZariskiIdealSheaf B S hS X N A).toSubmodule.obj (op W) ↔
      chartSectionsRingHom B S hS X A W r ∈
        N.obj (op (openChartOfComparison B S hS X A W)) :=
  mem_openChartIdeal_iff_chartSectionsRingHom_mem B S hS X N A W r

/-- The Zariski restriction of a sheaf of ideals cartesian on affine charts is the submodule
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` cut out by the chart ideal data
`AlgebraicGeometry.Space.idealSheafDataOfChart`. -/
theorem chartZariskiIdealSheaf_eq_unitSubmodule_idealSheafDataOfChart
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules) (A : SmallEtale B S hS X.1) :
    chartZariskiIdealSheaf B S hS X N A =
      (idealSheafDataOfChart B S hS X N hN A).unitSubmodule :=
  eq_unitSubmodule_idealSheafDataOfChart_of_obj_affine B S hS X N hN A
    (chartZariskiIdealSheaf B S hS X N A) fun _ => rfl

end AlgebraicGeometry.Space

end
