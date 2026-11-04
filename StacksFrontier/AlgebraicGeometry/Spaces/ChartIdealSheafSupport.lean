module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerSections
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# The support of the sheaf of ideals a chart inherits from an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals on its small étale site which is cartesian on affine charts, and
let `A` be an étale scheme chart of `X`. `AlgebraicGeometry.Space.idealSheafDataOfChart` is the
Zariski `AlgebraicGeometry.Scheme.IdealSheafData` on the scheme of the chart whose ideal over an
affine open `V` is the ideal of sections of `ℐ` over the étale chart `V` cuts out. This file
describes its support in terms of `ℐ`.

## Main results

* `AlgebraicGeometry.Space.openChartIdeal_eq_top_iff`: the transported ideal over a Zariski open
  is the unit ideal exactly when `ℐ` is the whole structure sheaf over the étale chart that open
  cuts out.
* `AlgebraicGeometry.Space.chartIdeal_openChart_eq_top_iff_disjoint_support`: for an affine
  open `V` of the chart's scheme, `ℐ(V) = 𝒪_X(V)` exactly when `V` misses the support.
* `AlgebraicGeometry.Space.notMem_support_iff_exists_affineOpen_chartIdeal_eq_top` and
  `AlgebraicGeometry.Space.mem_support_compl_iff_exists_affineOpen`: a point of the chart's
  scheme lies off the support exactly when it lies in an affine open on which `ℐ` is the whole
  structure sheaf.
* `AlgebraicGeometry.Space.exists_affineOpens_le_chartIdeal_eq_top`: the affine opens on which
  `ℐ` is the whole structure sheaf cover the complement of the support, each inside a prescribed
  open contained in it.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-! ### The transport along the comparison of global functions is harmless -/

/-- The comparison `Γ(V, ⊤) → Γ(A, V)` along which the ideal of sections of a sheaf of ideals
is transported is bijective. -/
theorem bijective_openChartTopRingHom (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    Function.Bijective (openChartTopRingHom B S hS X A V) :=
  ConcreteCategory.bijective_of_isIso V.topIso.hom

/-- The ideal which the chartwise sheaf of ideals assigns to a Zariski open is the unit ideal
exactly when the sheaf of ideals is the whole structure sheaf over the étale chart that open cuts
out. -/
theorem openChartIdeal_eq_top_iff (A : SmallEtale B S hS X.1) (V : (chartScheme A).Opens) :
    openChartIdeal B S hS X N A V = ⊤ ↔ N.obj (op (openChart B S hS X.1 A V)) = ⊤ :=
  Ideal.map_eq_top_of_bijective _ (bijective_openChartTopRingHom B S hS X A V)

/-! ### The support, read on affine opens -/

variable (hN : IsCartesianOnAffineCharts N.toSheafOfModules)

/-- The ideal which `AlgebraicGeometry.Space.idealSheafDataOfChart` assigns to an affine open of
the chart's scheme is the unit ideal exactly when the sheaf of ideals is the whole structure
sheaf over the étale chart that open cuts out. -/
theorem ideal_idealSheafDataOfChart_eq_top_iff (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    (idealSheafDataOfChart B S hS X N hN A).ideal V = ⊤ ↔
      N.obj (op (openChart B S hS X.1 A V.1)) = ⊤ :=
  (congrArg (· = ⊤) (ideal_idealSheafDataOfChart B S hS X N hN A V)).to_iff.trans
    (openChartIdeal_eq_top_iff B S hS X N A V.1)

/-- An affine open of the chart's scheme which misses the support of the chartwise sheaf of
ideals carries the unit ideal of sections of `ℐ`. -/
theorem chartIdeal_openChart_eq_top_of_disjoint_support (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).affineOpens}
    (h : Disjoint (V.1 : Set (chartScheme A))
      ((idealSheafDataOfChart B S hS X N hN A).support : Set (chartScheme A))) :
    N.obj (op (openChart B S hS X.1 A V.1)) = ⊤ :=
  (ideal_idealSheafDataOfChart_eq_top_iff B S hS X N hN A V).1
    (Stacks.AlgebraicGeometry.IdealPower.ideal_eq_top_of_disjoint_support _ h)

/-- An affine open of the chart's scheme over which `ℐ` is the whole structure sheaf misses the
support of the chartwise sheaf of ideals. -/
theorem disjoint_support_of_chartIdeal_openChart_eq_top (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).affineOpens}
    (h : N.obj (op (openChart B S hS X.1 A V.1)) = ⊤) :
    Disjoint (V.1 : Set (chartScheme A))
      ((idealSheafDataOfChart B S hS X N hN A).support : Set (chartScheme A)) := by
  have htop : (idealSheafDataOfChart B S hS X N hN A).ideal V = ⊤ :=
    (ideal_idealSheafDataOfChart_eq_top_iff B S hS X N hN A V).2 h
  refine Set.disjoint_left.2 fun x hxV hxs => ?_
  have hz : x ∈ (chartScheme A).zeroLocus
      (U := V.1) ((idealSheafDataOfChart B S hS X N hN A).ideal V : Set Γ(chartScheme A, V.1)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hxV).1 hxs
  rw [Scheme.mem_zeroLocus_iff] at hz
  exact hz 1 (by simp [htop]) (by rwa [Scheme.basicOpen_one])

/-- For an affine open of the chart's scheme, `ℐ` is the whole structure sheaf over the étale
chart it cuts out exactly when it misses the support of the chartwise sheaf of ideals. -/
theorem chartIdeal_openChart_eq_top_iff_disjoint_support (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).affineOpens) :
    N.obj (op (openChart B S hS X.1 A V.1)) = ⊤ ↔
      Disjoint (V.1 : Set (chartScheme A))
        ((idealSheafDataOfChart B S hS X N hN A).support : Set (chartScheme A)) :=
  ⟨disjoint_support_of_chartIdeal_openChart_eq_top B S hS X N hN A,
    chartIdeal_openChart_eq_top_of_disjoint_support B S hS X N hN A⟩

/-! ### The support, read on points -/

/-- The sheaf of ideals is the whole structure sheaf over the étale chart cut out by the basic
open of a section of the transported ideal. -/
theorem chartIdeal_openChart_affineBasicOpen_eq_top (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).affineOpens} {f : Γ(chartScheme A, V.1)}
    (hf : f ∈ (idealSheafDataOfChart B S hS X N hN A).ideal V) :
    N.obj (op (openChart B S hS X.1 A ((chartScheme A).affineBasicOpen f).1)) = ⊤ := by
  refine (ideal_idealSheafDataOfChart_eq_top_iff B S hS X N hN A
    ((chartScheme A).affineBasicOpen f)).1 ?_
  rw [← (idealSheafDataOfChart B S hS X N hN A).map_ideal_basicOpen V f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    ((chartScheme A).toRingedSpace.isUnit_res_basicOpen f)

/-- A point of the chart's scheme lies off the support of the chartwise sheaf of ideals exactly
when it has an affine open neighbourhood over which `ℐ` is the whole structure sheaf. -/
theorem notMem_support_iff_exists_affineOpen_chartIdeal_eq_top (A : SmallEtale B S hS X.1)
    (x : chartScheme A) :
    x ∉ ((idealSheafDataOfChart B S hS X N hN A).support : Set (chartScheme A)) ↔
      ∃ V : (chartScheme A).affineOpens,
        x ∈ V.1 ∧ N.obj (op (openChart B S hS X.1 A V.1)) = ⊤ := by
  refine ⟨fun hx => ?_, fun ⟨V, hxV, hV⟩ => Set.disjoint_left.1
    (disjoint_support_of_chartIdeal_openChart_eq_top B S hS X N hN A hV) hxV⟩
  obtain ⟨V, hVmem, hxV, -⟩ :=
    Opens.isBasis_iff_nbhd.mp (chartScheme A).isBasis_affineOpens
      (show x ∈ (⊤ : (chartScheme A).Opens) from trivial)
  have hz : x ∉ (chartScheme A).zeroLocus (U := V)
      ((idealSheafDataOfChart B S hS X N hN A).ideal ⟨V, hVmem⟩ :
        Set Γ(chartScheme A, V)) := fun h =>
    hx ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hVmem⟩) hxV).2 h)
  rw [Scheme.mem_zeroLocus_iff] at hz
  push Not at hz
  obtain ⟨f, hfI, hxf⟩ := hz
  exact ⟨(chartScheme A).affineBasicOpen (U := ⟨V, hVmem⟩) f, hxf,
    chartIdeal_openChart_affineBasicOpen_eq_top B S hS X N hN A (SetLike.mem_coe.1 hfI)⟩

/-- A point of the chart's scheme lies in the complement of the support of the chartwise sheaf
of ideals exactly when it has an affine open neighbourhood over which `ℐ` is the whole structure
sheaf. -/
theorem mem_support_compl_iff_exists_affineOpen (A : SmallEtale B S hS X.1)
    (x : chartScheme A) :
    x ∈ ((idealSheafDataOfChart B S hS X N hN A).support.compl : (chartScheme A).Opens) ↔
      ∃ V : (chartScheme A).affineOpens,
        x ∈ V.1 ∧ N.obj (op (openChart B S hS X.1 A V.1)) = ⊤ :=
  notMem_support_iff_exists_affineOpen_chartIdeal_eq_top B S hS X N hN A x

/-- The affine opens over which `ℐ` is the whole structure sheaf cover the complement of the
support, each of them inside a prescribed open contained in that complement. -/
theorem exists_affineOpens_le_chartIdeal_eq_top (A : SmallEtale B S hS X.1)
    {W : (chartScheme A).Opens}
    (hW : W ≤ ((idealSheafDataOfChart B S hS X N hN A).support.compl : (chartScheme A).Opens))
    (x : chartScheme A) (hx : x ∈ W) :
    ∃ V : (chartScheme A).affineOpens,
      x ∈ V.1 ∧ V.1 ≤ W ∧ N.obj (op (openChart B S hS X.1 A V.1)) = ⊤ := by
  obtain ⟨V₀, hxV₀, -⟩ :=
    (mem_support_compl_iff_exists_affineOpen B S hS X N hN A x).1 (hW hx)
  obtain ⟨V, hVmem, hxV, hVle⟩ :=
    Opens.isBasis_iff_nbhd.mp (chartScheme A).isBasis_affineOpens
      (show x ∈ V₀.1 ⊓ W from ⟨hxV₀, hx⟩)
  exact ⟨⟨V, hVmem⟩, hxV, fun y hy => (hVle hy).2,
    chartIdeal_openChart_eq_top_of_disjoint_support B S hS X N hN A
      (V := ⟨V, hVmem⟩) (Set.disjoint_left.2 fun y hyV hys => hW (hVle hyV).2 hys)⟩

end AlgebraicGeometry.Space

end
