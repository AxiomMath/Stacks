module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorSurjective

/-!
# Germs of regular functions in the fibre at the point of the small étale site

Let `X` be an algebraic space over a scheme `S` and let `x̄` be a geometric point of `X`. The fibre
of the structure sheaf at the point of the small étale site determined by `x̄` is the étale local
ring `𝒪_{X, x̄}` up to `AlgebraicGeometry.Space.pointStalkRingEquiv`, but unlike the étale local
ring it lives in `CommRingCat.{u}` rather than `CommRingCat.{u + 1}`.

This file defines the germ map of regular functions on a small étale neighbourhood into the fibre
and proves its compatibility with refinement. It also reads the germ map of module sections over a
Zariski open of a chart with its scalars in the fibre rather than in the local ring of the chart.

## Main definitions

* `AlgebraicGeometry.Space.etalePointFiber` is the fibre of the structure sheaf at the point of
  the small étale site determined by a geometric point.
* `AlgebraicGeometry.Space.pointRingGerm` is the germ map of regular functions on a small étale
  neighbourhood into that fibre.
* `AlgebraicGeometry.Space.chartZariskiSectionGermLarge` is
  `AlgebraicGeometry.Space.chartZariskiSectionGerm` with its target declared as the Zariski
  stalk before the scalars are restricted.

## Main results

* `AlgebraicGeometry.Space.pointRingGerm_map`: the germ of a regular function is unchanged by
  restricting it to a smaller neighbourhood.
* `AlgebraicGeometry.Space.chartZariskiSectionGermLarge_smul`: the Zariski germ map is
  semilinear along the germ map of the structure sheaf of the chart into the fibre at the
  Zariski point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The fibre of the structure sheaf of the algebraic space at the point of the small étale
site determined by a geometric point. It is the étale local ring `𝒪_{X, x̄}` up to
`AlgebraicGeometry.Space.pointStalkRingEquiv`, formed one universe lower. -/
noncomputable abbrev etalePointFiber (x : GeometricPoint B S hS X) : CommRingCat.{u} :=
  ((etaleSitePoint B S hS X x hX).presheafFiber (A := CommRingCat.{u})).obj
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj

/-- The germ at the point of the small étale site of a regular function on a small étale
neighbourhood of the geometric point. -/
noncomputable def pointRingGerm {x : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood x) :
    chartRing B S hS X hX N.chart →+* ↥(etalePointFiber B S hS hX x) :=
  ((etaleSitePoint B S hS X x hX).toPresheafFiber N.chart ⟨N.point, N.point_comp⟩
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj).hom

/-- The germ of a regular function is unchanged by restricting it to a smaller small étale
neighbourhood. -/
theorem pointRingGerm_map {x : GeometricPoint B S hS X} {N M : SmallEtaleNeighborhood x}
    (φ : N ⟶ M) (a : chartRing B S hS X hX M.chart) :
    pointRingGerm B S hS hX N (chartRestrict (hF := hX) φ.hom a) =
      pointRingGerm B S hS hX M a :=
  ((etaleSitePoint B S hS X x hX).toPresheafFiber_w_apply φ.hom ⟨N.point, N.point_comp⟩
      (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj a).trans
    (congrArg (fun y => (etaleSitePoint B S hS X x hX).toPresheafFiber M.chart y
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O.obj a)
      (show (etaleSitePoint B S hS X x hX).fiber.map φ.hom ⟨N.point, N.point_comp⟩ =
        ⟨M.point, M.point_comp⟩ from Subtype.ext φ.point_comp))

/-- `AlgebraicGeometry.Space.chartZariskiSectionGerm` with its target declared as the Zariski
stalk before the scalars are restricted to the local ring of the chart. The two have the same
carrier. -/
noncomputable abbrev chartZariskiSectionGermLarge {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →+
      ↥(chartZariskiModuleStalkLarge B S hS hX V F) :=
  chartZariskiSectionGerm B S hS hX V F W hw

/-- The Zariski germ map on sections over an open of the chart is semilinear along the germ
map of the structure sheaf of the chart into the fibre at the Zariski point. -/
theorem chartZariskiSectionGermLarge_smul {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (r : (chartZariskiRingSheaf B S hS V).obj.obj (op W))
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartZariskiSectionGermLarge B S hS hX V F W hw
        ((show ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X hX).O)).obj.obj
            (op ((chartOpens B S hS V.chart).obj W)) from
          ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom r) • s) =
      (chartZariskiPoint B S hS X V).toPresheafFiber W ⟨⟨hw⟩⟩
          (chartZariskiRingSheaf B S hS V).obj r •
        chartZariskiSectionGermLarge B S hS hX V F W hw s :=
  (chartZariskiSectionGerm_smul B S hS hX V F W hw r s).trans <|
    congrArg (fun c => c • chartZariskiSectionGermLarge B S hS hX V F W hw s)
      (ConcreteCategory.congr_hom (Opens.germ_pointFiberStalkInv (chartPoint B S hS X V)
        (chartZariskiRingSheaf B S hS V).obj W hw) r)

end AlgebraicGeometry.Space

end
