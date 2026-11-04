module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartClsAnyCount
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartFractionDeRham
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechClassPassage

/-!
# The class-map half of Stacks 0G87, for any number of equations

`Stacks.Gysin.ChartFractionCommutesWithDeRham` is the class-map half of the one hypothesis of
[Stacks, Tag 0G87] — on a chart, the class map of [Stacks, Tag 0G7Q] of the chart's own equations
is natural along the restriction to the chart of the relative de Rham differential of `X/S`, on
the equation wedges.  It is stated with
`Stacks.Perfect.SupportedFraction.supportedFractionSource` and so only for `c = d + 1`: that map
factors through the cokernel of the differential of the extended alternating Čech complex into
its *top* degree, and an empty family of equations gives a complex with only degree `0` and no
such differential.

This file restates and proves it with `Stacks.Perfect.FractionClass.classMapToSupport`, the same
map of [Stacks, Tag 0G7Q] built without a top differential, and so for **every** `c`, zero
included.  It then carries the chart square and its reading on sections across the same
substitution, which is what the `c = 0` case of [Stacks, Tag 0G87] needs: at conormal rank `0` a
chart carries an empty family of equations.

## What is new here, and what is not

**The localized Leibniz rule is not reproved.**  Its chart-level form,
`Stacks.Gysin.sectionsHom_chartDeRhamShift_smul_gysinWedge`, is already stated for an arbitrary
number of equations — as is everything it rests on, down to
`AlgebraicGeometry.SheafOfModules.d_smul_formProduct_prodDegOne_of_mul_eq_one`.  What was missing
was the passage from that identity on sections to the class map at an arbitrary `c`, and that is
`Stacks.Perfect.AbelianCechClassPassage.classMapToSupport_comm_of_smul`, proved in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AbelianCechClassPassage.lean`.  This
file does nothing but feed it to the chart.

**The excision half is already general.**  `Stacks.Gysin.SupportCohomologyRestrictAbNatural` and
`Stacks.Gysin.supportCohomologyRestrictIso` take a plain `n : ℕ`, and
`Stacks.Gysin.supportCohomologyRestrictAbNatural` proves the first for an arbitrary morphism of
the underlying abelian sheaves at every `n`.  So nothing about the passage from the chart to `X`
has to be redone.

**The formal chases are shared, not copied.**  `Stacks.Gysin.chart_square_formal`,
`Stacks.Gysin.conj_inv_square`, `Stacks.Gysin.abRestrictSections_comp3_right` and
`Stacks.Gysin.abRestrictSections_comp3_middle` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamClsReduction.lean` mention neither the
number of equations nor the equations themselves; they were `private` there and are now public, so
the squares below are chased by the same four lemmas the `c = d + 1` squares are chased by rather
than by four copies of them.

## Main definitions

* `Stacks.Gysin.ChartFractionCommutesWithDeRhamOfClassMap`: **the class-map half of the one
  hypothesis of [Stacks, Tag 0G87], for any number of equations.**  This is
  `Stacks.Gysin.ChartFractionCommutesWithDeRham` with `supportedFractionSource` replaced by
  `Stacks.Perfect.FractionClass.classMapToSupport`.

## Main results

* `Stacks.Gysin.map_comp_classMapToSupport_comm_of_smul`: the localized Leibniz rule for the class
  map of [Stacks, Tag 0G7Q] with the factor an `𝒪_Y`-linear morphism, which is the shape the
  chart's equation wedge takes.
* `Stacks.Gysin.chartFractionCommutesWithDeRhamOfClassMap`: **the class-map half holds, for every
  chart, every degree and every number of equations**, with no hypothesis beyond the data the
  chart carries.
* `Stacks.Gysin.chartClsSquareOfClassMap_of_excision`: **the square of [Stacks, Tag 0G87] on a
  chart, for any number of equations**, from the excision half alone.
* `Stacks.Gysin.abSectionsHom_gysinTargetDeRhamHom_chartClsOfClassMap`: the same read on the
  sections over an open of the ambient scheme contained in the chart.

## Implementation notes

**Why the two squares are restated rather than generalised in place.**
`Stacks.Gysin.chartClsSquare_of_excision_of_chartFraction` and
`Stacks.Gysin.abSectionsHom_gysinTargetDeRhamHom_chartCls` are about
`Stacks.Gysin.chartClsHom`, which does not exist at `c = 0`; the statements here are about
`Stacks.Gysin.chartClsHomOfClassMap`, which does.  Neither is an instance of the other, so both
are kept, and the original ones keep their consumers unchanged.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G87]; `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` does, and carries the tag.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom sectionsHom)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.FractionClass (classMapToSupport)
open Stacks.Perfect.GysinAbelianSquare (supportCohomologySheafAbelianMap)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The localized Leibniz rule with an `𝒪_Y`-linear factor -/

/-- **`Stacks.Perfect.AbelianCechClassPassage.classMapToSupport_comm_of_smul` with the factor an
`𝒪_Y`-linear morphism**, in which shape the two composites are the two sides of
`Stacks.Gysin.ChartFractionCommutesWithDeRhamOfClassMap`: the wedge factor of the Gysin formula is
`𝒪_X`-linear, and only the differential is not.

This is `Stacks.Gysin.map_comp_supportedFractionSource_comm_of_smul` with the `c = d + 1`
removed. -/
theorem map_comp_classMapToSupport_comm_of_smul {Y : Scheme.{u}} {c : ℕ}
    (e : Fin c → Γ(Y, ⊤)) {E F G : Y.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (uu : E ⟶ F)
    (h : ∀ (V : Y.Opens) (v : Γ(Y, V)) (y : Γ(E, V)),
      Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, e j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom (Scheme.Modules.Hom.mapPresheaf uu) V y) =
        v • sectionsHom ψ V (sectionsHom (Scheme.Modules.Hom.mapPresheaf uu) V y))
    {T : Set Y} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    (abelianSheaf Y).map uu ≫ (abelianSheaf Y).map (classMapToSupport e F hT hTe) ≫
        supportCohomologySheafAbelianMap hT c (abHom ψ) =
      (abelianSheaf Y).map uu ≫ abHom ψ ≫
        (abelianSheaf Y).map (classMapToSupport e G hT hTe) := by
  have hgen := Stacks.Perfect.AbelianCechClassPassage.classMapToSupport_comm_of_smul e ψ
    (Scheme.Modules.Hom.mapPresheaf uu) (Scheme.Modules.Hom.mapPresheaf uu ≫ ψ)
    (fun V v y hv => h V v y hv) hT hTe
  rw [← Category.assoc ((abelianSheaf Y).map uu) (abHom ψ)]
  exact hgen

/-! ### The class-map half, for any number of equations -/

variable {Z X S : Scheme.{u}}

/-- The relative differential forms of degree `p + c` are quasi-coherent. -/
private instance isQuasicoherent_relativeDifferentialForms_natCast_add' {X S : Scheme.{u}}
    (π : X ⟶ S) (p c : ℕ) : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
  isQuasicoherent_relativeDifferentialForms_natCast_add π p c

/-- **The class-map half of the one hypothesis of [Stacks, Tag 0G87], for any number of
equations**: on the chart `W`, where the equations are global sections and [Stacks, Tag 0G7Q]
applies verbatim, the class map `Stacks.Perfect.FractionClass.classMapToSupport` is natural along
the relative de Rham differential of `X/S` restricted to the chart, **on the equation wedges**,
the local cohomology sheaf of the chart acting on the differential through [Stacks, Tag 0G74]
part (2).

This is `Stacks.Gysin.ChartFractionCommutesWithDeRham` with
`Stacks.Perfect.SupportedFraction.supportedFractionSource` replaced by
`Stacks.Perfect.FractionClass.classMapToSupport`, which is the same map of [Stacks, Tag 0G7Q]
built without the top Čech differential and therefore available at `c = 0`.  Everything else is
unchanged, including that no excision occurs in it: both sides are morphisms of abelian sheaves on
`W.toScheme` between the restrictions to `W` of the forms of `X/S` and the local cohomology
sheaves taken *on the chart*.

The wedge `Stacks.Gysin.gysinWedgeOnHom` on the left of both composites is not a convenience: at
an arbitrary section the equation is *false*, see the counterexample in the implementation notes
of `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamCompat.lean`. -/
def ChartFractionCommutesWithDeRhamOfClassMap (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {c : ℕ} (p : ℕ) (W : X.Opens) (g : Fin c → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base) : Prop :=
  haveI : (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π p c
  haveI : (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms_natCast_add π (p + 1) c
  (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
      (abelianSheaf W.toScheme).map
          (classMapToSupport (restrictEquations W g)
            (Scheme.Modules.restrict
              (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) W.ι) hTW hTf) ≫
        supportCohomologySheafAbelianMap hTW c
          (restrictAbHom W (ambientDeRhamShiftAbHom π c p)) =
    (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
      restrictAbHom W (ambientDeRhamShiftAbHom π c p) ≫
        (abelianSheaf W.toScheme).map
          (classMapToSupport (restrictEquations W g)
            (Scheme.Modules.restrict
              (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))) W.ι) hTW hTf)

/-- **The class-map half of the one hypothesis of [Stacks, Tag 0G87] holds, for any number of
equations.**

This is `Stacks.Gysin.chartFractionCommutesWithDeRham` with the `c = d + 1` removed.  Its two
inputs are both already general: the localized Leibniz rule of the chart,
`Stacks.Gysin.sectionsHom_chartDeRhamShift_smul_gysinWedge`, which is stated for an arbitrary
number of equations, and the passage from it to the class map,
`map_comp_classMapToSupport_comm_of_smul`. -/
theorem chartFractionCommutesWithDeRhamOfClassMap (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens) (g : Fin c → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base) :
    ChartFractionCommutesWithDeRhamOfClassMap i π p W g hTW hTf := by
  exact map_comp_classMapToSupport_comm_of_smul (restrictEquations W g)
    (chartDeRhamShiftPresheafHom π W c p) (gysinWedgeOnHom π g (p : ℤ))
    (fun V v y hv => sectionsHom_chartDeRhamShift_smul_gysinWedge π g p V v y hv) hTW hTf

/-! ### The square on a chart, for any number of equations -/

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- `Stacks.Gysin.chartClsOfClassMap` is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictSections` of
`Stacks.Gysin.chartClsHomOfClassMap`, exactly as `Stacks.Gysin.chartCls_eq_restrictSections`
reads `Stacks.Gysin.chartCls` off `Stacks.Gysin.chartClsHom`: both read a morphism of the
restrictions to `W` on the sections over an open `V ≤ W`. -/
theorem chartClsOfClassMap_eq_restrictSections (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    {c : ℕ} (p : ℕ) (W : X.Opens) (f : Fin c → Γ(W.toScheme, ⊤))
    (hT : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet f ⊆ W.ι ⁻¹' Set.range i.base)
    (V : X.Opens) (hV : V ≤ W)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)) :
    chartClsOfClassMap i π p W f hT hTf V hV y =
      restrictSections (chartClsHomOfClassMap i π p W f hT hTf) V hV y :=
  rfl

/-- **The square of [Stacks, Tag 0G87] on a chart, for any number of equations**, from the
excision half alone.  The chart class map `Stacks.Gysin.chartClsHomOfClassMap` is the class map of
[Stacks, Tag 0G7Q] of the chart's own equations followed by the derived excision of
[Stacks, Tag 0G78]; the class-map half `chartFractionCommutesWithDeRhamOfClassMap` is the square
for the first factor and the excision half, conjugated into the inverse direction, carries it
across the second.

This is `Stacks.Gysin.chartClsSquare_of_excision_of_chartFraction` with the `c = d + 1` removed
and its class-map hypothesis discharged; the chase is the shared
`Stacks.Gysin.chart_square_formal`. -/
theorem chartClsSquareOfClassMap_of_excision (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens) (g : Fin c → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base)
    (hexc : SupportCohomologyRestrictAbNatural W (isClosed_range_base i) hTW c
      (ambientDeRhamShiftAbHom π c p)) :
    (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
        (abelianSheaf W.toScheme).map
            (chartClsHomOfClassMap i π p W (restrictEquations W g) hTW hTf) ≫
          restrictAbHom W (gysinTargetDeRhamHom i π c p) =
      (abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
        restrictAbHom W (ambientDeRhamShiftAbHom π c p) ≫
          (abelianSheaf W.toScheme).map
            (chartClsHomOfClassMap i π (p + 1) W (restrictEquations W g) hTW hTf) := by
  exact chart_square_formal
    ((abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)))
    ((abelianSheaf W.toScheme).map
      (classMapToSupport (restrictEquations W g)
        (Scheme.Modules.restrict
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) W.ι) hTW hTf))
    ((abelianSheaf W.toScheme).map
      (classMapToSupport (restrictEquations W g)
        (Scheme.Modules.restrict
          (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))) W.ι) hTW hTf))
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW (c : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).hom)
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW (c : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).inv)
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW (c : ℤ)
        (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ)))).hom)
    ((abelianSheaf W.toScheme).map
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW (c : ℤ)
        (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ)))).inv)
    (restrictAbHom W (ambientDeRhamShiftAbHom π c p))
    (supportCohomologySheafAbelianMap hTW c
      (restrictAbHom W (ambientDeRhamShiftAbHom π c p)))
    (restrictAbHom W (gysinTargetDeRhamHom i π c p))
    (((abelianSheaf W.toScheme).mapIso
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW (c : ℤ)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))).inv_hom_id)
    (((abelianSheaf W.toScheme).mapIso
      (supportCohomologyRestrictIso W (isClosed_range_base i) hTW (c : ℤ)
        (relativeDifferentialForms π (((p + 1 : ℕ) : ℤ) + (c : ℤ))))).hom_inv_id)
    hexc (chartFractionCommutesWithDeRhamOfClassMap i π p W g hTW hTf)

/-- **The class map of a chart commutes with the de Rham differential on the equation wedges, on
sections over an open of the chart, for any number of equations**, from the excision half alone.

This is `Stacks.Gysin.abSectionsHom_gysinTargetDeRhamHom_chartCls` with the `c = d + 1` removed:
`chartClsSquareOfClassMap_of_excision` read over an open `V ≤ W` of the ambient scheme through
`Stacks.Gysin.abRestrictSections`, which is where the vertical arrows of the square of
[Stacks, Tag 0G87] — morphisms of abelian sheaves on `X` — meet a square proved on the chart. -/
theorem abSectionsHom_gysinTargetDeRhamHom_chartClsOfClassMap (i : Z ⟶ X)
    [IsClosedImmersion i] (π : X ⟶ S) {c : ℕ} (p : ℕ) (W : X.Opens) (g : Fin c → Γ(X, W))
    (hTW : IsClosed (W.ι ⁻¹' Set.range i.base))
    (hTf : equationsClosedSet (restrictEquations W g) ⊆ W.ι ⁻¹' Set.range i.base)
    (hexc : SupportCohomologyRestrictAbNatural W (isClosed_range_base i) hTW c
      (ambientDeRhamShiftAbHom π c p))
    (V : X.Opens) (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    abSectionsHom (gysinTargetDeRhamHom i π c p) V
        (chartClsOfClassMap i π p W (restrictEquations W g) hTW hTf V hV
          (gysinWedgeOn π g (p : ℤ) hV ω))
      = chartClsOfClassMap i π (p + 1) W (restrictEquations W g) hTW hTf V hV
          (ambientDeRhamShift π c p V (gysinWedgeOn π g (p : ℤ) hV ω)) := by
  have h : abRestrictSections W
        ((abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
          (abelianSheaf W.toScheme).map
              (chartClsHomOfClassMap i π p W (restrictEquations W g) hTW hTf) ≫
            restrictAbHom W (gysinTargetDeRhamHom i π c p)) V hV ω
      = abRestrictSections W
        ((abelianSheaf W.toScheme).map (gysinWedgeOnHom π g (p : ℤ)) ≫
          restrictAbHom W (ambientDeRhamShiftAbHom π c p) ≫
            (abelianSheaf W.toScheme).map
              (chartClsHomOfClassMap i π (p + 1) W (restrictEquations W g) hTW hTf)) V hV ω :=
    congrArg (fun θ => abRestrictSections W θ V hV ω)
      (chartClsSquareOfClassMap_of_excision i π p W g hTW hTf hexc)
  rw [abRestrictSections_comp3_right, abRestrictSections_comp3_middle,
    restrictSections_gysinWedgeOnHom] at h
  rw [chartClsOfClassMap_eq_restrictSections, chartClsOfClassMap_eq_restrictSections,
    ← abSectionsHom_ambientDeRhamShiftAbHom]
  exact h

end Stacks.Gysin

end
