module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkPointDescent

/-!
# Germs in the Zariski stalk of the restriction of a module to an étale chart

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module, let `x̄` be a
geometric point of `X` and let `V` be a small étale neighbourhood of `x̄` whose chart is a scheme
`U`. A section of `F` over a Zariski open `W` of `U` — that is, over the étale chart
`AlgebraicGeometry.Space.chartOpens` of `W` — has a germ in the Zariski stalk
`AlgebraicGeometry.Space.chartZariskiModuleStalk`. This file defines that germ map and proves the
three facts which characterise it: every element of the Zariski stalk is such a germ, the germ is
unchanged by restricting to a smaller open, and the germ map is semilinear along the ordinary germ
map of the structure sheaf of the chart.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiSectionGerm` is the germ map from the sections of `F` over
  a Zariski open of the chart into the Zariski stalk of the restriction of `F` to the chart.

## Main results

* `AlgebraicGeometry.Space.chartZariskiSectionGerm_jointly_surjective`: every element of the
  Zariski stalk is the germ of a section of `F` over some Zariski open of the chart containing
  the point.
* `AlgebraicGeometry.Space.chartZariskiSectionGerm_map`: the germ of a section is unchanged by
  restricting the section to a smaller open.
* `AlgebraicGeometry.Space.chartZariskiSectionGerm_smul`: the germ map is semilinear along the
  ordinary germ map `𝒪_U(W) → 𝒪_{U, u}` of the structure sheaf of the chart.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The germ map from the sections of an `𝒪_X`-module over a Zariski open of an étale scheme
chart into the Zariski stalk of its restriction to the chart, together with the three facts
which characterise it: joint surjectivity, invariance under restriction to a smaller open, and
semilinearity along the ordinary germ map of the structure sheaf of the chart. -/
noncomputable def chartZariskiSectionGermData {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX) :
    { g : ∀ (W : (etaleChartScheme B S hS V.chart).Opens), chartPoint B S hS X V ∈ W →
        F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →+
          chartZariskiModuleStalk B S hS X hX V F //
      (∀ z, ∃ (W : (etaleChartScheme B S hS V.chart).Opens)
          (hw : chartPoint B S hS X V ∈ W)
          (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))), g W hw s = z) ∧
      (∀ (W W' : (etaleChartScheme B S hS V.chart).Opens) (i : W' ⟶ W)
          (hw' : chartPoint B S hS X V ∈ W') (hw : chartPoint B S hS X V ∈ W)
          (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))),
        g W' hw' (F.val.map ((chartOpens B S hS V.chart).map i).op s) = g W hw s) ∧
      (∀ (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
          (a : (etaleChartScheme B S hS V.chart).ringCatSheaf.obj.obj (op W))
          (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))),
        g W hw ((show ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X hX).O)).obj.obj
              (op ((chartOpens B S hS V.chart).obj W)) from
            ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom a) • s) =
          (etaleChartScheme B S hS V.chart).presheaf.germ W (chartPoint B S hS X V) hw a •
            g W hw s) } := by
  let Y := etaleChartScheme B S hS V.chart
  let J := Opens.grothendieckTopology Y
  let M₀ := chartRestrictionPresheaf B S hS hX F V.chart
  let MU := restrictToChart B S hS hX F V.chart
  let OU : Sheaf J CommRingCat.{u} := Y.sheaf
  let pZ : J.Point.{u} := chartZariskiPoint B S hS X V
  letI : HasSheafify J AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  let unit : M₀.presheaf ⟶ MU.val.presheaf := CategoryTheory.toSheafify J M₀.presheaf
  haveI : Presheaf.IsLocallySurjective J unit :=
    (inferInstance : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J M₀.presheaf))
  haveI : Presheaf.IsLocallyInjective J unit :=
    (inferInstance : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M₀.presheaf))
  let unitMod : M₀ ⟶ (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj MU.val :=
    PresheafOfModules.toSheafify _ unit
  have hlin : ∀ (W : Y.Opens) (a : Y.ringCatSheaf.obj.obj (op W)) (t : M₀.obj (op W)),
      unit.app (op W) (a • t) = a • unit.app (op W) t :=
    fun W a t => (unitMod.app (op W)).hom.map_smul a t
  let up : ∀ (W : Y.Opens),
      F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →+ M₀.obj (op W) :=
    fun _ => AddMonoidHom.mk' ULift.up (fun _ _ => rfl)
  let g : ∀ (W : Y.Opens), chartPoint B S hS X V ∈ W →
      F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →+
        chartZariskiModuleStalk B S hS X hX V F := fun W hw =>
    ((Stacks.moduleStalkLargeGerm pZ OU MU W ⟨⟨hw⟩⟩).comp (unit.app (op W)).hom).comp (up W)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨W, y, t, ht⟩ :=
      Stacks.moduleStalkLargeGerm_exists_of_locallyBijective pZ OU MU unit z
    exact ⟨W, y.down.down, t.down, ht⟩
  · intro W W' i hw' hw s
    refine Eq.trans ?_ ((Stacks.moduleStalkLargeGerm_w pZ OU MU i ⟨⟨hw'⟩⟩
      (unit.app (op W) (ULift.up s))).trans rfl)
    exact congrArg (Stacks.moduleStalkLargeGerm pZ OU MU W' ⟨⟨hw'⟩⟩)
      (ConcreteCategory.congr_hom (unit.naturality i.op) (ULift.up s))
  · intro W hw a s
    have h1 : unit.app (op W) (ULift.up
          ((show ((Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite B S hS X hX).O)).obj.obj
              (op ((chartOpens B S hS V.chart).obj W)) from
            ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom a) • s)) =
        a • unit.app (op W) (ULift.up s) := hlin W a (ULift.up s)
    refine Eq.trans (congrArg (Stacks.moduleStalkLargeGerm pZ OU MU W ⟨⟨hw⟩⟩) h1) ?_
    refine Eq.trans (Stacks.moduleStalkLargeGerm_smul pZ OU MU W ⟨⟨hw⟩⟩ a
      (unit.app (op W) (ULift.up s))) ?_
    exact congrArg (fun c : (pZ.presheafFiber (A := CommRingCat.{u})).obj OU.obj =>
        c • Stacks.moduleStalkLargeGerm pZ OU MU W ⟨⟨hw⟩⟩ (unit.app (op W) (ULift.up s)))
      (ConcreteCategory.congr_hom
        (Opens.germ_pointFiberStalkInv (chartPoint B S hS X V) Y.presheaf W hw) a).symm

/-- The germ in the Zariski stalk of the restriction of `F` to the chart of a section of `F`
over a Zariski open of the chart containing the point under the chosen lift. -/
noncomputable def chartZariskiSectionGerm {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →+
      chartZariskiModuleStalk B S hS X hX V F :=
  (chartZariskiSectionGermData B S hS hX V F).1 W hw

/-- **Every element of the Zariski stalk is a germ.** Each element of the Zariski stalk of the
restriction of `F` to the chart is the germ of a section of `F` over some Zariski open of the
chart containing the point under the chosen lift. -/
theorem chartZariskiSectionGerm_jointly_surjective {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (z : chartZariskiModuleStalk B S hS X hX V F) :
    ∃ (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
      (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))),
      chartZariskiSectionGerm B S hS hX V F W hw s = z :=
  (chartZariskiSectionGermData B S hS hX V F).2.1 z

/-- The germ of a section of `F` over a Zariski open of the chart is unchanged by restricting
the section to a smaller open which still contains the point. -/
theorem chartZariskiSectionGerm_map {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W W' : (etaleChartScheme B S hS V.chart).Opens) (i : W' ⟶ W)
    (hw' : chartPoint B S hS X V ∈ W') (hw : chartPoint B S hS X V ∈ W)
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartZariskiSectionGerm B S hS hX V F W' hw'
        (F.val.map ((chartOpens B S hS V.chart).map i).op s) =
      chartZariskiSectionGerm B S hS hX V F W hw s :=
  (chartZariskiSectionGermData B S hS hX V F).2.2.1 W W' i hw' hw s

/-- **The germ map is semilinear along the ordinary germ map of the chart.** The germ of a
regular function on a Zariski open of the chart acting on a section of `F` is the ordinary germ
of that function in the local ring of the chart acting on the germ of the section. -/
theorem chartZariskiSectionGerm_smul {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (a : (etaleChartScheme B S hS V.chart).ringCatSheaf.obj.obj (op W))
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartZariskiSectionGerm B S hS hX V F W hw
        ((show ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X hX).O)).obj.obj
            (op ((chartOpens B S hS V.chart).obj W)) from
          ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom a) • s) =
      (etaleChartScheme B S hS V.chart).presheaf.germ W (chartPoint B S hS X V) hw a •
        chartZariskiSectionGerm B S hS hX V F W hw s :=
  (chartZariskiSectionGermData B S hS hX V F).2.2.2 W hw a s

end AlgebraicGeometry.Space

end
