module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkGerm

/-!
# The vanishing criterion for a germ in the Zariski stalk of a chart restriction

The germ map from the sections of an `𝒪_X`-module over a Zariski open of an étale chart into the
Zariski stalk of its restriction to the chart is semilinear along the germ map of the structure
sheaf of the chart, and a section whose germ vanishes restricts to zero on a smaller open still
containing the point.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiSectionGermVanishingData`: the germ map with four facts.
* `AlgebraicGeometry.Space.chartZariskiSectionGermOfVanishing`: that germ map, which is
  `AlgebraicGeometry.Space.chartZariskiSectionGerm` by definition.

## Main results

* `AlgebraicGeometry.Space.chartZariskiSectionGermOfVanishing_smul`: semilinearity.
* `AlgebraicGeometry.Space.exists_restrict_eq_zero_of_chartZariskiSectionGermOfVanishing_eq_zero`:
  a section whose germ vanishes restricts to zero on a smaller open.

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The germ map from the sections of an `𝒪_X`-module over a Zariski open of an étale scheme
chart into the Zariski stalk of its restriction to the chart, together with four facts about it:
joint surjectivity, invariance under restriction to a smaller open, semilinearity along the
ordinary germ map of the structure sheaf of the chart, and the vanishing criterion — a section
whose germ is zero dies on a smaller open. -/
noncomputable def chartZariskiSectionGermVanishingData {x : GeometricPoint B S hS X}
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
            g W hw s) ∧
      (∀ (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
          (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))), g W hw s = 0 →
        ∃ (W' : (etaleChartScheme B S hS V.chart).Opens) (i : W' ⟶ W),
          chartPoint B S hS X V ∈ W' ∧
            F.val.map ((chartOpens B S hS V.chart).map i).op s = 0) } := by
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
  refine ⟨g, ?_, ?_, ?_, ?_⟩
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
  · intro W hw s hzero
    obtain ⟨W₁, i₁, y₁, -, hres⟩ :=
      (Stacks.moduleStalkLargeGerm_eq_iff pZ OU MU W ⟨⟨hw⟩⟩
        (unit.app (op W) (ULift.up s)) 0).mp (hzero.trans (map_zero _).symm)
    have hnat : unit.app (op W₁) (M₀.map i₁.op (ULift.up s)) = 0 :=
      (ConcreteCategory.congr_hom (unit.naturality i₁.op) (ULift.up s)).trans
        (hres.trans (map_zero _))
    obtain ⟨W₂, i₂, hi₂, y₂, -⟩ := pZ.jointly_surjective _
      (Presheaf.equalizerSieve_mem J unit (M₀.map i₁.op (ULift.up s))
        (0 : M₀.obj (op W₁)) (hnat.trans (map_zero _).symm)) y₁
    refine ⟨W₂, i₂ ≫ i₁, y₂.down.down, congrArg ULift.down ?_⟩
    exact (M₀.map_comp_apply i₁.op i₂.op (ULift.up s)).trans
      (hi₂.trans (map_zero _))

/-- The germ in the Zariski stalk of the restriction of `F` to the chart of a section of `F`
over a Zariski open of the chart containing the point under the chosen lift. -/
noncomputable def chartZariskiSectionGermOfVanishing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    F.val.obj (op ((chartOpens B S hS V.chart).obj W)) →+
      chartZariskiModuleStalk B S hS X hX V F :=
  chartZariskiSectionGerm B S hS hX V F W hw

/-- **The germ map is semilinear along the ordinary germ map of the chart.** The germ of a regular
function on a Zariski open of the chart acting on a section of `F` is the ordinary germ of that
function in the local ring of the chart acting on the germ of the section. -/
theorem chartZariskiSectionGermOfVanishing_smul {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, m} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (a : (etaleChartScheme B S hS V.chart).ringCatSheaf.obj.obj (op W))
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartZariskiSectionGermOfVanishing B S hS hX V F W hw
        ((show ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X hX).O)).obj.obj
            (op ((chartOpens B S hS V.chart).obj W)) from
          ((chartRestrictionRingHom B S hS hX V.chart).app (op W)).hom a) • s) =
      (etaleChartScheme B S hS V.chart).presheaf.germ W (chartPoint B S hS X V) hw a •
        chartZariskiSectionGermOfVanishing B S hS hX V F W hw s :=
  (chartZariskiSectionGermVanishingData B S hS hX V F).2.2.2.1 W hw a s

/-- **A section whose germ vanishes dies on a smaller open.** If the germ of a section of `F` over
a Zariski open of the chart vanishes in the Zariski stalk, then the section restricts to zero on
some smaller open still containing the point under the chosen lift. -/
theorem exists_restrict_eq_zero_of_chartZariskiSectionGermOfVanishing_eq_zero
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (F : Modules.{u, m} B S hS X hX) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W)
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W)))
    (hs : chartZariskiSectionGermOfVanishing B S hS hX V F W hw s = 0) :
    ∃ (W' : (etaleChartScheme B S hS V.chart).Opens) (i : W' ⟶ W),
      chartPoint B S hS X V ∈ W' ∧
        F.val.map ((chartOpens B S hS V.chart).map i).op s = 0 :=
  (chartZariskiSectionGermVanishingData B S hS hX V F).2.2.2.2 W hw s hs

end AlgebraicGeometry.Space

end
