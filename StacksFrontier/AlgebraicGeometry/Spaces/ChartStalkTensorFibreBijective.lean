module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorFibreInverse

/-!
# The comparison map of Stacks 05VP is bijective over the fibre at the point

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module and
let `x̄` be a geometric point with small étale neighbourhood `V`.  Fix a Zariski open `W` of the
chart of `V` containing the point under the chosen lift and whose étale chart is affine.  This
file proves that `AlgebraicGeometry.Space.chartStalkTensorFibreComparison` and
`AlgebraicGeometry.Space.chartStalkTensorFibreInverse` are mutually inverse, so the comparison
map of Stacks 05VP is bijective in its fibre-level form.

## Main results

* `AlgebraicGeometry.Space.chartStalkTensorFibre_leftInverse` and
  `AlgebraicGeometry.Space.chartStalkTensorFibre_rightInverse`: the two composites are the
  identity.
* `AlgebraicGeometry.Space.bijective_chartStalkTensorFibreComparison`: hence the fibre-level
  comparison map is bijective.
* `AlgebraicGeometry.Space.affineSectionDesc_chartOpen`: on a Zariski open contained in `W`
  whose étale chart is affine, the extended germ map of
  `AlgebraicGeometry.Space.affineSectionDesc` is the germ map of that open.
* `AlgebraicGeometry.Space.chartStalkTensorFibreComparison_affineSectionDesc`: the comparison map
  carries the extended germ map of an affine neighbourhood back to the germ map of that
  neighbourhood.

## Implementation notes

Both composites reduce to germs.  For `inverse ∘ comparison` the generators are the pure
tensors, and `AlgebraicGeometry.Space.chartZariskiSectionGerm_jointly_surjective_affine` writes
the right factor as a germ over an affine Zariski open *contained in* `W`, which is what makes
`AlgebraicGeometry.Space.affineSectionDesc_chartOpen` available; for
`comparison ∘ inverse` the generators are the germs themselves
(`Stacks.moduleStalkLargeGerm_jointly_surjective`).

That the inverse is linear and not merely additive
(`AlgebraicGeometry.Space.chartStalkTensorFibreInverse_smul`) is needed to pull the scalar out
of a pure tensor, and it comes from `Stacks.moduleStalkLargeDescOfCompatibleFamily_smul` with
`θ := RingHom.id`: the fibre map `GrothendieckTopology.Point.toPresheafFiber` at a
neighbourhood *is* `AlgebraicGeometry.Space.pointRingGerm` by definition, so the semilinearity
of the family is literally that lemma's hypothesis and no bridging lemma is required.

`AlgebraicGeometry.Space.affineSectionDesc_chartOpen` and
`AlgebraicGeometry.Space.chartStalkTensorFibreComparison_affineSectionDesc` are both proved by
uniqueness of the descent (`AlgebraicGeometry.Space.baseChangeDesc_unique`) rather than by
induction, each against a pair of semilinear maps named separately
(`AlgebraicGeometry.Space.pointModuleGermSemilinear`,
`AlgebraicGeometry.Space.comparisonAffineSectionDesc`).

## References

* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The family of germ maps is semilinear along `AlgebraicGeometry.Space.pointRingGerm`. -/
theorem inverseFamily_smul {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (U : SmallEtale B S hS X) (y : (etaleSitePoint B S hS X x hX).fiber.obj U)
    (a : chartRing B S hS X hX U) (s : F.val.obj (op U)) :
    inverseFamily B S hS hX V F W hw hW U y (a • s) =
      pointRingGerm B S hS hX ⟨U, y.1, y.2⟩ a •
        inverseFamily B S hS hX V F W hw hW U y s := by
  refine Eq.trans (congrArg (affineSectionDesc B S hS hX V F W hw hW
      (affineOverChart B S hS hX V W hw ⟨U, y.1, y.2⟩)
      (affineOverNbhd_isAffine B S hS hX V W hw ⟨U, y.1, y.2⟩))
    (F.val.map_smul (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).hom.op a s)) ?_
  refine Eq.trans ((affineSectionDesc B S hS hX V F W hw hW
      (affineOverChart B S hS hX V W hw ⟨U, y.1, y.2⟩)
      (affineOverNbhd_isAffine B S hS hX V W hw ⟨U, y.1, y.2⟩)).map_smulₛₗ
    (chartRestrict (hF := hX) (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).hom a)
    (F.val.map (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).hom.op s)) ?_
  exact congrArg (fun c => c • inverseFamily B S hS hX V F W hw hW U y s)
    (pointRingGerm_map B S hS hX (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩) a)

/-- The inverse is linear over the fibre of the structure sheaf, not merely additive. -/
theorem chartStalkTensorFibreInverse_smul {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (r : ↥(etalePointFiber B S hS hX x))
    (z : ↥(geometricModuleStalkLarge B S hS hX x F)) :
    chartStalkTensorFibreInverse B S hS hX V F W hw hW (r • z) =
      r • chartStalkTensorFibreInverse B S hS hX V F W hw hW z :=
  Stacks.moduleStalkLargeDescOfCompatibleFamily_smul (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
    (inverseFamily B S hS hX V F W hw hW) (inverseFamily_w B S hS hX V F W hw hW)
    (RingHom.id ↥(etalePointFiber B S hS hX x))
    (fun U y a s => inverseFamily_smul B S hS hX V F W hw hW U y a s) r z

/-- Every element of the Zariski stalk is the germ of a section over an affine Zariski open of
the chart contained in a given open and containing the point. -/
theorem chartZariskiSectionGerm_jointly_surjective_affine {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (z : ↥(chartZariskiModuleStalkLarge B S hS hX V F)) :
    ∃ (W' : (etaleChartScheme B S hS V.chart).Opens) (_hle : W' ≤ W)
      (hw' : chartPoint B S hS X V ∈ W')
      (_ : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W')))
      (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W'))),
      chartZariskiSectionGermLarge B S hS hX V F W' hw' s = z := by
  obtain ⟨W₁, hw₁, s₁, rfl⟩ := chartZariskiSectionGerm_jointly_surjective B S hS hX V F z
  obtain ⟨W', hW'aff, hw', hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show chartPoint B S hS X V ∈ W ⊓ W₁ from ⟨hw, hw₁⟩)
  refine ⟨W', le_trans hsub inf_le_left, hw', hW'aff,
    F.val.map ((chartOpens B S hS V.chart).map
      (homOfLE (le_trans hsub inf_le_right))).op s₁, ?_⟩
  exact chartZariskiSectionGerm_map B S hS hX V F W₁ W'
    (homOfLE (le_trans hsub inf_le_right)) hw' hw₁ s₁

/-- An inclusion of Zariski opens of the chart, both containing the point, as a morphism of the
small étale neighbourhoods they define. -/
noncomputable abbrev chartOpenInclusion {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (W' : (etaleChartScheme B S hS V.chart).Opens)
    (hle : W' ≤ W) (hw' : chartPoint B S hS X V ∈ W') :
    chartOpenNeighborhood B S hS V W' hw' ⟶ chartOpenNeighborhood B S hS V W hw :=
  chartOpenNeighborhoodMap B S hS V (homOfLE hle) hw' hw

/-- The extended germ map of a Zariski open contained in `W` and the germ map of that open
agree on sections restricted from `W`. -/
theorem affineSectionDesc_chartOpen_aux {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (W' : (etaleChartScheme B S hS V.chart).Opens) (hle : W' ≤ W)
    (hw' : chartPoint B S hS X V ∈ W')
    (hW' : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W')))
    (t : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    affineSectionDesc B S hS hX V F W hw hW
          (chartOpenInclusion B S hS V W hw W' hle hw') hW'
        (F.val.map (chartOpenInclusion B S hS V W hw W' hle hw').hom.op t) =
      chartAffineTensorGerm B S hS hX V F W' hw'
        (F.val.map (chartOpenInclusion B S hS V W hw W' hle hw').hom.op t) := by
  refine Eq.trans (affineSectionDesc_restrict B S hS hX V F W hw hW
    (chartOpenInclusion B S hS V W hw W' hle hw') hW' t) ?_
  exact (congrArg (fun w : ↥(chartZariskiModuleStalkLarge B S hS hX V F) =>
      (1 : ↥(etalePointFiber B S hS hX x)) ⊗ₜ[↥(chartZariskiFiber B S hS V),
        chartZariskiFiberToEtaleFiber B S hS hX V] w)
    (chartZariskiSectionGerm_map B S hS hX V F W W' (homOfLE hle) hw' hw t)).symm

/-- Two semilinear maps out of the sections over an affine refinement of an affine open `W` of
the chart agree if they agree on the restrictions of sections over `W`. -/
private theorem semilinear_ext_of_chartOpenRestrict {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {M : SmallEtaleNeighborhood x} (φ : M ⟶ chartOpenNeighborhood B S hS V W hw)
    (hM : IsAffine (chartScheme M.chart)) {E P : Type u} [CommRing E] [AddCommGroup P]
    [Module E P] (l : chartRing B S hS X hX M.chart →+* E)
    (h₁ h₂ : F.val.obj (op M.chart) →ₛₗ[l] P)
    (he : ∀ t : F.val.obj (op ((chartOpens B S hS V.chart).obj W)),
      h₁ (chartOpenRestrictLinear B S hS hX V F W hw φ t) =
        h₂ (chartOpenRestrictLinear B S hS hX V F W hw φ t)) :
    h₁ = h₂ := by
  let : Algebra (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (chartRing B S hS X hX M.chart) := chartOpenAlgebra B S hS hX V W hw φ
  let : Module (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (F.val.obj (op M.chart)) := chartOpenSectionsModule B S hS hX V F W hw φ
  let : IsScalarTower (chartRing B S hS X hX ((chartOpens B S hS V.chart).obj W))
      (chartRing B S hS X hX M.chart) (F.val.obj (op M.chart)) :=
    chartSections_isScalarTower F φ.hom
  exact baseChangeDesc_unique (chartOpenRestrictLinear B S hS hX V F W hw φ)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F inferInstance
      ((chartOpens B S hS V.chart).obj W) M.chart hW hM φ.hom) l h₁ h₂ he

/-- **The extension agrees with the germ map of a smaller open.**  On a Zariski open contained
in `W` whose étale chart is affine, the extended germ map of
`AlgebraicGeometry.Space.affineSectionDesc` is the germ map of that open. -/
theorem affineSectionDesc_chartOpen {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (W' : (etaleChartScheme B S hS V.chart).Opens) (hle : W' ≤ W)
    (hw' : chartPoint B S hS X V ∈ W')
    (hW' : IsAffine (chartScheme (chartOpenNeighborhood B S hS V W' hw').chart))
    (s : F.val.obj (op (chartOpenNeighborhood B S hS V W' hw').chart)) :
    affineSectionDesc B S hS hX V F W hw hW
        (chartOpenInclusion B S hS V W hw W' hle hw') hW' s =
      chartAffineTensorGerm B S hS hX V F W' hw' s := by
  exact DFunLike.congr_fun (semilinear_ext_of_chartOpenRestrict B S hS hX V F W hw hW
    (chartOpenInclusion B S hS V W hw W' hle hw') hW'
    (pointRingGerm B S hS hX (chartOpenNeighborhood B S hS V W' hw'))
    (affineSectionDesc B S hS hX V F W hw hW
      (chartOpenInclusion B S hS V W hw W' hle hw') hW')
    (chartAffineTensorGerm B S hS hX V F W' hw')
    (affineSectionDesc_chartOpen_aux B S hS hX V F W hw hW W' hle hw' hW')) s

/-- The inverse sends the germ of a section over an affine Zariski open contained in `W` back
to the base change of its Zariski germ. -/
theorem chartStalkTensorFibreInverse_chartAffineGerm {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (W' : (etaleChartScheme B S hS V.chart).Opens) (hle : W' ≤ W)
    (hw' : chartPoint B S hS X V ∈ W')
    (hW' : IsAffine (chartScheme (chartOpenNeighborhood B S hS V W' hw').chart))
    (s : F.val.obj (op (chartOpenNeighborhood B S hS V W' hw').chart)) :
    chartStalkTensorFibreInverse B S hS hX V F W hw hW
        (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
          (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
          ((chartOpens B S hS V.chart).obj W')
          ⟨(chartOpenNeighborhood B S hS V W' hw').point,
            (chartOpenNeighborhood B S hS V W' hw').point_comp⟩ s) =
      chartAffineTensorGerm B S hS hX V F W' hw' s := by
  refine Eq.trans (chartStalkTensorFibreInverse_germ B S hS hX V F W hw hW
    ((chartOpens B S hS V.chart).obj W')
    ⟨(chartOpenNeighborhood B S hS V W' hw').point,
      (chartOpenNeighborhood B S hS V W' hw').point_comp⟩ s) ?_
  refine Eq.trans (affineSectionDesc_eq_of_over B S hS hX V F W hw hW
    (affineOverChart B S hS hX V W hw (chartOpenNeighborhood B S hS V W' hw'))
    (affineOverNbhd_isAffine B S hS hX V W hw (chartOpenNeighborhood B S hS V W' hw'))
    (affineOverHom B S hS hX V W hw (chartOpenNeighborhood B S hS V W' hw'))
    (chartOpenInclusion B S hS V W hw W' hle hw') hW' (𝟙 _) s) ?_
  refine Eq.trans (congrArg (affineSectionDesc B S hS hX V F W hw hW
      (chartOpenInclusion B S hS V W hw W' hle hw') hW')
    (ConcreteCategory.congr_hom (F.val.presheaf.map_id
      (op (chartOpenNeighborhood B S hS V W' hw').chart)) s)) ?_
  exact affineSectionDesc_chartOpen B S hS hX V F W hw hW W' hle hw' hW' s

/-- **The inverse is a left inverse of the fibre-level comparison map.** -/
theorem chartStalkTensorFibre_leftInverse {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (z : ↥(chartZariskiFibreTensor B S hS hX V F)) :
    chartStalkTensorFibreInverse B S hS hX V F W hw hW
        (chartStalkTensorFibreComparison B S hS hX V F z) = z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    exact Eq.trans (congrArg (chartStalkTensorFibreInverse B S hS hX V F W hw hW)
        (map_zero (chartStalkTensorFibreComparison B S hS hX V F).hom))
      (map_zero (chartStalkTensorFibreInverse B S hS hX V F W hw hW))
  | add y y' hy hy' =>
    refine Eq.trans (congrArg (chartStalkTensorFibreInverse B S hS hX V F W hw hW)
      (map_add (chartStalkTensorFibreComparison B S hS hX V F).hom y y')) ?_
    refine Eq.trans (map_add (chartStalkTensorFibreInverse B S hS hX V F W hw hW)
      (chartStalkTensorFibreComparison B S hS hX V F y)
      (chartStalkTensorFibreComparison B S hS hX V F y')) ?_
    refine Eq.trans (congrArg (· + chartStalkTensorFibreInverse B S hS hX V F W hw hW
      (chartStalkTensorFibreComparison B S hS hX V F y')) hy) ?_
    exact congrArg (y + ·) hy'
  | tmul a y =>
    obtain ⟨W', hle, hw', hW'aff, s, rfl⟩ :=
      chartZariskiSectionGerm_jointly_surjective_affine B S hS hX V F W hw y
    have ha : ((a ⊗ₜ[↥(chartZariskiFiber B S hS V),
          chartZariskiFiberToEtaleFiber B S hS hX V]
        chartZariskiSectionGermLarge B S hS hX V F W' hw' s) :
          ↥(chartZariskiFibreTensor B S hS hX V F)) =
        (@id ↥(etalePointFiber B S hS hX x) a) •
          chartAffineTensorGerm B S hS hX V F W' hw' s :=
      (Eq.trans (ModuleCat.ExtendScalars.smul_tmul
          (chartZariskiFiberToEtaleFiber B S hS hX V)
          (@id ↥(etalePointFiber B S hS hX x) a) 1
          (chartZariskiSectionGermLarge B S hS hX V F W' hw' s))
        (congrArg (fun c : ↥(etalePointFiber B S hS hX x) =>
            (c ⊗ₜ[↥(chartZariskiFiber B S hS V),
              chartZariskiFiberToEtaleFiber B S hS hX V]
            chartZariskiSectionGermLarge B S hS hX V F W' hw' s :
              ↥(chartZariskiFibreTensor B S hS hX V F)))
          (mul_one (@id ↥(etalePointFiber B S hS hX x) a)))).symm
    refine Eq.trans (congrArg (fun w => chartStalkTensorFibreInverse B S hS hX V F W hw hW
      (chartStalkTensorFibreComparison B S hS hX V F w)) ha) (Eq.trans ?_ ha.symm)
    refine Eq.trans (congrArg (chartStalkTensorFibreInverse B S hS hX V F W hw hW)
      ((chartStalkTensorFibreComparison B S hS hX V F).hom.map_smul
        (@id ↥(etalePointFiber B S hS hX x) a)
        (chartAffineTensorGerm B S hS hX V F W' hw' s))) ?_
    refine Eq.trans (chartStalkTensorFibreInverse_smul B S hS hX V F W hw hW
      (@id ↥(etalePointFiber B S hS hX x) a)
      (chartStalkTensorFibreComparison B S hS hX V F
        (chartAffineTensorGerm B S hS hX V F W' hw' s))) ?_
    exact congrArg (fun w => (@id ↥(etalePointFiber B S hS hX x) a) • w)
      (Eq.trans (congrArg (chartStalkTensorFibreInverse B S hS hX V F W hw hW)
        (chartStalkTensorFibreComparison_germ B S hS hX V F W' hw' s))
        (chartStalkTensorFibreInverse_chartAffineGerm B S hS hX V F W hw hW
          W' hle hw' hW'aff s))

/-- The germ map of module sections at a small étale neighbourhood, as a semilinear map along
the germ map of regular functions. -/
noncomputable def pointModuleGermSemilinear {x : GeometricPoint B S hS X}
    (F : Modules.{u, u} B S hS X hX) (M : SmallEtaleNeighborhood x) :
    F.val.obj (op M.chart) →ₛₗ[pointRingGerm B S hS hX M]
      ↥(geometricModuleStalkLarge B S hS hX x F) where
  toFun := Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F M.chart ⟨M.point, M.point_comp⟩
  map_add' := map_add _
  map_smul' := Stacks.moduleStalkLargeGerm_smul (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F M.chart ⟨M.point, M.point_comp⟩

/-- The fibre-level comparison map composed with the extended germ map of an affine
neighbourhood, as a semilinear map. -/
noncomputable def comparisonAffineSectionDesc {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {M : SmallEtaleNeighborhood x} (φ : M ⟶ chartOpenNeighborhood B S hS V W hw)
    (hM : IsAffine (chartScheme M.chart)) :
    F.val.obj (op M.chart) →ₛₗ[pointRingGerm B S hS hX M]
      ↥(geometricModuleStalkLarge B S hS hX x F) where
  toFun z := chartStalkTensorFibreComparison B S hS hX V F
    (affineSectionDesc B S hS hX V F W hw hW φ hM z)
  map_add' z z' := by
    refine Eq.trans (congrArg (chartStalkTensorFibreComparison B S hS hX V F)
      (map_add (affineSectionDesc B S hS hX V F W hw hW φ hM) z z')) ?_
    exact map_add (chartStalkTensorFibreComparison B S hS hX V F).hom _ _
  map_smul' a z := by
    refine Eq.trans (congrArg (chartStalkTensorFibreComparison B S hS hX V F)
      ((affineSectionDesc B S hS hX V F W hw hW φ hM).map_smulₛₗ a z)) ?_
    exact (chartStalkTensorFibreComparison B S hS hX V F).hom.map_smul _ _

/-- The comparison map carries the extended germ map of an affine neighbourhood over `W` back
to the germ map of that neighbourhood. -/
theorem chartStalkTensorFibreComparison_affineSectionDesc {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {M : SmallEtaleNeighborhood x} (φ : M ⟶ chartOpenNeighborhood B S hS V W hw)
    (hM : IsAffine (chartScheme M.chart)) (z : F.val.obj (op M.chart)) :
    chartStalkTensorFibreComparison B S hS hX V F
        (affineSectionDesc B S hS hX V F W hw hW φ hM z) =
      Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F M.chart ⟨M.point, M.point_comp⟩ z := by
  have he : ∀ t : F.val.obj (op ((chartOpens B S hS V.chart).obj W)),
      comparisonAffineSectionDesc B S hS hX V F W hw hW φ hM
          (chartOpenRestrictLinear B S hS hX V F W hw φ t) =
        pointModuleGermSemilinear B S hS hX F M
          (chartOpenRestrictLinear B S hS hX V F W hw φ t) := by
    intro t
    refine Eq.trans (congrArg (chartStalkTensorFibreComparison B S hS hX V F)
      (affineSectionDesc_restrict B S hS hX V F W hw hW φ hM t)) ?_
    refine Eq.trans (chartStalkTensorFibreComparison_germ B S hS hX V F W hw t) ?_
    refine Eq.trans ?_ (Stacks.moduleStalkLargeGerm_w (etaleSitePoint B S hS X x hX)
      (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F φ.hom ⟨M.point, M.point_comp⟩ t).symm
    exact congrArg (fun c => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
        ((chartOpens B S hS V.chart).obj W) c t)
      (show (⟨(chartOpenNeighborhood B S hS V W hw).point,
          (chartOpenNeighborhood B S hS V W hw).point_comp⟩ :
            (etaleSitePoint B S hS X x hX).fiber.obj ((chartOpens B S hS V.chart).obj W)) =
        (etaleSitePoint B S hS X x hX).fiber.map φ.hom ⟨M.point, M.point_comp⟩ from
        (Subtype.ext φ.point_comp).symm)
  exact DFunLike.congr_fun (semilinear_ext_of_chartOpenRestrict B S hS hX V F W hw hW φ hM
    (pointRingGerm B S hS hX M) (comparisonAffineSectionDesc B S hS hX V F W hw hW φ hM)
    (pointModuleGermSemilinear B S hS hX F M) he) z

/-- **The inverse is a right inverse of the fibre-level comparison map.** -/
theorem chartStalkTensorFibre_rightInverse {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (z : ↥(geometricModuleStalkLarge B S hS hX x F)) :
    chartStalkTensorFibreComparison B S hS hX V F
        (chartStalkTensorFibreInverse B S hS hX V F W hw hW z) = z := by
  obtain ⟨U, y, t, rfl⟩ := Stacks.moduleStalkLargeGerm_jointly_surjective
    (etaleSitePoint B S hS X x hX) (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F z
  refine Eq.trans (congrArg (chartStalkTensorFibreComparison B S hS hX V F)
    (chartStalkTensorFibreInverse_germ B S hS hX V F W hw hW U y t)) ?_
  refine Eq.trans (chartStalkTensorFibreComparison_affineSectionDesc B S hS hX V F W hw hW
    (affineOverChart B S hS hX V W hw ⟨U, y.1, y.2⟩)
    (affineOverNbhd_isAffine B S hS hX V W hw ⟨U, y.1, y.2⟩)
    (F.val.map (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).hom.op t)) ?_
  refine Eq.trans (Stacks.moduleStalkLargeGerm_w (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
    (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).hom
    ⟨(affineOverNbhd B S hS hX V W hw ⟨U, y.1, y.2⟩).point,
      (affineOverNbhd B S hS hX V W hw ⟨U, y.1, y.2⟩).point_comp⟩ t) ?_
  exact congrArg (fun c => Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
      (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F U c t)
    (Subtype.ext (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).point_comp)

/-- **The comparison map of Stacks 05VP is bijective in its fibre-level form.** -/
theorem bijective_chartStalkTensorFibreComparison {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W))) :
    Function.Bijective (chartStalkTensorFibreComparison B S hS hX V F) :=
  ⟨Function.LeftInverse.injective (chartStalkTensorFibre_leftInverse B S hS hX V F W hw hW),
    Function.RightInverse.surjective (chartStalkTensorFibre_rightInverse B S hS hX V F W hw hW)⟩


end AlgebraicGeometry.Space

end
