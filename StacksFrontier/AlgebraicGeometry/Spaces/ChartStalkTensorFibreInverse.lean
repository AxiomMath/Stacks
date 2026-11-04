module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSectionDescent

/-!
# The inverse of the comparison map of Stacks 05VP, over the fibre at the point

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module and
let `x̄` be a geometric point with small étale neighbourhood `V`. Fix a Zariski open `W` of the
chart of `V` whose étale chart is affine and which contains the point under the chosen lift.
`AlgebraicGeometry.Space.affineSectionDesc` attaches a germ into the base-changed Zariski stalk
to every section over an affine neighbourhood lying over the one `W` defines. This file extends
that to *every* small étale neighbourhood by choosing an affine refinement which lies over it,
shows the choice does not matter, and descends the resulting family to the stalk.

It also defines the comparison map of Stacks 05VP over the fibre
`AlgebraicGeometry.Space.etalePointFiber` rather than over the étale local ring.

## Main definitions

* `AlgebraicGeometry.Space.affineOverNbhd`, with
  `AlgebraicGeometry.Space.affineOverHom` and `AlgebraicGeometry.Space.affineOverChart`, is a
  chosen affine refinement of a small étale neighbourhood lying over the fixed one.
* `AlgebraicGeometry.Space.inverseFamily` is the resulting family of germ maps, one for each
  neighbourhood, and `AlgebraicGeometry.Space.chartStalkTensorFibreInverse` its descent to the
  stalk.
* `AlgebraicGeometry.Space.chartStalkTensorFibreComparison` is the comparison map of Stacks 05VP
  formed over the fibre.

## Main results

* `AlgebraicGeometry.Space.affineSectionDesc_eq_of_over`: the germ attached to a section over a
  neighbourhood does not depend on which affine refinement over the fixed neighbourhood is used.
* `AlgebraicGeometry.Space.inverseFamily_w` and
  `AlgebraicGeometry.Space.chartStalkTensorFibreInverse_germ`: the family is compatible with
  restriction, and its descent sends a germ to the family's value.
* `AlgebraicGeometry.Space.chartStalkTensorFibreComparison_germ`: the fibre-level comparison map
  sends `1 ⊗ (germ of s)` to the germ of `s` at the geometric point.

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

/-- Restriction of sections along two successive morphisms of small étale neighbourhoods is
restriction along their composite. -/
theorem map_comp_apply_neighborhood {x : GeometricPoint B S hS X}
    (F : Modules.{u, u} B S hS X hX) {N M P : SmallEtaleNeighborhood x}
    (f : N ⟶ M) (g : M ⟶ P) (s : F.val.obj (op P.chart)) :
    F.val.map f.hom.op (F.val.map g.hom.op s) = F.val.map (f ≫ g).hom.op s := by
  refine Eq.trans (ConcreteCategory.comp_apply (F.val.presheaf.map g.hom.op)
    (F.val.presheaf.map f.hom.op) s).symm ?_
  exact ConcreteCategory.congr_hom (F.val.presheaf.map_comp g.hom.op f.hom.op).symm s

include hX in
/-- Every small étale neighbourhood of a geometric point is refined by one with affine chart
which also lies over a fixed neighbourhood. -/
theorem exists_affineNeighborhoodOver {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (N : SmallEtaleNeighborhood x) :
    ∃ (M : SmallEtaleNeighborhood x) (_ : M ⟶ N)
      (_ : M ⟶ chartOpenNeighborhood B S hS V W hw), IsAffine (chartScheme M.chart) := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X hX x
  obtain ⟨M₀, a, b, -⟩ :=
    IsCofilteredOrEmpty.cone_objs N (chartOpenNeighborhood B S hS V W hw)
  obtain ⟨M, g, hMaff⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS ⟨X, hX⟩ x M₀
  exact ⟨M, g ≫ a, g ≫ b, hMaff⟩

include hX in
/-- A chosen affine refinement of a small étale neighbourhood lying over the neighbourhood
defined by a Zariski open of the chart. -/
noncomputable def affineOverNbhd {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (N : SmallEtaleNeighborhood x) :
    SmallEtaleNeighborhood x :=
  (exists_affineNeighborhoodOver B S hS hX V W hw N).choose

/-- The chosen refinement maps to the neighbourhood it refines. -/
noncomputable def affineOverHom {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (N : SmallEtaleNeighborhood x) :
    affineOverNbhd B S hS hX V W hw N ⟶ N :=
  (exists_affineNeighborhoodOver B S hS hX V W hw N).choose_spec.choose

/-- The chosen refinement lies over the neighbourhood defined by the Zariski open. -/
noncomputable def affineOverChart {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (N : SmallEtaleNeighborhood x) :
    affineOverNbhd B S hS hX V W hw N ⟶ chartOpenNeighborhood B S hS V W hw :=
  (exists_affineNeighborhoodOver B S hS hX V W hw N).choose_spec.choose_spec.choose

/-- The chart of the chosen refinement is affine. -/
theorem affineOverNbhd_isAffine {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (W : (etaleChartScheme B S hS V.chart).Opens)
    (hw : chartPoint B S hS X V ∈ W) (N : SmallEtaleNeighborhood x) :
    IsAffine (chartScheme (affineOverNbhd B S hS hX V W hw N).chart) :=
  (exists_affineNeighborhoodOver B S hS hX V W hw N).choose_spec.choose_spec.choose_spec

/-- **The germ of a section does not depend on the affine refinement used to compute it.** Two
affine neighbourhoods over the fixed one, each mapping to a neighbourhood `N`, give the same
germ for a section over `N`. -/
theorem affineSectionDesc_eq_of_over {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    {N M M' : SmallEtaleNeighborhood x}
    (φ : M ⟶ chartOpenNeighborhood B S hS V W hw) (hM : IsAffine (chartScheme M.chart))
    (k : M ⟶ N)
    (φ' : M' ⟶ chartOpenNeighborhood B S hS V W hw) (hM' : IsAffine (chartScheme M'.chart))
    (k' : M' ⟶ N) (s : F.val.obj (op N.chart)) :
    affineSectionDesc B S hS hX V F W hw hW φ hM (F.val.map k.hom.op s) =
      affineSectionDesc B S hS hX V F W hw hW φ' hM' (F.val.map k'.hom.op s) := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X hX x
  obtain ⟨P, p, p', -⟩ := IsCofilteredOrEmpty.cone_objs M M'
  obtain ⟨Q, q, hq⟩ := IsCofilteredOrEmpty.cone_maps (p ≫ φ) (p' ≫ φ')
  obtain ⟨R, r, hr⟩ := IsCofilteredOrEmpty.cone_maps (q ≫ p ≫ k) (q ≫ p' ≫ k')
  obtain ⟨T, g, hTaff⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS ⟨X, hX⟩ x R
  have h1 : (g ≫ r ≫ q ≫ p) ≫ φ = (g ≫ r ≫ q ≫ p') ≫ φ' := by
    simp only [Category.assoc, hq]
  have h2 : (g ≫ r ≫ q ≫ p) ≫ k = (g ≫ r ≫ q ≫ p') ≫ k' := by
    simp only [Category.assoc]
    simpa only [Category.assoc] using congrArg (fun m => g ≫ m) hr
  have e1 := affineSectionDesc_map B S hS hX V F W hw hW
    ((g ≫ r ≫ q ≫ p) ≫ φ) hTaff φ hM (g ≫ r ≫ q ≫ p) rfl (F.val.map k.hom.op s)
  have e2 := affineSectionDesc_map B S hS hX V F W hw hW
    ((g ≫ r ≫ q ≫ p') ≫ φ') hTaff φ' hM' (g ≫ r ≫ q ≫ p') rfl (F.val.map k'.hom.op s)
  refine Eq.trans e1.symm (Eq.trans ?_ e2)
  rw [map_comp_apply_neighborhood, map_comp_apply_neighborhood, h1, h2]

/-- The germ into the base-changed Zariski stalk of a section over an arbitrary small étale
neighbourhood, computed on the chosen affine refinement. -/
noncomputable def inverseFamily {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (U : SmallEtale B S hS X) (y : (etaleSitePoint B S hS X x hX).fiber.obj U) :
    F.val.obj (op U) →+ ↥(chartZariskiFibreTensor B S hS hX V F) :=
  (affineSectionDesc B S hS hX V F W hw hW
        (affineOverChart B S hS hX V W hw ⟨U, y.1, y.2⟩)
        (affineOverNbhd_isAffine B S hS hX V W hw ⟨U, y.1, y.2⟩)).toAddMonoidHom.comp
    (F.val.map (affineOverHom B S hS hX V W hw ⟨U, y.1, y.2⟩).hom.op).hom.toAddMonoidHom

/-- The family of germ maps is compatible with restriction to a smaller neighbourhood. -/
theorem inverseFamily_w {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    ⦃U U' : SmallEtale B S hS X⦄ (f : U ⟶ U')
    (y : (etaleSitePoint B S hS X x hX).fiber.obj U) (s : F.val.obj (op U')) :
    inverseFamily B S hS hX V F W hw hW U y (F.val.map f.op s) =
      inverseFamily B S hS hX V F W hw hW U'
        ((etaleSitePoint B S hS X x hX).fiber.map f y) s := by
  let N : SmallEtaleNeighborhood x := ⟨U, y.1, y.2⟩
  let N' : SmallEtaleNeighborhood x :=
    ⟨U', ((etaleSitePoint B S hS X x hX).fiber.map f y).1,
      ((etaleSitePoint B S hS X x hX).fiber.map f y).2⟩
  let fN : N ⟶ N' := ⟨f, rfl⟩
  refine Eq.trans (congrArg (affineSectionDesc B S hS hX V F W hw hW
    (affineOverChart B S hS hX V W hw N) (affineOverNbhd_isAffine B S hS hX V W hw N))
    (map_comp_apply_neighborhood B S hS hX F (affineOverHom B S hS hX V W hw N) fN s)) ?_
  exact affineSectionDesc_eq_of_over B S hS hX V F W hw hW
    (affineOverChart B S hS hX V W hw N) (affineOverNbhd_isAffine B S hS hX V W hw N)
    (affineOverHom B S hS hX V W hw N ≫ fN)
    (affineOverChart B S hS hX V W hw N') (affineOverNbhd_isAffine B S hS hX V W hw N')
    (affineOverHom B S hS hX V W hw N') s

/-- **The inverse of the comparison map of Stacks 05VP, over the fibre at the point.** The
descent of `AlgebraicGeometry.Space.inverseFamily` to the stalk of `F` at the geometric
point. -/
noncomputable def chartStalkTensorFibreInverse {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W))) :
    ↥(geometricModuleStalkLarge B S hS hX x F) →+
      ↥(chartZariskiFibreTensor B S hS hX V F) :=
  Stacks.moduleStalkLargeDescOfCompatibleFamily (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
    (inverseFamily B S hS hX V F W hw hW) (inverseFamily_w B S hS hX V F W hw hW)

/-- The descent sends the germ of a section to the value of the family on that section. -/
theorem chartStalkTensorFibreInverse_germ {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    [F.IsQuasicoherentOnSite]
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hW : IsAffine (chartScheme ((chartOpens B S hS V.chart).obj W)))
    (U : SmallEtale B S hS X) (y : (etaleSitePoint B S hS X x hX).fiber.obj U)
    (t : F.val.obj (op U)) :
    chartStalkTensorFibreInverse B S hS hX V F W hw hW
        (Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
          (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F U y t) =
      inverseFamily B S hS hX V F W hw hW U y t :=
  Stacks.moduleStalkLargeDescOfCompatibleFamily_germ (etaleSitePoint B S hS X x hX)
    (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
    (inverseFamily B S hS hX V F W hw hW) (inverseFamily_w B S hS hX V F W hw hW) U y t

/-- The semilinear map from the Zariski stalk to the stalk at the geometric point, over the
fibre of the structure sheaf rather than over the étale local ring, together with its value on
germs. -/
noncomputable def chartZariskiToGeometricFibreData {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX) :
    { Ψ : ↥(chartZariskiModuleStalkLarge B S hS hX V F) →ₛₗ[
          chartZariskiFiberToEtaleFiber B S hS hX V]
        ↥(geometricModuleStalkLarge B S hS hX x F) //
      ∀ (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
        (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))),
        Ψ (chartZariskiSectionGermLarge B S hS hX V F W hw s) =
          Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
            (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F
            ((chartOpens B S hS V.chart).obj W)
            ⟨(chartOpenNeighborhood B S hS V W hw).point,
              (chartOpenNeighborhood B S hS V W hw).point_comp⟩ s } := by
  let Y := etaleChartScheme B S hS V.chart
  let J := Opens.grothendieckTopology Y
  let M₀ := chartRestrictionPresheaf B S hS hX F V.chart
  let MU := restrictToChart B S hS hX F V.chart
  let OU : Sheaf J CommRingCat.{u} := Y.sheaf
  let pZ : J.Point.{u} := chartZariskiPoint B S hS X V
  letI : HasSheafify J AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  let unit : M₀.presheaf ⟶ MU.val.presheaf := CategoryTheory.toSheafify J M₀.presheaf
  haveI : Presheaf.IsLocallySurjective J unit :=
    (inferInstance : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J M₀.presheaf))
  haveI : Presheaf.IsLocallyInjective J unit :=
    (inferInstance : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M₀.presheaf))
  let unitMod : M₀ ⟶ (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj MU.val :=
    PresheafOfModules.toSheafify _ unit
  have hψ : ∀ (Z : (Opens Y)ᵒᵖ) (a : Y.ringCatSheaf.obj.obj Z) (t : M₀.obj Z),
      unit.app Z (a • t) = a • unit.app Z t :=
    fun Z a t => (unitMod.app Z).hom.map_smul a t
  let Ψ₀ := Stacks.moduleStalkLargeDescOfLocallyBijective pZ OU MU unit
    (chartOpenGeometricGerm B S hS hX V F) (chartOpenGeometricGerm_w B S hS hX V F)
  have hΨ₀ := Stacks.moduleStalkLargeDescOfLocallyBijective_smul pZ OU MU unit
    (chartOpenGeometricGerm B S hS hX V F) (chartOpenGeometricGerm_w B S hS hX V F)
    (chartZariskiFiberToEtaleFiber B S hS hX V) hψ
    (chartOpenGeometricGerm_smul B S hS hX V F)
  have hgerm := Stacks.moduleStalkLargeDescOfLocallyBijective_germ pZ OU MU unit
    (chartOpenGeometricGerm B S hS hX V F) (chartOpenGeometricGerm_w B S hS hX V F)
  exact ⟨{ toFun := Ψ₀, map_add' := map_add Ψ₀, map_smul' := hΨ₀ },
    fun W hw s => hgerm W ⟨⟨hw⟩⟩ (ULift.up s)⟩

/-- The comparison map of Stacks 05VP formed over the fibre of the structure sheaf at the point
of the small étale site. -/
noncomputable def chartStalkTensorFibreComparison {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX) :
    chartZariskiFibreTensor B S hS hX V F ⟶ geometricModuleStalkLarge B S hS hX x F :=
  baseChangeLiftHom (chartZariskiFiberToEtaleFiber B S hS hX V)
    (chartZariskiModuleStalkLarge B S hS hX V F)
    (geometricModuleStalkLarge B S hS hX x F)
    (chartZariskiToGeometricFibreData B S hS hX V F).1

/-- The fibre-level comparison map sends the base change of the Zariski germ of a section to
the germ of the same section at the geometric point. -/
theorem chartStalkTensorFibreComparison_germ {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (F : Modules.{u, u} B S hS X hX)
    (W : (etaleChartScheme B S hS V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (s : F.val.obj (op ((chartOpens B S hS V.chart).obj W))) :
    chartStalkTensorFibreComparison B S hS hX V F
        (chartAffineTensorGerm B S hS hX V F W hw s) =
      Stacks.moduleStalkLargeGerm (etaleSitePoint B S hS X x hX)
        (smallEtaleRingedTopos B S hS ⟨X, hX⟩).O F ((chartOpens B S hS V.chart).obj W)
        ⟨(chartOpenNeighborhood B S hS V W hw).point,
          (chartOpenNeighborhood B S hS V W hw).point_comp⟩ s := by
  refine Eq.trans (baseChangeLift_tmul (chartZariskiFiberToEtaleFiber B S hS hX V)
    (chartZariskiModuleStalkLarge B S hS hX V F)
    (chartZariskiToGeometricFibreData B S hS hX V F).1 1
    (chartZariskiSectionGermLarge B S hS hX V F W hw s)) ?_
  refine Eq.trans (one_smul _ _) ?_
  exact (chartZariskiToGeometricFibreData B S hS hX V F).2 W hw s

end AlgebraicGeometry.Space

end
