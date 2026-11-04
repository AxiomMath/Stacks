module

public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.GlueAlgebra
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjChartBridge
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwistArith
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.IsoOfInverse
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two twisting sheaves of a blowup agree, and the arithmetic transports

The repository carries the twisting sheaves of a blowup twice over:

* `AlgebraicGeometry.blowUpTwist`, glued from the absolute twists of the charts along the
  transition datum `Stacks.RelativeProj.Situation.twistTransition`, whose chart comparison is
  `Stacks.ProjTwistComparison.twistMap`;
* `Stacks.Blowup.reesTwist`, the relative twist of [Stacks, Tag 01NR] of the Rees algebra on the
  `SheafGradedAlgebra` substrate, whose chart comparison is
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`.

`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/BlowupTwistArith.lean` proves the two
arithmetic laws `𝒪(n) ⊗ 𝒪(m) ≅ 𝒪(n + m)` and `𝒪(-n) ≅ 𝒪(n)^∨` for the second and records that
they are **not** transported to the first because nothing identified the two chart comparisons.
They are identified now, by
`StacksFrontier/AlgebraicGeometry/ProjThetaCompare/`, and **this file carries the degreewise
comparison and both arithmetic laws across**.

## Main definitions

* `Stacks.Blowup.blowUpTwistReesIso`: the degreewise comparison, in the direction the glueing
  produces it.
* `Stacks.Blowup.pullbackBlowUpTwistIso`: **the degreewise comparison**
  `(reesProjBlowUpIso ℐ)^* 𝒪_{X'}(n) ≅ 𝒪(n)`, for an arbitrary scheme, an arbitrary
  quasi-coherent ideal sheaf and every `n : ℤ`.
* `Stacks.Blowup.blowUpTwistMulIso`: **the addition law for `AlgebraicGeometry.blowUpTwist`**,
  `𝒪_{X'}(n) ⊗ 𝒪_{X'}(m) ≅ 𝒪_{X'}(n + m)`.
* `Stacks.Blowup.blowUpTwistZeroIsoUnit`: `𝒪_{X'}(0) ≅ 𝒪_{X'}`.
* `Stacks.Blowup.blowUpTwistNegTensorIsoUnit`: `𝒪_{X'}(n) ⊗ 𝒪_{X'}(-n) ≅ 𝒪_{X'}`.
* `Stacks.Blowup.blowUpTwistNegIsoDual`: **the inversion law for
  `AlgebraicGeometry.blowUpTwist`**, `𝒪_{X'}(-n) ≅ 𝒪_{X'}(n)^∨`.

## The route

`Stacks.AlgebraicGeometry.ProjThetaCompare.chartComparisonIso` glues a comparison of the two
twisting sheaves over the charts of a relative `Proj` situation, taking the other side's chart
data — charts, chart identifications, graded rings with their restriction maps, and the
chart-refinement law — as hypotheses. The situation here is
`AlgebraicGeometry.reesSituation ℐ`, whose relative `Proj` **is** the blowup, and the other side
is the relative twist of the Rees algebra on the `SheafGradedAlgebra` substrate: its charts are
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj`'s, its chart identifications are
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso` in `restrict` form, and its
chart-refinement law is
`Stacks.AlgebraicGeometry.ProjThetaCompare.pullbackIsoOfRestrictIso_comp_twistMap_relativeTwist`.
The comparison of the two graded rings of sections over an affine open is
`Stacks.Blowup.reesChartGradedHom`, an isomorphism, so each chart twist comparison is invertible
by `Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id`.

With the comparison in hand the addition law transports by [Stacks, Tag 01CD], the comparison of
the inverse image of a tensor product with the tensor product of the inverse images, which is
unconditional. The three remaining laws are then the same monoidal consequences of the addition
law and invertibility that `BlowupTwistArith.lean` draws for `Stacks.Blowup.reesTwist`: an
invertible module isomorphic to its own square is the unit, and a tensor inverse of an invertible
module is its dual, [Stacks, Tag 0B8N] (c).

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.AlgebraicGeometry.ProjThetaCompare
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.ProjTwistComparison
open Stacks.RelativeVeryAmple

universe u

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The chart data of the comparison -/

/-- An affine open of the base, as an object of the small affine Zariski site. -/
public abbrev siteOf (W : X.affineOpens) : X.AffineZariskiSite :=
  ⟨W.1, show IsAffineOpen W.1 from W.2⟩

/-- Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` holds for the graded comparison of the
two spellings of the Rees algebra's sections: it is an isomorphism, with two-sided inverse
`Stacks.Blowup.reesChartGradedInv`. -/
public theorem irrelevant_le_map_reesChartGradedHom (W : X.affineOpens) :
    HomogeneousIdeal.irrelevant
          ((AlgebraicGeometry.reesSituation I).sectionRingGrading W.1)
      ≤ (HomogeneousIdeal.irrelevant ((reesSheafGradedAlgebra I).grading W.1)).map
          (reesChartGradedHom I (siteOf W)) := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun n hn x hx => ?_
  rw [← reesChartGradedHom_inv_apply I (siteOf W) x]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn
    ((reesChartGradedInv I (siteOf W)).map_mem hx))

/-- **The chart of the blowup over an affine open of the base, followed by the identification of
the blowup with the relative `Proj` of the Rees algebra, is the chart there**, through the graded
comparison of the two spellings of the Rees algebra's sections.

This is `Stacks.Blowup.chart_reesProjBlowUpIso_hom` read in the other direction: the chart
comparison `AlgebraicGeometry.Proj.map (reesChartGradedInv …)` is inverted by
`AlgebraicGeometry.Proj.map (reesChartGradedHom …)`, the two being the two halves of
`Stacks.Blowup.reesChartProjIso`. -/
public theorem reesChartProjIso_inv (W : X.affineOpens) :
    (reesChartProjIso I (siteOf W)).inv =
      AlgebraicGeometry.Proj.map (reesChartGradedHom I (siteOf W))
        (irrelevant_le_map_reesChartGradedHom I W) := rfl

/-- **The two chart comparisons of the two spellings of the Rees algebra's sections cancel.** -/
public theorem projMap_reesChartGradedHom_comp_inv (W : X.affineOpens) :
    AlgebraicGeometry.Proj.map (reesChartGradedHom I (siteOf W))
          (irrelevant_le_map_reesChartGradedHom I W)
        ≫ AlgebraicGeometry.Proj.map (reesChartGradedInv I (siteOf W))
          (irrelevant_le_map_reesChartGradedInv I (siteOf W))
      = 𝟙 (AlgebraicGeometry.Proj
          ((AlgebraicGeometry.reesSituation I).sectionRingGrading W.1)) := by
  have h := (reesChartProjIso I (siteOf W)).inv_hom_id
  rw [reesChartProjIso_inv, reesChartProjIso_hom] at h
  exact h

/-- **The chart of the blowup over an affine open of the base, followed by the identification of
the blowup with the relative `Proj` of the Rees algebra, is the chart there**, through the graded
comparison of the two spellings of the Rees algebra's sections.

This is `Stacks.Blowup.chart_reesProjBlowUpIso_hom` read in the other direction: the chart
comparison `AlgebraicGeometry.Proj.map (reesChartGradedInv …)` is inverted by
`AlgebraicGeometry.Proj.map (reesChartGradedHom …)`. -/
public theorem relativeProjChart_comp_reesProjBlowUpIso_inv (W : X.affineOpens) :
    Stacks.RelativeProj.Situation.relativeProjChart (AlgebraicGeometry.reesSituation I) W
          ≫ (reesProjBlowUpIso I).inv
      = AlgebraicGeometry.Proj.map (reesChartGradedHom I (siteOf W))
            (irrelevant_le_map_reesChartGradedHom I W)
        ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
            (reesSheafGradedAlgebra I)).chart W.1 W.2 := by
  have key : Stacks.RelativeProj.Situation.relativeProjChart
        (AlgebraicGeometry.reesSituation I) W
      = (AlgebraicGeometry.Proj.map (reesChartGradedHom I (siteOf W))
            (irrelevant_le_map_reesChartGradedHom I W)
          ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
              (reesSheafGradedAlgebra I)).chart W.1 W.2)
        ≫ (reesProjBlowUpIso I).hom := by
    refine Eq.trans (Category.id_comp _).symm ?_
    refine Eq.trans (eq_whisker (projMap_reesChartGradedHom_comp_inv I W).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (chart_reesProjBlowUpIso_hom I (siteOf W)).symm) ?_
    exact (Category.assoc _ _ _).symm
  refine Eq.trans (eq_whisker key _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (reesProjBlowUpIso I).hom_inv_id) ?_
  exact Category.comp_id _

/-- **Each chart twist comparison of the identification is invertible.** The graded comparison has
a two-sided inverse, so this is
`Stacks.ProjTwistComparison.isIso_twistMap_of_comp_eq_id`. -/
public theorem isIso_twistMap_reesChartGradedHom (n : ℤ) (W : X.affineOpens) :
    IsIso (twistMap (reesChartGradedHom I (siteOf W))
      (irrelevant_le_map_reesChartGradedHom I W) n) :=
  isIso_twistMap_of_comp_eq_id _ _ n (reesChartGradedInv I (siteOf W))
    (reesChartGradedHom_comp_inv I (siteOf W)) (reesChartGradedInv_comp_hom I (siteOf W))

/-! ### The degreewise comparison -/

/-- **The relative twist of the Rees algebra, transported to the blowup.** -/
public def blowUpTwistReesIso (n : ℤ) :
    (Scheme.Modules.pullback (reesProjBlowUpIso I).inv).obj (reesTwist I n)
      ≅ AlgebraicGeometry.blowUpTwist I n :=
  twistSheafAlgebraComparisonIso (s := AlgebraicGeometry.reesSituation I)
    (reesSheafGradedAlgebra I) n (reesProjBlowUpIso I).inv
    (fun W => reesChartGradedHom I (siteOf W))
    (fun W => irrelevant_le_map_reesChartGradedHom I W)
    (fun W => relativeProjChart_comp_reesProjBlowUpIso_inv I W)
    (fun {W W'} h => (reesChartGradedHom_comp_res I (siteOf W') (siteOf W) h).symm)
    (fun W => isIso_twistMap_reesChartGradedHom I n W)

/-- **The degreewise comparison of the two twisting sheaves of a blowup.** For an arbitrary scheme
`X`, an arbitrary quasi-coherent sheaf of ideals `ℐ` and every `n : ℤ`, the inverse image of
`AlgebraicGeometry.blowUpTwist ℐ n` along the identification
`Stacks.Blowup.reesProjBlowUpIso` of the relative `Proj` of the Rees algebra with the blowup is
the relative twist `Stacks.Blowup.reesTwist ℐ n` there. -/
public def pullbackBlowUpTwistIso (n : ℤ) :
    (Scheme.Modules.pullback (reesProjBlowUpIso I).hom).obj
        (AlgebraicGeometry.blowUpTwist I n)
      ≅ reesTwist I n :=
  (Scheme.Modules.pullback (reesProjBlowUpIso I).hom).mapIso
      (blowUpTwistReesIso I n).symm ≪≫
    (Scheme.Modules.pullbackComp (reesProjBlowUpIso I).hom
        (reesProjBlowUpIso I).inv).app (reesTwist I n) ≪≫
    (Scheme.Modules.pullbackCongr (reesProjBlowUpIso I).hom_inv_id).app (reesTwist I n) ≪≫
    (Scheme.Modules.pullbackId
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (reesSheafGradedAlgebra I)).scheme).app (reesTwist I n)

/-! ### The arithmetic, transported -/

/-- **The addition law for the twisting sheaves of a blowup**, for
`AlgebraicGeometry.blowUpTwist`: `𝒪_{X'}(n) ⊗ 𝒪_{X'}(m) ≅ 𝒪_{X'}(n + m)`, in all integer degrees,
for an arbitrary scheme and an arbitrary quasi-coherent sheaf of ideals.

`Stacks.Blowup.reesTwistAddIso` is the law for the relative twist of the Rees algebra; it is
carried across `Stacks.Blowup.blowUpTwistReesIso` by [Stacks, Tag 01CD], the comparison of the
inverse image of a tensor product with the tensor product of the inverse images. -/
@[ega "II 3.2.7" "special case"]
public def blowUpTwistMulIso (n m : ℤ) :
    AlgebraicGeometry.blowUpTwist I n ⊗ AlgebraicGeometry.blowUpTwist I m
      ≅ AlgebraicGeometry.blowUpTwist I (n + m) :=
  whiskerRightIso (blowUpTwistReesIso I n).symm (AlgebraicGeometry.blowUpTwist I m) ≪≫
    whiskerLeftIso
        ((Scheme.Modules.pullback (reesProjBlowUpIso I).inv).obj (reesTwist I n))
        (blowUpTwistReesIso I m).symm ≪≫
      (pullbackTensorModulesIso (reesProjBlowUpIso I).inv (reesTwist I n)
        (reesTwist I m)).symm ≪≫
      (Scheme.Modules.pullback (reesProjBlowUpIso I).inv).mapIso
        (reesTwistAddIso I n m) ≪≫
      blowUpTwistReesIso I (n + m)

/-- Reindexing of `𝒪_{X'}(n)` along an equality of degrees. -/
public def blowUpTwistCongr {n m : ℤ} (h : n = m) :
    AlgebraicGeometry.blowUpTwist I n ≅ AlgebraicGeometry.blowUpTwist I m :=
  eqToIso (congrArg (fun k : ℤ => AlgebraicGeometry.blowUpTwist I k) h)

/-- **`𝒪_{X'}(0) ≅ 𝒪_{X'}`.** The degree-zero twist is invertible and idempotent for the tensor
product — the addition law at `(0, 0)` — and an invertible module isomorphic to its own square is
the unit. -/
public def blowUpTwistZeroIsoUnit :
    AlgebraicGeometry.blowUpTwist I 0 ≅ 𝟙_ (AlgebraicGeometry.blowUp I).Modules :=
  let Y := AlgebraicGeometry.blowUp I
  let L := AlgebraicGeometry.blowUpTwist I 0
  let N := tensorPowModule Y L (-1)
  let eN : L ⊗ N ≅ 𝟙_ Y.Modules :=
    whiskerRightIso (tensorPowModuleOneIso Y L).symm N ≪≫
      Stacks.AlgebraicGeometry.TensorPowCongrInt.tensorPowModuleInvIsoRight Y L 1
  let h : L ⊗ L ≅ L := blowUpTwistMulIso I 0 0 ≪≫ blowUpTwistCongr I (by ring)
  (ρ_ L).symm ≪≫ whiskerLeftIso L eN.symm ≪≫ (α_ L L N).symm ≪≫
    whiskerRightIso h N ≪≫ eN

/-- **`𝒪_{X'}(n) ⊗ 𝒪_{X'}(-n) ≅ 𝒪_{X'}`**: the twists in opposite degrees are tensor
inverses. -/
public def blowUpTwistNegTensorIsoUnit (n : ℤ) :
    AlgebraicGeometry.blowUpTwist I n ⊗ AlgebraicGeometry.blowUpTwist I (-n)
      ≅ 𝟙_ (AlgebraicGeometry.blowUp I).Modules :=
  blowUpTwistMulIso I n (-n) ≪≫ blowUpTwistCongr I (by ring) ≪≫ blowUpTwistZeroIsoUnit I

/-- **The inversion law for the twisting sheaves of a blowup**, for
`AlgebraicGeometry.blowUpTwist`: `𝒪_{X'}(-n) ≅ 𝒪_{X'}(n)^∨`, in all integer degrees, for an
arbitrary scheme and an arbitrary quasi-coherent sheaf of ideals.

`𝒪_{X'}(-n)` is a tensor inverse of `𝒪_{X'}(n)` by
`Stacks.Blowup.blowUpTwistNegTensorIsoUnit`, and a tensor inverse of an invertible sheaf of
modules is its dual, [Stacks, Tag 0B8N] (c). -/
public def blowUpTwistNegIsoDual (n : ℤ) :
    AlgebraicGeometry.blowUpTwist I (-n) ≅
      Stacks.SheafOfModules.dualSheaf (AlgebraicGeometry.blowUp I).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.blowUp I))
        (AlgebraicGeometry.blowUpTwist I n) :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf _ _
    (AlgebraicGeometry.blowUpTwist I n) (AlgebraicGeometry.blowUpTwist I (-n))
    (blowUpTwistNegTensorIsoUnit I n)

end Stacks.Blowup

end
