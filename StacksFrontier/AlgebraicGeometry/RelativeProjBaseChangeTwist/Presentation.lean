module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.ProjPresentationCompare.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.PullbackSituation

/-!
# The two relative homogeneous spectra of one quasi-coherent graded algebra, as a named isomorphism

Situation 01NN is formalized twice in this library: as
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, whose relative `Proj` is
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` and carries the twists of Tag 01NR, and as
`Stacks.RelativeProj.Situation`, whose relative `Proj` is
`Stacks.RelativeProj.Situation.relativeProj` and carries the base-change square. This file reads
a `SheafGradedAlgebra` as a `Situation` on the same data and names the comparison isomorphism of
the two glueings, together with its action on the charts.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation`: the `Situation` on the data
  of a `SheafGradedAlgebra`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.chartHom` and `chartInv`: the graded ring
  comparison of the two graded rings of sections over an affine open, and its inverse.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso`: **the isomorphism of the
  two relative homogeneous spectra**, over the base.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.situation_pullback`: the situation of the
  pullback `g^*A` is the pullback of the situation of `A`, by `rfl`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.presentationIso_hom_toBase` and
  `chart_presentationIso_hom`: the isomorphism lies over the base and is `Proj.map` of the
  inverse graded comparison on each chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open Stacks.AlgebraicGeometry.RelativeProjDescent Stacks.AlgebraicGeometry.ProjPresentation

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The graded algebra of a `SheafGradedAlgebra`, read over the structure sheaf of rings. -/
abbrev algebra : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf :=
  situationAlgebra A

/-- The multiplication is commutative. -/
theorem isCommutative : IsCommutative (algebra A) :=
  fun i j U a b => A.mul_comm i j U.unop a b

/-- The negative pieces vanish. -/
theorem vanishesInNegativeDegrees : VanishesInNegativeDegrees (algebra A) :=
  fun n hn U x => section_eq_zero_of_isZero (A.negative_isZero n hn) U.unop x

/-- **The relative `Proj` situation on the data of a `SheafGradedAlgebra`.** -/
abbrev situation : Stacks.RelativeProj.Situation.{u} :=
  situationOfGradedAlgebra (algebra A) (isCommutative A) (vanishesInNegativeDegrees A)
    A.isQuasicoherent

/-- Reading the graded algebra back as a `SheafGradedAlgebra` gives `A` on the nose. -/
theorem toSheafGradedAlgebra_algebra :
    toSheafGradedAlgebra (algebra A) (isCommutative A) (vanishesInNegativeDegrees A)
      A.isQuasicoherent = A := rfl

/-- **The situation of the pullback is the pullback of the situation**, on the nose. -/
theorem situation_pullback {S' : Scheme.{u}} (g : S' ⟶ S) :
    situation (A.pullback g) = (situation A).pullback g := rfl

/-- The graded-ring structure on the homogeneous sections of the situation over an open. -/
instance gcommRingSituation (U : S.Opens) :
    DirectSum.GCommRing ((situation A).sectionPieces U) :=
  Stacks.RelativeProj.Situation.sectionRingGradedRing (situation A) U

/-- The internal grading of the section ring of the situation over an open. -/
instance gradedRingSituation (U : S.Opens) :
    GradedRing ((situation A).sectionRingGrading U) :=
  Stacks.RelativeProj.Situation.sectionRingGradingGradedRing (situation A) U

/-- The graded-ring comparison of the two substrates' sections over an affine open. -/
def chartHom (U : S.AffineZariskiSite) :
    (A.toGradedAlgebra).grading U →+*ᵍ (situation A).sectionRingGrading (siteAffineOpen U).1 :=
  situationSectionGradedHom (algebra A) (isCommutative A) (vanishesInNegativeDegrees A)
    A.isQuasicoherent U.toOpens

/-- The inverse graded-ring comparison. -/
def chartInv (U : S.AffineZariskiSite) :
    (situation A).sectionRingGrading (siteAffineOpen U).1 →+*ᵍ (A.toGradedAlgebra).grading U :=
  situationSectionGradedInv (algebra A) (isCommutative A) (vanishesInNegativeDegrees A)
    A.isQuasicoherent U.toOpens

/-- `chartInv` is a left inverse of `chartHom`. -/
theorem chartInv_comp_chartHom (U : S.AffineZariskiSite) :
    (chartInv A U).comp (chartHom A U) = GradedRingHom.id ((A.toGradedAlgebra).grading U) :=
  situationSectionGradedInv_comp_hom (algebra A) (isCommutative A)
    (vanishesInNegativeDegrees A) A.isQuasicoherent U.toOpens

/-- `chartInv` is a right inverse of `chartHom`. -/
theorem chartHom_comp_chartInv (U : S.AffineZariskiSite) :
    (chartHom A U).comp (chartInv A U) =
      GradedRingHom.id ((situation A).sectionRingGrading (siteAffineOpen U).1) :=
  situationSectionGradedHom_comp_inv (algebra A) (isCommutative A)
    (vanishesInNegativeDegrees A) A.isQuasicoherent U.toOpens

/-- The comparison carries the degree-zero identification of `A` to that of the situation. -/
theorem strZero_comp_chartHom (U : S.AffineZariskiSite) :
    (A.toGradedAlgebra).strZero U ≫ CommRingCat.ofHom (chartHom A U).gradedZeroRingHom =
      (Stacks.RelativeProj.Situation.chartData (situation A)).base (siteAffineOpen U) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  refine Eq.trans (congrArg (situationSectionRingEquiv (algebra A) (isCommutative A)
    (vanishesInNegativeDegrees A) A.isQuasicoherent U.toOpens)
    ((A.toGradedAlgebra).coe_strZero_apply U r)) ?_
  refine Eq.trans (situationSectionRingEquiv_strHom (algebra A) (isCommutative A)
    (vanishesInNegativeDegrees A) A.isQuasicoherent U.toOpens r) ?_
  exact (Stacks.AlgebraicGeometry.RelativeProj.projZeroRingHom'_coe_of_mem _
    (Stacks.RelativeProj.Situation.sectionRingBaseMap_mem_zero
      (situation A) U.toOpens r)).symm

/-- The charts of the situation's relative `Proj`, read as a chart family for `A`. -/
def chartFamily :
    ChartFamily (A.toGradedAlgebra) (Stacks.RelativeProj.Situation.relativeProj (situation A))
      (Stacks.RelativeProj.Situation.relativeProjToBase (situation A)) :=
  ProjPresentation.chartFamily (Stacks.RelativeProj.Situation.chartData (situation A))
    (A.toGradedAlgebra) (chartHom A) (chartInv A) (chartInv_comp_chartHom A)
    (chartHom_comp_chartInv A)
    (fun _ _ h => GradedRingHom.ext fun x =>
      situationSectionRingEquiv_resRingHom (algebra A) (isCommutative A)
        (vanishesInNegativeDegrees A) A.isQuasicoherent h x)
    (strZero_comp_chartHom A)

/-- **The relative `Proj` of a `SheafGradedAlgebra` is the relative `Proj` of its situation.** -/
def presentationIso :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).scheme ≅
      Stacks.RelativeProj.Situation.relativeProj (situation A) :=
  (chartFamily A).iso

/-- The comparison lies over the base. -/
theorem presentationIso_hom_toBase :
    (presentationIso A).hom ≫ Stacks.RelativeProj.Situation.relativeProjToBase (situation A) =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase :=
  (chartFamily A).iso_hom_comp

/-- The comparison of the irrelevant ideals that `Proj.map` of the inverse comparison asks for. -/
theorem irrelevant_le_map_chartInv (U : S.AffineZariskiSite) :
    HomogeneousIdeal.irrelevant ((A.toGradedAlgebra).grading U) ≤
      (HomogeneousIdeal.irrelevant ((situation A).sectionRingGrading
        (siteAffineOpen U).1)).map (chartInv A U) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (chartInv_comp_chartHom A U)

/-- **The comparison on the charts** is `Proj.map` of the inverse graded comparison. -/
theorem chart_presentationIso_hom (U : S.AffineZariskiSite) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart U.toOpens
        (isAffineOpen_toOpens U) ≫ (presentationIso A).hom =
      AlgebraicGeometry.Proj.map (chartInv A U) (irrelevant_le_map_chartInv A U) ≫
        Stacks.RelativeProj.Situation.relativeProjChart (situation A) (siteAffineOpen U) :=
  (chartFamily A).chart_iso_hom U

/-- The comparison of the irrelevant ideals that `Proj.map` of the comparison asks for. -/
theorem irrelevant_le_map_chartHom (U : S.AffineZariskiSite) :
    HomogeneousIdeal.irrelevant ((situation A).sectionRingGrading (siteAffineOpen U).1) ≤
      (HomogeneousIdeal.irrelevant ((A.toGradedAlgebra).grading U)).map (chartHom A U) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (chartHom_comp_chartInv A U)

/-- **The inverse comparison on the charts**: the chart of the situation followed by the inverse
comparison is `Proj.map` of the comparison followed by the chart of `A`. -/
theorem relativeProjChart_presentationIso_inv (U : S.AffineZariskiSite) :
    Stacks.RelativeProj.Situation.relativeProjChart (situation A) (siteAffineOpen U) ≫
        (presentationIso A).inv =
      AlgebraicGeometry.Proj.map (chartHom A U) (irrelevant_le_map_chartHom A U) ≫
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart U.toOpens
          (isAffineOpen_toOpens U) := by
  refine (Iso.comp_inv_eq _).2 ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun z => AlgebraicGeometry.Proj.map (chartHom A U)
    (irrelevant_le_map_chartHom A U) ≫ z) (chart_presentationIso_hom A U)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (fun z => z ≫ Stacks.RelativeProj.Situation.relativeProjChart
    (situation A) (siteAffineOpen U)) (AlgebraicGeometry.Proj.map_comp _ _ _ _))
  refine Eq.trans ?_ (congrArg (fun z => z ≫ Stacks.RelativeProj.Situation.relativeProjChart
    (situation A) (siteAffineOpen U))
      (AlgebraicGeometry.Proj.map_congr (chartHom_comp_chartInv A U) _ (by simp))).symm
  refine Eq.trans ?_ (congrArg (fun z => z ≫ Stacks.RelativeProj.Situation.relativeProjChart
    (situation A) (siteAffineOpen U)) AlgebraicGeometry.Proj.map_id).symm
  exact (Category.id_comp _).symm

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
