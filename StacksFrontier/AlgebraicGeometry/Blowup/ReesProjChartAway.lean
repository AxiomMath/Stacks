module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjChartBridge
public import StacksFrontier.AlgebraicGeometry.BlowUpChartCover.Cartier
public import StacksFrontier.AlgebraicGeometry.HomogeneousAwayMapCriteria.Basic

/-!
# The standard affine blowup chart as a degree-one `Proj` chart on the sheaf substrate

`Stacks.BlowUpChartCover.chart I U a` is the standard affine chart of the blowup of `X` in `I`
attached to an affine open `U` of the base and a section `a` of `I` on it: it is `Spec` of the
affine blowup algebra `Γ(X, U)[I/a]`, mapped into `Bl_I(X)`. It is built out of
`AlgebraicGeometry.reesSituation`, the spelling of the Rees algebra out of which the blowup is
glued.

The results about closed subschemes of a relative `Proj` — Tags 0801, 0802 and 0803 — are
instead stated on the `SheafGradedAlgebra` substrate, for the relative `Proj` of
`Stacks.Blowup.reesSheafGradedAlgebra I`. To read one of them on a standard affine chart one
needs the chart presented on *that* substrate: as the degree-one chart
`AlgebraicGeometry.Proj.awayι` attached to the image of `a` in the sheaf-substrate graded ring
of sections.

This file supplies that presentation. The degree-one element is the image of
`AlgebraicGeometry.reesDegreeOne` under the graded comparison
`Stacks.Blowup.reesChartGradedInv` of `ReesProjChartBridge.lean`, its away-localization is
identified with `Γ(X, U)[I/a]`, and the two charts agree under that identification.

## Main definitions

* `Stacks.Blowup.chartSite`: an affine open of the base, as an object of the small affine
  Zariski site.
* `Stacks.Blowup.reesSheafDegreeOne`: the section `a`, read as a degree-one element of the
  sheaf-substrate graded ring of sections of the Rees algebra over `U`.
* `Stacks.Blowup.chartAwayEquiv`: the identification of the degree-zero away-localization at
  that element with the affine blowup algebra `Γ(X, U)[I/a]`.
* `Stacks.Blowup.awayChart`: the standard chart of the blowup, built on the sheaf substrate.

## Main results

* `Stacks.Blowup.bijective_awayMap_reesChartGradedInv`: the graded comparison induces a
  bijection of the away-localizations at `a`.
* `Stacks.Blowup.chart_eq_specMap_awayι`: the standard affine chart of
  `BlowUpChartCover.chart` factors as `Spec` of the blowup-algebra identification, followed by
  the degree-one `Proj` chart of `AlgebraicGeometry.reesSituation` and the relative-`Proj`
  chart over `U`.
* `Stacks.Blowup.specMap_chartAwayEquiv_awayChart`: **the standard affine blowup chart factors
  through the degree-one `Proj` chart of the relative `Proj` of the Rees algebra on the
  `SheafGradedAlgebra` substrate.**

## Implementation notes

Writing `A` for `Stacks.Blowup.reesSheafGradedAlgebra I` and `𝒞` for `A.toGradedAlgebra`, the
bijectivity of `HomogeneousLocalization.Away.map (reesChartGradedInv I (chartSite U)) a⁽¹⁾` is
not deduced from the fact that the graded comparison is an isomorphism — `Away.map` is not
packaged as a functor on graded ring isomorphisms — but from the two elementwise criteria of
`StacksFrontier/AlgebraicGeometry/HomogeneousAwayMapCriteria/Basic.lean`, each of which the
two-sided inverse `Stacks.Blowup.reesChartGradedHom` discharges with the trivial witness
`k = 0`.

The two sides of the main result are compared after factoring each through the *same* morphism
`Proj.awayι` of `AlgebraicGeometry.reesSituation` composed with
`Stacks.RelativeProj.Situation.relativeProjChart`: on the `BlowUpChartCover` side by unfolding
`AlgebraicGeometry.affineBlowupStandardOpenIso` and applying Mathlib's
`AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι`, and on the sheaf-substrate side by the chart
lemma `Stacks.Blowup.chart_reesProjBlowUpIso_hom` together with Mathlib's
`AlgebraicGeometry.Proj.awayι_comp_map`. What is left is an equality of two ring maps, which is
the computation rule `Stacks.Blowup.chartAwayEquiv_awayMap`.

## Not done here

No Stacks tag is claimed. The charts themselves are Tag 0804 and are tagged where they are
built; the comparison of two presentations of one chart is not a labelled assertion of the
source.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-! ### The affine open as a site object, and the degree-one element on the sheaf substrate -/

/-- An affine open of the base, packaged as an object of the small affine Zariski site: the
index of the charts of the relative `Proj` on the `SheafGradedAlgebra` substrate. -/
public abbrev chartSite : X.AffineZariskiSite := ⟨U.1, show IsAffineOpen U.1 from U.2⟩

/-- Reading the site object `Stacks.Blowup.chartSite U` back as an affine open returns `U`. -/
public theorem siteAffineOpen_chartSite : siteAffineOpen (chartSite U) = U := rfl

/-- **The section `a`, as a degree-one element of the sheaf-substrate graded ring of sections**
of the Rees algebra over `U`: the image of `AlgebraicGeometry.reesDegreeOne` under the graded
comparison of the two spellings of the Rees algebra's sections. -/
public def reesSheafDegreeOne :
    ((reesSheafGradedAlgebra I).toGradedAlgebra).ring (chartSite U) :=
  reesChartGradedInv I (chartSite U) (AlgebraicGeometry.reesDegreeOne I U a).1

/-- The degree-one element of the sheaf substrate is homogeneous of degree one. -/
public theorem reesSheafDegreeOne_mem :
    reesSheafDegreeOne I U a ∈
      ((reesSheafGradedAlgebra I).toGradedAlgebra).grading (chartSite U) 1 :=
  Graded.map_mem _ (AlgebraicGeometry.reesDegreeOne I U a).2

/-- The graded comparison carries the degree-one element of the sheaf substrate back to
`AlgebraicGeometry.reesDegreeOne`. -/
public theorem reesChartGradedHom_reesSheafDegreeOne :
    reesChartGradedHom I (chartSite U) (reesSheafDegreeOne I U a) =
      (AlgebraicGeometry.reesDegreeOne I U a).1 :=
  reesChartGradedHom_inv_apply I (chartSite U) _

/-! ### The induced map of away-localizations is bijective -/

/-- **The graded comparison induces a bijection of the away-localizations at `a`.** Both
criteria of `StacksFrontier/AlgebraicGeometry/HomogeneousAwayMapCriteria/Basic.lean` are
discharged with the trivial witness, because the comparison has a two-sided inverse. -/
public theorem bijective_awayMap_reesChartGradedInv :
    Function.Bijective (HomogeneousLocalization.Away.map (reesChartGradedInv I (chartSite U))
      (AlgebraicGeometry.reesDegreeOne I U a).1) := by
  constructor
  · refine (Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMap_injective_iff
      (reesChartGradedInv I (chartSite U)) (AlgebraicGeometry.reesDegreeOne I U a).2).2 ?_
    intro n x _ hx
    obtain rfl : x = 0 := by
      rw [← reesChartGradedHom_inv_apply I (chartSite U) x, hx, map_zero]
    exact ⟨0, mul_zero _⟩
  · refine (Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMap_surjective_iff
      (reesChartGradedInv I (chartSite U)) (AlgebraicGeometry.reesDegreeOne I U a).2).2 ?_
    intro n b hb
    exact ⟨0, reesChartGradedHom I (chartSite U) b,
      by simpa only [zero_add] using Graded.map_mem (reesChartGradedHom I (chartSite U)) hb,
      by simpa only [pow_zero, one_mul] using reesChartGradedInv_hom_apply I (chartSite U) b⟩

/-- **The away-localization of the sheaf substrate at the degree-one element is the affine
blowup algebra** `Γ(X, U)[I/a]`: the graded comparison identifies it with the away-localization
of `AlgebraicGeometry.reesSituation`, which is the blowup algebra by [Stacks, Tag 0804]. -/
public def chartAwayEquiv :
    HomogeneousLocalization.Away
        (((reesSheafGradedAlgebra I).toGradedAlgebra).grading (chartSite U))
        (reesSheafDegreeOne I U a) ≃+*
      Stacks.BlowUpChartCover.chartRing I U a :=
  (RingEquiv.ofBijective _ (bijective_awayMap_reesChartGradedInv I U a)).symm.trans
    (AlgebraicGeometry.reesToAffineBlowupEquiv I U a)

/-- The identification of the away-localization with the blowup algebra undoes the map induced
by the graded comparison. -/
public theorem chartAwayEquiv_awayMap
    (z : HomogeneousLocalization.Away
      ((AlgebraicGeometry.reesSituation I).sectionRingGrading U.1)
      (AlgebraicGeometry.reesDegreeOne I U a).1) :
    chartAwayEquiv I U a (HomogeneousLocalization.Away.map
        (reesChartGradedInv I (chartSite U)) (AlgebraicGeometry.reesDegreeOne I U a).1 z) =
      AlgebraicGeometry.reesToAffineBlowupEquiv I U a z :=
  congrArg (AlgebraicGeometry.reesToAffineBlowupEquiv I U a)
    ((RingEquiv.ofBijective _ (bijective_awayMap_reesChartGradedInv I U a)).symm_apply_apply z)

/-! ### The chart on the sheaf substrate -/

/-- **The standard affine chart of the blowup, built on the `SheafGradedAlgebra` substrate**:
the degree-one `Proj` chart at `Stacks.Blowup.reesSheafDegreeOne`, followed by the chart of the
relative `Proj` over `U` and the identification of that relative `Proj` with the blowup. -/
public def awayChart :
    Spec (.of (HomogeneousLocalization.Away
        (((reesSheafGradedAlgebra I).toGradedAlgebra).grading (chartSite U))
        (reesSheafDegreeOne I U a))) ⟶ AlgebraicGeometry.blowUp I :=
  AlgebraicGeometry.Proj.awayι _ (reesSheafDegreeOne I U a) (reesSheafDegreeOne_mem I U a)
      Nat.one_pos ≫
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (reesSheafGradedAlgebra I)).chart
        (chartSite U).toOpens (isAffineOpen_toOpens (chartSite U)) ≫
      (Stacks.Blowup.reesProjBlowUpIso I).hom

/-- **The standard affine blowup chart, factored through the degree-one `Proj` chart of
`AlgebraicGeometry.reesSituation`.** This is `Stacks.BlowUpChartCover.chart` with the
identification of [Stacks, Tag 0804] moved onto the ring side. -/
public theorem chart_eq_specMap_awayι :
    Stacks.BlowUpChartCover.chart I U a =
      Spec.map (CommRingCat.ofHom
          (AlgebraicGeometry.reesToAffineBlowupEquiv I U a).toRingHom) ≫
        AlgebraicGeometry.Proj.awayι
            ((AlgebraicGeometry.reesSituation I).sectionRingGrading U.1)
            (AlgebraicGeometry.reesDegreeOne I U a).1
            (AlgebraicGeometry.reesDegreeOne I U a).2 Nat.one_pos ≫
          Stacks.RelativeProj.Situation.relativeProjChart
            (AlgebraicGeometry.reesSituation I) U := by
  dsimp only [Stacks.BlowUpChartCover.chart,
    Stacks.AlgebraicGeometry.AffineBlowupLift.chartToBlowUp]
  simp only [AlgebraicGeometry.affineBlowupStandardOpenIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Iso.symm_hom, Scheme.Spec_map, Category.assoc,
    RingEquiv.toCommRingCatIso_hom]
  rw [← Category.assoc (Proj.basicOpenIsoSpec _ _ _ _).inv, Proj.basicOpenIsoSpec_inv_ι]
  rfl

/-- The chart on the sheaf substrate, factored through the degree-one `Proj` chart of
`AlgebraicGeometry.reesSituation`. -/
public theorem awayChart_eq_specMap_awayι :
    awayChart I U a =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
          (reesChartGradedInv I (chartSite U))
          (AlgebraicGeometry.reesDegreeOne I U a).1)) ≫
        AlgebraicGeometry.Proj.awayι
            ((AlgebraicGeometry.reesSituation I).sectionRingGrading U.1)
            (AlgebraicGeometry.reesDegreeOne I U a).1
            (AlgebraicGeometry.reesDegreeOne I U a).2 Nat.one_pos ≫
          Stacks.RelativeProj.Situation.relativeProjChart
            (AlgebraicGeometry.reesSituation I) U := by
  refine Eq.trans (congrArg (AlgebraicGeometry.Proj.awayι _ (reesSheafDegreeOne I U a)
    (reesSheafDegreeOne_mem I U a) Nat.one_pos ≫ ·)
      (chart_reesProjBlowUpIso_hom I (chartSite U))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.assoc _ _ _))
  congr 1
  exact AlgebraicGeometry.Proj.awayι_comp_map (reesChartGradedInv I (chartSite U))
    (irrelevant_le_map_reesChartGradedInv I (chartSite U)) Nat.one_pos _
    (AlgebraicGeometry.reesDegreeOne I U a).2

/-- **The standard affine blowup chart factors through the degree-one `Proj` chart of the
relative `Proj` of the Rees algebra on the `SheafGradedAlgebra` substrate.** -/
public theorem specMap_chartAwayEquiv_awayChart :
    Spec.map (CommRingCat.ofHom (chartAwayEquiv I U a).toRingHom) ≫ awayChart I U a =
      Stacks.BlowUpChartCover.chart I U a := by
  have key : CommRingCat.ofHom (HomogeneousLocalization.Away.map
          (reesChartGradedInv I (chartSite U))
          (AlgebraicGeometry.reesDegreeOne I U a).1) ≫
        CommRingCat.ofHom (chartAwayEquiv I U a).toRingHom =
      CommRingCat.ofHom (AlgebraicGeometry.reesToAffineBlowupEquiv I U a).toRingHom :=
    CommRingCat.hom_ext (RingHom.ext (chartAwayEquiv_awayMap I U a))
  rw [awayChart_eq_specMap_awayι, chart_eq_specMap_awayι]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  congr 1
  exact Eq.trans (Spec.map_comp _ _).symm (congrArg Spec.map key)

end Stacks.Blowup

end
