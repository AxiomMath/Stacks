module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.AffineCharts
public import StacksFrontier.AlgebraicGeometry.AffineBlowupLift.Ring

/-!
# A morphism into the blowup, from an affine chart

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on it, `U` an affine open of `X` and
`a ∈ I.ideal U` a section of the ideal there. Let `B` be a `Γ(X, U)`-algebra in which the image
of `a` is a nonzerodivisor generating the ideal `I.ideal U · B`.

This file builds a morphism `Spec B ⟶ Bl_I(X)` over `X`, and identifies the morphism to `X` it
lies over.

Together with [Stacks, Tag 01WS] — the affine-local characterization of an effective Cartier
divisor by a nonzerodivisor — this is the local half of the existence statement that the
reduction of [Stacks, Tag 0806] in
`StacksFrontier/AlgebraicGeometry/BlowUpUniversal/Basic.lean` takes as its hypothesis `hlift`.
It is **not** that hypothesis: `hlift` quantifies over an arbitrary scheme over `X`, and getting
there from here needs a gluing step over an open cover of the source and of the base. See the
implementation notes.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp`: the morphism `Spec B ⟶ Bl_I(X)`.

## Main results

* `Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp_blowUpToBase`: the morphism lies over the
  morphism `Spec B ⟶ U ⊆ X` determined by the algebra structure.

## Implementation notes

The three steps are each already available:

1. the affine blowup algebra `Γ(X, U)[I/a]` maps to `B`, by the universal property proved in
   `StacksFrontier/AlgebraicGeometry/AffineBlowupLift/Ring.lean`;
2. `Spec` of that algebra *is* the standard chart of the blowup attached to `a`, by
   `AlgebraicGeometry.affineBlowupStandardOpenIso` ([Stacks, Tag 0804]), and the chart sits in
   the part of the blowup over `U` as a standard open of a projective spectrum;
3. that projective spectrum is the part of the blowup lying over `U`, by
   `Stacks.RelativeProj.Situation.relativeProjChart` ([Stacks, Tag 01NQ]).

The compatibility with the structure morphism to `X` is the composite of two squares that are
also already available: `AlgebraicGeometry.affineBlowupStandardOpenIso_over` for the chart and
the cartesian square `Stacks.RelativeProj.Situation.relativeProjChart_isPullback` for the
relative `Proj`. The only new input is that the ring map of step 1 is a `Γ(X, U)`-algebra map,
which is `AlgHom.comp_algebraMap`.

**What is still owed for `hlift`, precisely.** Given `f : Y ⟶ X` with `I.comap f` an effective
Cartier divisor, one wants a morphism `Y ⟶ Bl_I(X)` over `X`. Choose affine opens `U` of `X`
covering `X` and affine opens `V ⊆ f⁻¹(U)` covering `Y`; on each, [Stacks, Tag 01WS] should
produce a section of the ideal whose image in `Γ(V, ⊤)` is a nonzerodivisor generating the
restricted ideal, and then `toBlowUp` gives a morphism `V ≅ Spec Γ(V, ⊤) ⟶ Bl_I(X)` over `X`.
Those glue by `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, and the required agreement on
overlaps is **not** new mathematics: it is the already-proved uniqueness half,
`Stacks.AlgebraicGeometry.BlowUpUniversal.over_hom_unique`, applied on the overlap — which needs
only that `IsCartierOver` restricts to an open subscheme.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineBlowupLift

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)
  (B : Type u) [CommRing B] [Algebra (X.presheaf.obj (.op U.1)) B]

/-- The standard affine chart of the blowup attached to `a`, as a morphism into the blowup: the
standard open of the projective spectrum of the local Rees algebra, included into that spectrum
and then into the blowup through the chart over `U`. -/
public noncomputable def chartToBlowUp :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1).toScheme ⟶ blowUp I :=
  letI := (reesSituation I).sectionRingGradedRing U.1
  letI := (reesSituation I).sectionRingGradingGradedRing U.1
  (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1).ι ≫
    Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U

/-- The chart of the blowup at `a` lies over `U`: composing with the blowup morphism gives the
structure morphism of the chart to `U`, followed by the inclusion of `U`. -/
public theorem chartToBlowUp_blowUpToBase :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    chartToBlowUp I U a ≫ blowUpToBase I =
      (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
          (reesDegreeOne I U a).1).ι ≫
        Stacks.RelativeProj.Situation.projInclusionToOpen (reesSituation I) U.1 U.2 ≫ U.1.ι := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  simp only [chartToBlowUp, Category.assoc,
    (Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) U).w]

variable (hnzd : algebraMap (X.presheaf.obj (.op U.1)) B (a : X.presheaf.obj (.op U.1)) ∈
    nonZeroDivisors B)
  (hIB : (I.ideal U).map (algebraMap (X.presheaf.obj (.op U.1)) B) =
    Ideal.span {algebraMap (X.presheaf.obj (.op U.1)) B (a : X.presheaf.obj (.op U.1))})

include hnzd hIB

/-- **A morphism into the blowup.** If the image of the section `a` of `I` in a `Γ(X, U)`-algebra
`B` is a nonzerodivisor generating `I.ideal U · B`, then `Spec B` maps to the blowup of `X` in
`I`, through the standard chart attached to `a`.

The ring map is the one supplied by the universal property of the affine blowup algebra
`Γ(X, U)[I/a]`, and `Spec` of that algebra is the chart, by [Stacks, Tag 0804]. -/
public noncomputable def toBlowUp : Spec (.of B) ⟶ blowUp I :=
  letI := (reesSituation I).sectionRingGradedRing U.1
  letI := (reesSituation I).sectionRingGradingGradedRing U.1
  Spec.map (CommRingCat.ofHom (lift hnzd hIB
      (Rₐ := Localization.Away (a : X.presheaf.obj (.op U.1)))).toRingHom) ≫
    (affineBlowupStandardOpenIso I U a).hom ≫ chartToBlowUp I U a

/-- **The morphism into the blowup lies over `X`.** Its composite with the blowup morphism is the
morphism `Spec B ⟶ U ⊆ X` determined by the `Γ(X, U)`-algebra structure of `B`. -/
public theorem toBlowUp_blowUpToBase :
    toBlowUp I U a B hnzd hIB ≫ blowUpToBase I =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (.op U.1)) B)) ≫
        U.2.isoSpec.inv ≫ U.1.ι := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  have hover := congrArg (fun t => t ≫ U.1.ι) (affineBlowupStandardOpenIso_over I U a)
  simp only [Category.assoc] at hover
  simp only [toBlowUp, Category.assoc, chartToBlowUp_blowUpToBase]
  rw [hover, ← Category.assoc (Spec.map _), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact (lift hnzd hIB (Rₐ := Localization.Away (a : X.presheaf.obj (.op U.1)))).comp_algebraMap

end Stacks.AlgebraicGeometry.AffineBlowupLift

end
