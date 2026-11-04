module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartSourceSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartSourceEquation

/-!
# The source comparison at a presented chart, factored at the represented chart space

`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` is
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` at the data a chart
presentation carries, by `rfl`
(`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq`).  This file carries its
factorization into three factors across, at the reading of the chart space that the squares of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartSourceSquare` use.

## Why it has to be done at the isomorphism, and here

The three constituent squares of the chart-level source square read the chart space as
`AlgebraicGeometry.Space.schemeSpace` of the chart's object of the site; both
`.chartDifferentialsAssociatedCotangentIso` and `.chartSourceIso` read it as
`AlgebraicGeometry.Space.chartSpace`, because that is what the *inferred* type of
`AlgebraicGeometry.Space.chartToSpace` gives and a type ascription does not change a term's type.
Crossing those two readings inside a composite of chart-level comparisons is a `whnf` timeout; at
an isomorphism it costs nothing.  So the crossing is made once, between the isomorphisms, and the
factorization of the composite is taken from it by `congrArg` — exactly as
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_eq_represented` and
`.chartDifferentialsAssociatedCotangentIso_hom_represented` do for the general comparison.

This is what an assembler needs: the chart-level square is
`CategoryTheory.square_of_functor_factorizations_of_paste` fed a factorization of each of its two
sides, and the factorization must be the one whose three factors are the terms the three squares
write.  Generalising the square over the comparison instead — taking it as a variable with
its factorization as a hypothesis — does not work: the variable's *type* carries the reading, so
instantiating it at `.chartSourceIso` reopens the junction underneath
`CategoryTheory.Functor.map`, and the kernel does not finish.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq_represented`: the source
  comparison at a presented chart **is** the three-factor composite, read at the represented chart
  space.
* `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_hom_represented`: the same on
  `hom`, which is the factorization an assembler takes.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CS and 04CU are registered at the isomorphisms
composed here.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1}
  (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The source comparison at a presented chart, factored at the represented chart space.**
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_eq_represented` at the data the
presentation carries, carried across
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq`.

The factored side is stated first, which is what puts the equation at the represented reading: an
equation takes the category of whichever side elaborates first.  Both steps are between
isomorphisms, which is the one level at which the two readings of the chart space meet
affordably. -/
theorem chartSourceIso_eq_represented
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (modulePullbackCompIso C S hS
            (X := schemeSpace ((SmallEtale.toOver C S hS Z.1.toFunctor).obj
              (P.subEtaleChart (Z := Z) (a := a))))
            (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
              (P.subEtaleChart (Z := Z) (a := a))) a).app
          (sheafOfDifferentials C S hS q) ≪≫
        chartCompositeDifferentialsAssociatedIso C S hS q
          (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
          ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
          ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
          P.chartSq' (P.incl ≫ P.liftHom)
          (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
            (P.subEtaleChart (Z := Z) (a := a)) ≫ a) P.subChart_comp ≪≫
        (representedAssociatedModule C S hS
          ((SmallEtale.toOver C S hS Z.1.toFunctor).obj (P.subEtaleChart (Z := Z) (a := a)))
          (schemeSpace ((SmallEtale.toOver C S hS Z.1.toFunctor).obj
            (P.subEtaleChart (Z := Z) (a := a)))).property).mapIso
            ((Scheme.Modules.pullback
                ((BigFppfOver.toScheme C S hS).map (P.incl ≫ P.liftHom))).mapIso
              (Scheme.Hom.cotangentSheafIso
                ((BigFppfOver.toScheme C S hS).map P.chartHom))) =
      chartSourceIso C S hS P hw hv :=
  (chartDifferentialsAssociatedCotangentIso_eq_represented C S hS q a
      (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
      ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
      ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
      P.chartSq' (P.subEtaleChart (Z := Z) (a := a)) (P.incl ≫ P.liftHom)
      P.subChart_comp).trans
    (chartSourceIso_eq C S hS P hw hv).symm

/-- **The factorization of the source comparison at a presented chart**, at the represented chart
space: `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq_represented` on `hom`, by
`congrArg`.

This is the form `CategoryTheory.square_of_functor_factorizations_of_paste` takes as a
factorization of one side of the chart-level source square, and each of its three factors is the
term the corresponding square of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartSourceSquare` writes. -/
theorem chartSourceIso_hom_represented
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    ((modulePullbackCompIso C S hS
              (X := schemeSpace ((SmallEtale.toOver C S hS Z.1.toFunctor).obj
                (P.subEtaleChart (Z := Z) (a := a))))
              (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
                (P.subEtaleChart (Z := Z) (a := a))) a).app
          (sheafOfDifferentials C S hS q)).hom ≫
        (chartCompositeDifferentialsAssociatedIso C S hS q
            (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
            ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
            ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
            P.chartSq' (P.incl ≫ P.liftHom)
            (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
              (P.subEtaleChart (Z := Z) (a := a)) ≫ a) P.subChart_comp).hom ≫
          (representedAssociatedModule C S hS
              ((SmallEtale.toOver C S hS Z.1.toFunctor).obj (P.subEtaleChart (Z := Z) (a := a)))
              (schemeSpace ((SmallEtale.toOver C S hS Z.1.toFunctor).obj
                (P.subEtaleChart (Z := Z) (a := a)))).property).map
            ((Scheme.Modules.pullback
                ((BigFppfOver.toScheme C S hS).map (P.incl ≫ P.liftHom))).map
              (Scheme.Hom.cotangentSheafIso
                ((BigFppfOver.toScheme C S hS).map P.chartHom)).hom) =
      (chartSourceIso C S hS P hw hv).hom :=
  congrArg Iso.hom (chartSourceIso_eq_represented C S hS P hw hv)

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
