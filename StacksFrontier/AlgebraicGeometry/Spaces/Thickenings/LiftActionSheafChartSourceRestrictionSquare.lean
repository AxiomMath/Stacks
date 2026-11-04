module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftRestrictionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartSourceFactorization

/-!
# The source comparison at a presented chart is natural in the restriction

`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` is the source comparison at the
étale chart of the closed subspace that a chart presentation presents.  Restricting the
presentation to a smaller étale chart of `X'` produces a second presented chart and a morphism
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subEtaleChartMap` between them, and
this file proves that the source comparison **commutes with that morphism**, up to the comparison
of [Stacks Project, Tag 03LU] in front and the Zariski comparison of two pullback cotangent
sheaves behind.

This is the third of the four compatibilities that
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`
decomposes into.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.chartSourceIso_hom_square`: **the
  source comparison at a presented chart commutes with the morphism of presented charts attached
  to a restriction.**

## How it is proved

`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom_square_of_chartMap` is the
same square at bare data, and the restriction supplies every one of its arguments: the two charts
are the two presented charts, the morphism between them is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subEtaleChartMap`, the two morphisms of
the site through which the chart composites factor are the reductions of the two presented lifts,
the factorization relating them is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap_comp_redHom`, and the two chart
composites factor by `AlgebraicGeometry.Space.ChartLiftPresentation.subChart_comp`.  The only work
beyond that instantiation is carrying each of its two comparisons over to
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso`, and that is done **at the
isomorphism** — `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq` read with the
general comparison on the *left*, so that the equation's type is the general comparison's — and
projected onto the square's two sides by `congrArg`.

## The three readings, and which one the statement has

The chart space has two spellings and so does the chart's object of the site, and this square
meets both.  `chartSourceIso`'s own type reads the chart space as
`AlgebraicGeometry.Space.chartSpace` and the chart's object as
`AlgebraicGeometry.Space.ChartLiftPresentation.sub`, because that is what the inferred types of
`AlgebraicGeometry.Space.chartToSpace` and of `P.incl ≫ P.liftHom` give.  The library's square reads
them as `AlgebraicGeometry.Space.schemeSpace` and `(AlgebraicGeometry.SmallEtale.toOver … ).obj A`
for the chart `A`.  Each pair is the same object and a different term, and crossing either one
inside a composite of chart-level comparisons is a timeout; crossing it between isomorphisms, or
at an object, costs nothing.  This file is therefore stated at the **library square's** reading
throughout, and three devices put it there, all three load-bearing:

* the source and target of each comparison are named by an ascription, so that
  `CategoryTheory.Functor.map` and `CategoryTheory.CategoryStruct.comp` take that reading's
  objects rather than the ones `chartSourceIso`'s type supplies.  Without them the whole
  declaration is `maximum recursion depth has been reached`;
* the four `(X := …)` name the source of `AlgebraicGeometry.BigFppfOver.toScheme`'s image, which
  a type ascription cannot do.  Without them the inverse image of the Zariski cotangent sheaf is
  written at `ChartLiftPresentation.sub` in the statement and at `(SmallEtale.toOver … ).obj A` in
  the instantiation, the two have to be identified underneath
  `AlgebraicGeometry.Scheme.Modules.pullback` inside a module, and the elaborator computes the
  inverse image by sheafification instead — a `whnf` timeout at 200 000 heartbeats;
* the ambient space is written `(⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces … ).1` and not
  `Z.1.toFunctor`.  Those differ by one projection-of-a-constructor, and it is what the library
  square's instantiation has at twelve positions; with `Z.1.toFunctor` written instead the two
  differ at every `AlgebraicGeometry.SmallEtale` in an 8 600-token type and the match is again a
  `whnf` timeout at 200 000 heartbeats.

## Routes that do not work

* **Pasting the three constituent squares again here**, by
  `CategoryTheory.square_of_functor_factorizations_of_paste` with the two factorizations
  discharged by
  `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_hom_represented`.  That
  factorization's three factors are at *mixed* readings — its outer two at the chart's object of
  the site and its middle one at `ChartLiftPresentation.sub`, and its last factor is itself mixed,
  with `AlgebraicGeometry.Space.representedAssociatedModule` at the first spelling and the inverse
  image at the second — so no instantiation of the three constituent squares produces them: whichever
  reading the squares are pinned to, one of the two holes has to cross the junction inside a
  composite.  That is an `isDefEq` timeout which survives 1 000 000 heartbeats, with
  `CategoryTheory.Functor.leftAdjoint` and `structureSheaf` in its unfolding counts.
* **Rewriting the assembled square** with `chartSourceIso_eq`: `rw` is a `whnf` timeout at the
  second comparison and `simp only` is a kernel timeout, both because the rewrite has to abstract
  an occurrence whose *type* carries the reading.
* **Transporting the library's square across the comparison**, i.e. generalising it over the
  comparison isomorphism and instantiating: elaborates and then does not pass the kernel.  See
  the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartSourceFactorization`.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CS and 04CU are registered at the isomorphisms
composed here, and this is an interior step of [Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation.Restriction

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1} {P : ChartLiftPresentation C S hS p q a.hom U'}
  {V' : SmallEtale C S hS X'.1} (R : Restriction P V')

/-- **The source comparison at a presented chart is natural in the restriction.**  The inverse
image along the morphism of presented charts of
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` at the presentation, followed by
the comparison of [Stacks Project, Tag 03LU] and the Zariski comparison of the two pullback
cotangent sheaves, is the comparison of [Stacks Project, Tag 03LU] at the two charts followed by
the source comparison at the restricted presentation.

This is `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom_square_of_chartMap`
at the data the presentation and the restriction carry: the two charts of the source are the two
presented charts, the morphism between them is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subEtaleChartMap`, the two morphisms of
the site through which the chart composites factor are the reductions of the two presented lifts,
the factorization relating them is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMap_comp_redHom`, and the two chart
composites factor by `AlgebraicGeometry.Space.ChartLiftPresentation.subChart_comp`.

The source and target of each comparison are **named**, which is what puts the statement at the
chart-level reading of the chart space; see the section on the readings in the module docstring.
That is the only reason the two ascriptions are here, and removing either one restores the
timeout. -/
theorem chartSourceIso_hom_square
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    (modulePullback C S hS (schemeSpaceMap ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).map
              (R.subEtaleChartMap (Z := Z) (a := a))))).map
          ((chartSourceIso C S hS P hw hv).hom :
            (modulePullback C S hS
                (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
                    (P.subEtaleChart (Z := Z) (a := a)) :
                  schemeSpace ((SmallEtale.toOver C S hS
                    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                    (P.subEtaleChart (Z := Z) (a := a))) ⟶
                    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))).obj
              ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)) ⟶
            (representedAssociatedModule C S hS
                ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (P.subEtaleChart (Z := Z) (a := a)))
                (schemeSpace ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (P.subEtaleChart (Z := Z) (a := a)))).property).obj
              (Stacks.Smooth.pullbackCotangentSheaf
                ((BigFppfOver.toScheme C S hS).map P.chartHom)
                ((BigFppfOver.toScheme C S hS).map
                  (X := ((SmallEtale.toOver C S hS
                    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                    (P.subEtaleChart (Z := Z) (a := a))))
                  (P.incl ≫ P.liftHom)))) ≫
        ((representedAssociatedModulePullbackIso C S hS
                ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).map
                  (R.subEtaleChartMap (Z := Z) (a := a)))
                (relativelyRepresentable_yoneda_map C S hS
                  ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).map
                    (R.subEtaleChartMap (Z := Z) (a := a))))
                ((Scheme.Modules.pullback ((BigFppfOver.toScheme C S hS).map
                      (X := (SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                        (P.subEtaleChart (Z := Z) (a := a)))
                      (P.incl ≫ P.liftHom))).obj
                  (Stacks.Smooth.cotangentSheaf
                    ((BigFppfOver.toScheme C S hS).map P.chartHom)))).hom ≫
          (representedAssociatedModule C S hS
              ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                (R.presentation.subEtaleChart (Z := Z) (a := a)))
              (schemeSpace ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                (R.presentation.subEtaleChart (Z := Z) (a := a)))).property).map
            (Stacks.Smooth.pullbackCotangentCompHom
              ((BigFppfOver.toScheme C S hS).map P.chartHom)
              ((BigFppfOver.toScheme C S hS).map
                (X := (SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (P.subEtaleChart (Z := Z) (a := a))) (P.incl ≫ P.liftHom))
              ((BigFppfOver.toScheme C S hS).map
                ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).map
                  (R.subEtaleChartMap (Z := Z) (a := a))))
              ((BigFppfOver.toScheme C S hS).map
                (X := (SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (R.presentation.subEtaleChart (Z := Z) (a := a)))
                (R.presentation.incl ≫ R.presentation.liftHom))
              R.subMapScheme_comp_redHomScheme)) =
      ((modulePullbackCompIso C S hS
              (schemeSpaceMap ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).map
                (R.subEtaleChartMap (Z := Z) (a := a))))
              (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
                  (P.subEtaleChart (Z := Z) (a := a)) :
                schemeSpace ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                    (P.subEtaleChart (Z := Z) (a := a))) ⟶
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))).hom.app
            ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)) ≫
          eqToHom (congrArg
            (fun g : schemeSpace ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (R.presentation.subEtaleChart (Z := Z) (a := a))) ⟶
                (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) =>
              (modulePullback C S hS a ⋙ modulePullback C S hS g).obj
                (sheafOfDifferentials C S hS q))
            (schemeSpaceMap_toOver_comp_chartToSpace C S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
              (R.subEtaleChartMap (Z := Z) (a := a))))) ≫
        ((chartSourceIso C S hS R.presentation hw hv).hom :
            (modulePullback C S hS
                (chartToSpace C S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
                    (R.presentation.subEtaleChart (Z := Z) (a := a)) :
                  schemeSpace ((SmallEtale.toOver C S hS
                    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                    (R.presentation.subEtaleChart (Z := Z) (a := a))) ⟶
                    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))).obj
              ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q)) ⟶
            (representedAssociatedModule C S hS
                ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (R.presentation.subEtaleChart (Z := Z) (a := a)))
                (schemeSpace ((SmallEtale.toOver C S hS
                  (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                  (R.presentation.subEtaleChart (Z := Z) (a := a)))).property).obj
              (Stacks.Smooth.pullbackCotangentSheaf
                ((BigFppfOver.toScheme C S hS).map P.chartHom)
                ((BigFppfOver.toScheme C S hS).map
                  (X := ((SmallEtale.toOver C S hS
                    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS).1).obj
                    (R.presentation.subEtaleChart (Z := Z) (a := a))))
                  (R.presentation.incl ≫ R.presentation.liftHom)))) :=
  (congrArg ((modulePullback C S hS (schemeSpaceMap _)).map · ≫ _)
      (congrArg Iso.hom
          (((chartSourceIso_eq C S hS P hw hv).symm :
        chartDifferentialsAssociatedCotangentIso C S hS q a
          (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
          ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
          ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
          P.chartSq' (P.subEtaleChart (Z := Z) (a := a)) (P.incl ≫ P.liftHom)
          P.subChart_comp =
          chartSourceIso C S hS P hw hv))).symm).trans
    ((chartDifferentialsAssociatedCotangentIso_hom_square_of_chartMap C S hS q a
          (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
          ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
          ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
          P.chartSq' (P.subEtaleChart (Z := Z) (a := a))
          (R.presentation.subEtaleChart (Z := Z) (a := a))
          (R.subEtaleChartMap (Z := Z) (a := a))
          (P.incl ≫ P.liftHom) (R.presentation.incl ≫ R.presentation.liftHom)
          R.subMap_comp_redHom P.subChart_comp R.presentation.subChart_comp).trans
      (congrArg (_ ≫ ·)
        (congrArg Iso.hom
          (((chartSourceIso_eq C S hS R.presentation hw hv).symm :
        chartDifferentialsAssociatedCotangentIso C S hS q a
          (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
          ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
          ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
          P.chartSq' (R.presentation.subEtaleChart (Z := Z) (a := a))
          (R.presentation.incl ≫ R.presentation.liftHom)
          R.presentation.subChart_comp =
          chartSourceIso C S hS R.presentation hw hv)))))

end ChartLiftPresentation.Restriction

end AlgebraicGeometry.Space

end
