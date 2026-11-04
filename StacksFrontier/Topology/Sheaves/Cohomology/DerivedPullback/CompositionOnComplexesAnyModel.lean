module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes

/-!
# Derived pullback on complexes and composition, over an arbitrary model

`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/CompositionOnComplexes.lean` states the
comparison of [Stacks, Tag 06YJ] at a cochain complex and its compatibility with composition at
the model `CategoryTheory.HasDerivedCategory.standard`. This file restates them with the model of
each derived category quantified over, so that they apply at the locally small model as well.

## Main definitions

* `Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_general`: the
  comparison of Tag 06YJ at a cochain complex, at an arbitrary model.

## Main results

* `Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp_general`: its
  compatibility with composition.
* `AlgebraicGeometry.pullbackComparisonOnComplex_eq_general`: for a morphism of schemes the
  comparison is the ringed-space one.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-! ### The same comparisons over an arbitrary model of the derived category

The statements above are read at `CategoryTheory.HasDerivedCategory.standard`. A consumer that
computes a derived pullback at another model -- the locally small one of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, say -- cannot use them, because the model is
part of their types. The declarations below are the same comparisons with the model quantified
over, so that they say something at every model; their proofs are those above, elaborated against
the quantified instances. -/

namespace Stacks.DerivedPullback.Composition

universe u wX wY wZ

variable {X Y Z : RingedSpace.{u, u}}
  [HasDerivedCategory.{wX} (ModuleSheaves X)] [HasDerivedCategory.{wY} (ModuleSheaves Y)]
  [HasDerivedCategory.{wZ} (ModuleSheaves Z)]

/-- **The comparison of Tag 06YJ at a cochain complex**, for a morphism of ringed spaces: the
derived pullback of `Q P` maps to `Q` of the degreewise pullback of `P`.

The comparison itself lives on the homotopy category, so the map is the derived pullback of the
identification `DerivedCategory.quotientCompQhIso`, then the comparison at the quotient of `P`,
then the factorization of degreewise pullback through the quotient, then that identification
again.  For a morphism of schemes this is `AlgebraicGeometry.pullbackComparisonOnComplex`, by
`AlgebraicGeometry.pullbackComparisonOnComplex_eq_general`. -/
def derivedPullbackComparisonOnComplex_general (f : X ⟶ Y)
    (P : CochainComplex (ModuleSheaves Y) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (derivedPullback f).map ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).inv.app P) ≫
    (derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

variable (f : X ⟶ Y) (g : Y ⟶ Z)

open Stacks.Cohomology.DerivedPushforwardComposition in
/-- **The composition formula of Tag 0D5S, on a complex.**  The comparison
`Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`, followed by the comparison on complexes for `f ≫ g`, is the derived
pullback along `f` of the comparison on complexes for `g`, then the comparison on complexes for
`f`, then the degreewise pullback-composition isomorphism of
`Stacks.DerivedPullback.Composition.modulePullbackComp`.

This is the compatibility of the composition formula with
`AlgebraicGeometry.pullbackComparisonOnComplex` that the derived stalk of an iterated derived
pullback needs.  The proof is
`derivedPullbackCompIsoCanonical_hom_app_comp_comparison_general` carried from the homotopy
category onto complexes: one naturality square for the comparison of Tag 0D5S,
one for the comparison of Tag 06YJ along `f`, one for `DerivedCategory.quotientCompQhIso`, the
cancellation of the derived pullback of `DerivedCategory.quotientCompQhIso` against its inverse,
and `Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso_hom_app_comp_factors` carried to
the derived category, which holds at every model because it is a statement about homotopy
categories. -/
theorem derivedPullbackComparisonOnComplex_comp_general (P : CochainComplex (ModuleSheaves Z) ℤ) :
    (derivedPullbackCompComparisonCanonical f g).app (DerivedCategory.Q.obj P) ≫
        derivedPullbackComparisonOnComplex_general (f ≫ g) P =
      (derivedPullback f).map (derivedPullbackComparisonOnComplex_general g P) ≫
        derivedPullbackComparisonOnComplex_general f
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
            (ComplexShape.up ℤ)).hom.app P) := by
  have hQh : DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (((modulePullback (f ≫ g)).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P) =
      DerivedCategory.Qh.map
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P)) ≫
        DerivedCategory.Qh.map
            (((modulePullback f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
              (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
                (ComplexShape.up ℤ)).hom.app P)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp]
    exact congrArg DerivedCategory.Qh.map (pullbackOnHomotopyCompIso_hom_app_comp_factors f g P)
  have hcancel : ∀ {T : DerivedCategory (ModuleSheaves X)}
      (h : (derivedPullback f).obj
        ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).obj
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ⟶ T),
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).hom.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).inv.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫ h = h :=
    fun h => Iso.hom_inv_id_assoc ((derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).app
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) h
  have hfac : (derivedPullbackCompComparisonCanonical f g).app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackComparison (f ≫ g)).app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P) =
      (derivedPullback f).map ((derivedPullbackComparison g).app
          ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app
            ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) :=
    derivedPullbackCompIsoCanonical_hom_app_comp_comparison_general f g _
  have hnatf : (derivedPullback f).map (DerivedCategory.Qh.map
          (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ)).obj
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (derivedPullbackComparison f).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
            (((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app P)) :=
    (derivedPullbackComparison f).naturality _
  have hnatA : (derivedPullback f).map ((derivedPullback g).map
          ((DerivedCategory.quotientCompQhIso (ModuleSheaves Z)).inv.app P)) ≫
        (derivedPullbackCompComparisonCanonical f g).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleSheaves Z) (ComplexShape.up ℤ)).obj P)) =
      (derivedPullbackCompComparisonCanonical f g).app (DerivedCategory.Q.obj P) ≫
        (derivedPullback (f ≫ g)).map
          ((DerivedCategory.quotientCompQhIso (ModuleSheaves Z)).inv.app P) :=
    (derivedPullbackCompComparisonCanonical f g).naturality _
  have hnatQ : DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
              (ComplexShape.up ℤ)).hom.app P)) ≫
        (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
          (((modulePullback (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
          (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
          (ComplexShape.up ℤ)).hom.app P) :=
    (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.naturality _
  unfold derivedPullbackComparisonOnComplex_general
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  conv_rhs => rw [hcancel,
    reassoc_of% hnatf, ← hnatQ]
  conv_lhs => rw [← reassoc_of% hnatA, reassoc_of% hfac,
    reassoc_of% hQh]

end Stacks.DerivedPullback.Composition

namespace AlgebraicGeometry

universe u w

attribute [local instance] hasDerivedCategory_ringedSpaceModules

variable {X Y Z : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]
  [HasDerivedCategory.{w} Y.Modules] [HasDerivedCategory.{w} Z.Modules]
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The scheme-level comparison on a complex is the ringed-space one.**  Both sides are the same
composite: the scheme spelling of the category of modules and the ringed-space spelling are
definitionally equal, and `AlgebraicGeometry.Scheme.Modules.pullback` is degreewise pullback along
the underlying morphism of ringed spaces. -/
theorem pullbackComparisonOnComplex_eq_general (P : CochainComplex Y.Modules ℤ) :
    pullbackComparisonOnComplex f P =
      Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_general
        f.toLRSHom.toShHom P :=
  rfl

end AlgebraicGeometry

end
