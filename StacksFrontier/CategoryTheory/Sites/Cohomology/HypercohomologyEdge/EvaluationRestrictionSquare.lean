module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestriction

/-!
# Restriction in the object of the site, against the evaluation isomorphism of Tag 0A94

Let `(C, O)` be a ringed site and `g : U' ⟶ U` a morphism of `C`.  The naturality in the object of
the site of `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` — the identification of
the value at `U` of the degree-`q` cohomology presheaf with the hypercohomology `H^q(U, K)` — is
one of the two halves of the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso`, hence an input of
`Stacks.Cohomology.UnboundedHigherDirectImage.derivedPreimageHomPresheafValueEquiv`, hence of the
uniqueness clause of [Stacks, Tag 0D68].

The square was recorded object by object.  This file reduces it to the corresponding equation of
*natural transformations*, where both sides are transformations out of
`derivedSectionsPresheaf O ⋙ H^q ⋙ evaluation U`, and that functor is a right derived functor of
`homotopySectionsPresheaf O ⋙ H^q ⋙ evaluation U` with unit
`Stacks.Cohomology.HypercohomologyEdge.totalRightDerivedCompUnit`, by
`Stacks.Cohomology.HypercohomologyEdge.isRightDerivedFunctor_totalRightDerived_comp`.  So the
universal property applies directly and the square reduces to an equation on the homotopy
category, where both the restriction map of the presheaf and the evaluation of a complex of
sections are termwise.  That is the route
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` is itself built by.

Neither statement here closes the square; what they do is fix its shape and identify the right
derived functor it is to be tested against.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_natTrans_of_unit`: the
  transformation form of the square follows from the corresponding equation after composition with
  the unit, that is from an equation on the homotopy category.  This is the residual.
* `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_of_natTrans`: the
  object-wise square, in the shape its consumer needs, follows from the transformation form.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.SiteCohomologyPresheaf

attribute [local instance] restrictScalars_preservesFiniteLimits
  restrictScalars_preservesFiniteColimits evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-- **The evaluation restriction square, tested against the unit.** Both sides of the square are
transformations out of `derivedSectionsPresheaf O ⋙ H^q ⋙ evaluation U`, which is a right derived
functor with unit `Stacks.Cohomology.HypercohomologyEdge.totalRightDerivedCompUnit` by
`Stacks.Cohomology.HypercohomologyEdge.isRightDerivedFunctor_totalRightDerived_comp`; so they
agree as soon as they agree after composition with that unit, which is an equation on the homotopy
category.

This is the step that identifies which right derived functor the square is to be tested against.
The hypothesis is not discharged here, and it is the residual of this half of the square. -/
theorem sectionsEvaluationIso_restrict_natTrans_of_unit {U U' : C} (g : U' ⟶ U) (q : ℤ)
    (hu : totalRightDerivedCompUnit (homotopySectionsPresheaf O)
          (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
            PresheafOfModules.evaluation O.obj (.op U)) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          ((sectionsEvaluationIso O U q).hom ≫ derivedSectionsRestrictHomology O g q) =
      totalRightDerivedCompUnit (homotopySectionsPresheaf O)
          (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
            PresheafOfModules.evaluation O.obj (.op U)) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
              DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
            (PresheafOfModules.restriction O.obj g.op) ≫
            Functor.whiskerRight (sectionsEvaluationIso O U' q).hom
              (ModuleCat.restrictScalars (O.obj.map g.op).hom))) :
    (sectionsEvaluationIso O U q).hom ≫ derivedSectionsRestrictHomology O g q =
      Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
        (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (sectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) := by
  have := isRightDerivedFunctor_totalRightDerived_comp (homotopySectionsPresheaf O)
    (DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⋙
      PresheafOfModules.evaluation O.obj (.op U))
  exact Functor.rightDerived_ext _ _
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) _ _ _ hu

/-- **The object-wise evaluation restriction square follows from its transformation form.** The
restriction map on the left-hand presheaf is semilinear, so the two factors of that side do not
compose over `O(U)`: it is written with `CategoryTheory.PresheafOfModules.restriction` and the
second factor read through restriction of scalars.  Stated as a transformation that is a single
`Functor.whiskerLeft`, and the object-wise form is its component.

The hypothesis is not discharged here. -/
theorem sectionsEvaluationIso_restrict_of_natTrans {U U' : C} (g : U' ⟶ U) (q : ℤ)
    (h : (sectionsEvaluationIso O U q).hom ≫ derivedSectionsRestrictHomology O g q =
      Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
        (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (sectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom))
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (sectionsEvaluationIso O U q).hom.app K ≫ (derivedSectionsRestrictHomology O g q).app K =
      (PresheafOfModules.restriction O.obj g.op).app
          ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
            ((derivedSectionsPresheaf O).obj K)) ≫
        (ModuleCat.restrictScalars (O.obj.map g.op).hom).map
          ((sectionsEvaluationIso O U' q).hom.app K) :=
  NatTrans.congr_app h K

end Stacks.Cohomology.HypercohomologyEdge

end
