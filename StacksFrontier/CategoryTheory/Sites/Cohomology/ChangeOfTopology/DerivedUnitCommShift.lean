module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The derived change-of-topology unit commutes with the shift

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3 and write
`ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology morphism. The canonical map
`K' ⟶ Rε_{X,*}(ε_X^{-1} K')` on bounded below derived categories,
`Stacks.ComparingTopologies.derivedComparisonUnit`, is produced by the universal property of
the localization functor `DerivedCategory.Plus.Qh` and therefore has no componentwise formula.
This file shows that it nevertheless commutes with the shift by `ℤ`, which is what allows a
statement about it to be moved between degrees — the step `(V_n) ⇒ (V_{n+1})` of Stacks 0EZE
applies the map to a shifted sheaf, and the induction of Stacks 0EZB compares its effect on
cohomology sheaves in neighbouring degrees.

## Main results

* `Stacks.ComparingTopologies.commShift_derivedComparisonUnit`: the derived unit commutes with
  the shift by `ℤ`.

## Implementation notes

The commutation is tested after restriction along `DerivedCategory.Plus.Qh`, which is
essentially surjective and commutes with the shift
(`CategoryTheory.NatTrans.commShift_of_whiskerLeft`), and there the defining equation
`Stacks.ComparingTopologies.derivedComparisonUnit_fac` expresses the restriction as a composite
of five transformations, each shift-compatible for a reason of its own:

* the comparison of the identity functor of the bounded below homotopy category with the functor
  induced by the identity, and the comparison of a composite with the functor induced by the
  composite, by `CategoryTheory.commShift_mapHomotopyCategoryPlusIdComparison` and
  `CategoryTheory.commShift_mapHomotopyCategoryPlusCompIso`;
* the degreewise change-of-topology unit, which *is* the transformation induced on bounded below
  homotopy categories by the underived unit, by
  `CategoryTheory.commShift_mapHomotopyCategoryPlusNatTrans`;
* the unit of right derivation of `ε_{X,*}`, by
  `Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit`;
* the degreewise description of the action of the exact functor `ε_X^{-1}` on bounded below
  derived categories, which is a lifting along a localization, by Mathlib's
  `CategoryTheory.NatTrans.commShift_iso_hom_of_localization`.

The last of these needs the commutation of `(ε_X^{-1})_{D^+}` itself with the shift, which is
not an instance: it is produced here, as `commShiftMapDerivedCategoryPlus`, from
`CategoryTheory.Functor.commShiftOfLocalization` applied to the lifting instance
`CategoryTheory.Functor.mapDerivedCategoryPlusLifting`.

The five transformations do not compose on the nose: their sources and targets are the same
functors written with different bracketings and with the identity functor inserted on different
sides. The proof therefore writes out the composite *with* the intervening associators and
unitors — each of which is shift-compatible — and identifies it with the restriction of the
derived unit by `CategoryTheory.NatTrans.commShift_of_eq`. The resulting equation has identity
components wherever an associator or a unitor occurs, and is discharged by `Category.id_comp`,
`Category.comp_id` and `CategoryTheory.Category.whisker_eq` applied as terms: the object
arguments of those identities are produced by the comparison isomorphisms in a spelling which is
only definitionally the source and target of the morphism between them, so neither `rw` nor
`simp` has anything to match on.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit

/-- **The action of the exact functor `ε_X^{-1}` on bounded below derived categories commutes
with the shift.** It is a lifting along the localization functor of the degreewise action, which
commutes with the shift, so the commutation is transported by
`CategoryTheory.Functor.commShiftOfLocalization`. This is not an instance in Mathlib and has to
be supplied by hand wherever the functor is used. -/
@[instance_reducible]
def commShiftMapDerivedCategoryPlus (S : CohomologyComparison C) (X : C) :
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus.CommShift
      ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X)) ℤ
    ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus

attribute [local instance] commShiftMapDerivedCategoryPlus

/-- **The degreewise description of the action of `ε_X^{-1}` on bounded below derived categories
is compatible with the shift**, for the commutation of `commShiftMapDerivedCategoryPlus`. -/
theorem commShiftMapDerivedCategoryPlusFactorsh (S : CohomologyComparison C) (X : C) :
    NatTrans.CommShift (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapDerivedCategoryPlusFactorsh.hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X)) ℤ
    ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus

attribute [local instance] commShiftMapDerivedCategoryPlusFactorsh

/-- The degreewise change-of-topology unit on bounded below homotopy categories *is* the
transformation induced there by the underived unit; the two definitions agree on the nose. -/
theorem abelianComparisonHomotopyUnit_eq (S : CohomologyComparison C) (X : C) :
    abelianComparisonHomotopyUnit S X =
      Functor.mapHomotopyCategoryPlusNatTrans (abelianComparisonAdjunction S.fineCoverage
        S.coarseCoverage S.coarse_le_fine X).unit :=
  rfl

/-- **The degreewise change-of-topology unit commutes with the shift**, being the transformation
induced on bounded below homotopy categories by an additive natural transformation. -/
instance commShift_abelianComparisonHomotopyUnit (S : CohomologyComparison C) (X : C) :
    NatTrans.CommShift (abelianComparisonHomotopyUnit S X) ℤ :=
  NatTrans.commShift_of_eq (abelianComparisonHomotopyUnit_eq S X)

/-- **The canonical map `K' ⟶ Rε_{X,*}(ε_X^{-1} K')` on bounded below derived categories
commutes with the shift by `ℤ`.** The equation is tested after restriction along the
localization functor onto the bounded below derived category, where the map is the composite of
the five shift-compatible transformations of
`Stacks.ComparingTopologies.derivedComparisonUnit_fac`. -/
instance commShift_derivedComparisonUnit (S : CohomologyComparison C) (X : C) :
    NatTrans.CommShift (derivedComparisonUnit S X) ℤ := by
  refine NatTrans.commShift_of_whiskerLeft DerivedCategory.Plus.Qh _ ?_
  set A := AbelianSheaves S.coarseCoverage.toGrothendieck X
  set L := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  set R := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  refine NatTrans.commShift_of_eq (θ :=
    (Functor.rightUnitor DerivedCategory.Plus.Qh).hom ≫
    (Functor.leftUnitor DerivedCategory.Plus.Qh).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdComparison A)
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (abelianComparisonHomotopyUnit S X) DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ R))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator L.mapHomotopyCategoryPlus R.mapHomotopyCategoryPlus
      DerivedCategory.Plus.Qh).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit ≫
    (Functor.associator L.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh
      R.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus ≫
    (Functor.associator DerivedCategory.Plus.Qh L.mapDerivedCategoryPlus
      R.rightDerivedFunctorPlus).hom) ?_
  rw [derivedComparisonUnit_fac]
  ext K
  exact ((Category.id_comp _).trans ((Category.id_comp _).trans
    (_ ≫= (_ ≫= (_ ≫= ((Category.id_comp _).trans
      (_ ≫= ((Category.id_comp _).trans (Category.comp_id _))))))))).symm

end Stacks.ComparingTopologies

end
