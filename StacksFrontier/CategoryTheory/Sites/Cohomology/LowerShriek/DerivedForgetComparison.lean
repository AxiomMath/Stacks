module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ForgetComparison

/-!
# The comparison transformation of Stacks 07AE, as a named map

`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ForgetComparison.lean` shows that there
is exactly one natural transformation `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` compatible with the
counits of the two left derived functors and the comparison of Stacks 0798. This file names that
transformation, so that later statements (the canonical maps at the generators `j_{U!}O_U` of
the criterion of Stacks 07AE) can be phrased in terms of its components.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.derivedForgetComparison`: the comparison
  `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.derivedForgetComparison_fac`: its compatibility with the
  two counits.
* `Stacks.Cohomology.DerivedLowerShriek.derivedForgetComparison_uniq`: that compatibility
  determines it.

## References

* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] (O : Sheaf K RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}]
  [(_root_.SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

attribute [local instance] HasDerivedCategory.standard

variable [((lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))]
  [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (sourceQuasiIso J K f O)]
  [(derivedLowerShriek J K f O ⋙
    (forgetTargetModules K O).mapDerivedCategory).IsLeftDerivedFunctor
      (derivedLowerShriekForgetCounit J K f O) (sourceQuasiIso J K f O)]

/-- The comparison transformation `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` of Stacks 07AE: the
transformation obtained from `derivedForgetComparisonCounit` by the universal property of
`Lg_! ⋙ forget` as a left derived functor. `derivedForgetComparison_fac` is the compatibility
with the two counits, and `derivedForgetComparison_uniq` says that compatibility pins it down. -/
def derivedForgetComparison :
    (forgetSourceModules J K f O).mapDerivedCategory ⋙ derivedLowerShriekAbelian J K f ⟶
      derivedLowerShriek J K f O ⋙ (forgetTargetModules K O).mapDerivedCategory :=
  Functor.leftDerivedLift _ (derivedLowerShriekForgetCounit J K f O)
    (sourceQuasiIso J K f O) _ (derivedForgetComparisonCounit J K f O)

/-- The comparison of Stacks 07AE is compatible with the counit exhibiting `Lg_! ⋙ forget` as a
left derived functor and with the transformation `derivedForgetComparisonCounit` assembled from
the counit of `Lg_!^{Ab}` and the comparison of Stacks 0798. -/
@[reassoc]
lemma derivedForgetComparison_fac :
    Functor.whiskerLeft DerivedCategory.Qh (derivedForgetComparison J K f O) ≫
        derivedLowerShriekForgetCounit J K f O =
      derivedForgetComparisonCounit J K f O :=
  Functor.leftDerived_fac _ _ _ _ _

/-- The compatibility of `derivedForgetComparison_fac` determines the comparison of Stacks 07AE
uniquely, a left derived functor being a right Kan extension along the localization. -/
lemma derivedForgetComparison_uniq
    (t : (forgetSourceModules J K f O).mapDerivedCategory ⋙ derivedLowerShriekAbelian J K f ⟶
      derivedLowerShriek J K f O ⋙ (forgetTargetModules K O).mapDerivedCategory)
    (ht : Functor.whiskerLeft DerivedCategory.Qh t ≫ derivedLowerShriekForgetCounit J K f O =
      derivedForgetComparisonCounit J K f O) :
    t = derivedForgetComparison J K f O :=
  Functor.leftDerived_ext _ (derivedLowerShriekForgetCounit J K f O)
    (sourceQuasiIso J K f O) _ _ _ (by rw [ht, derivedForgetComparison_fac])

end Stacks.Cohomology.DerivedLowerShriek

end
