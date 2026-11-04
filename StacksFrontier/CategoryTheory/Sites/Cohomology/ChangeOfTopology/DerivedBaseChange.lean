module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
import StacksCore.Tactic.StacksAttribute

/-!
# The derived base change map for a change of topology

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3, write
`ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology morphism, and let `f : X ⟶ Y` be a morphism
of `C`. On abelian sheaves the direct images satisfy the strict identity
`ε_{X,*} ⋙ f_{τ',*} = f_{τ,*} ⋙ ε_{Y,*}` of Stacks 0EZ2, and the mate of that identity under
the two change-of-topology adjunctions is a natural map

`ε_Y^{-1} ∘ f_{τ',*} ⟶ f_{τ,*} ∘ ε_X^{-1}`

of inverse images. This file constructs that map, `abelianComparisonBaseChange`, and its
canonical extension `derivedComparisonBaseChange` to bounded below derived categories, which is
characterized by a factorization through the unit of right derivation. It also constructs the
canonical map `K' ⟶ Rε_{X,*}(ε_X^{-1} K')` on bounded below derived categories,
`derivedComparisonUnit`.

## Main definitions

* `Stacks.ComparingTopologies.abelianComparisonBaseChange`: the mate of the square of direct
  images, a map of inverse images.
* `Stacks.ComparingTopologies.derivedComparisonBaseChangeOnHomotopy`: the same map applied
  degreewise and composed with the units of right derivation.
* `Stacks.ComparingTopologies.derivedComparisonBaseChange`: the canonical derived base change
  map `ε_Y^{-1} Rf_{τ',*} ⟶ Rf_{τ,*} ε_X^{-1}` on bounded below derived categories.
* `Stacks.ComparingTopologies.abelianComparisonHomotopyUnit` and
  `Stacks.ComparingTopologies.derivedComparisonUnit`: the change-of-topology adjunction unit on
  bounded below homotopy categories, and the canonical map it descends to on bounded below
  derived categories.

## Main results

* `Stacks.ComparingTopologies.isIso_abelianComparisonPullback_rightDerivedFunctorPlusUnit`:
  the unit of right derivation of the exact functor `ε_X^{-1}` is an isomorphism.
* `Stacks.ComparingTopologies.derivedComparisonBaseChange_fac` and
  `Stacks.ComparingTopologies.eq_derivedComparisonBaseChange_of_fac`: the defining equation of
  the derived base change map, and the uniqueness it gives.
* `Stacks.ComparingTopologies.derivedComparisonUnit_fac`: the defining equation of the derived
  unit.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZ2](https://stacks.math.columbia.edu/tag/0EZ2)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

/-- The unit of right derivation of the change-of-topology inverse image `ε_X^{-1}` on bounded
below homotopy categories is an isomorphism. -/
instance isIso_abelianComparisonPullback_rightDerivedFunctorPlusUnit
    (S : CohomologyComparison C) (X : C) :
    IsIso (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).rightDerivedFunctorPlusUnit := by
  have := (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine X).isLeftAdjoint
  exact Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology _

/-- **The mate of the square of topoi of Stacks 0EZ2 on abelian sheaves.** The natural map
`ε_Y^{-1} ∘ f_{τ',*} ⟶ f_{τ,*} ∘ ε_X^{-1}` of inverse images obtained from the strict identity
`ε_{X,*} ∘ f_{τ',*} = f_{τ,*} ∘ ε_{Y,*}` of direct images by the two change-of-topology
adjunctions. -/
def abelianComparisonBaseChange (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    overPushforward S.coarseCoverage.toGrothendieck f ⋙
        abelianComparisonPullback S.fineCoverage S.coarseCoverage Y ⟶
      abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
        overPushforward S.fineCoverage.toGrothendieck f :=
  Functor.whiskerRight
      (Functor.whiskerRight (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).unit
        (overPushforward S.coarseCoverage.toGrothendieck f))
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y) ≫
    Functor.whiskerLeft (abelianComparisonPullback S.fineCoverage S.coarseCoverage X)
      (Functor.whiskerLeft (overPushforward S.fineCoverage.toGrothendieck f)
        (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).counit)

/-- The mate is adjoint to the coarse direct image of the change-of-topology unit at the
source. -/
theorem abelianComparisonBaseChange_homEquiv (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}) :
    (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
        S.coarse_le_fine Y).homEquiv _ _ ((abelianComparisonBaseChange S f).app F) =
      (overPushforward S.coarseCoverage.toGrothendieck f).map
        ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).unit.app F) :=
  (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine Y).homEquiv _ _ |>.apply_symm_apply _

/-- The mate applied degreewise on bounded below homotopy categories and composed with the
units of right derivation, the (invertible) unit for `ε_Y^{-1}` being inverted. -/
def derivedComparisonBaseChangeOnHomotopy (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    (overPushforward S.coarseCoverage.toGrothendieck f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ (abelianComparisonPullback S.fineCoverage
          S.coarseCoverage Y).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage
          X).rightDerivedFunctorPlus ⋙
        (overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlus :=
  let Fc := overPushforward S.coarseCoverage.toGrothendieck f
  let Ff := overPushforward S.fineCoverage.toGrothendieck f
  let EX := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let EY := abelianComparisonPullback S.fineCoverage S.coarseCoverage Y
  Functor.whiskerLeft Fc.mapHomotopyCategoryPlus (inv EY.rightDerivedFunctorPlusUnit) ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (Fc ⋙ EY))).hom
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusNatTrans (abelianComparisonBaseChange S f))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (EX ⋙ Ff))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft EX.mapHomotopyCategoryPlus Ff.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight EX.rightDerivedFunctorPlusUnit Ff.rightDerivedFunctorPlus

/-- **The canonical derived base change map for a change of topology,**
`ε_Y^{-1} Rf_{τ',*} ⟶ Rf_{τ,*} ε_X^{-1}` on bounded below derived categories: the unique
transformation which, precomposed with the unit of right derivation of `f_{τ',*}`, is
`derivedComparisonBaseChangeOnHomotopy`. -/
def derivedComparisonBaseChange (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus ⋙
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).rightDerivedFunctorPlus ⟶
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).rightDerivedFunctorPlus ⋙
        (overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc
    ((overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus ⋙
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight
      (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlusUnit
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    _ (derivedComparisonBaseChangeOnHomotopy S f)

/-- The equation defining the canonical derived base change map. -/
theorem derivedComparisonBaseChange_fac (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    Functor.whiskerRight
        (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlusUnit
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).rightDerivedFunctorPlus ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (derivedComparisonBaseChange S f) =
        derivedComparisonBaseChangeOnHomotopy S f :=
  Functor.rightDerived_fac
    ((overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus ⋙
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight
      (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlusUnit
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    _ (derivedComparisonBaseChangeOnHomotopy S f)

/-- A transformation satisfying the defining equation *is* the canonical derived base change
map. -/
theorem eq_derivedComparisonBaseChange_of_fac (S : CohomologyComparison C) {X Y : C}
    (f : X ⟶ Y)
    (τ : (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlus ⋙
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).rightDerivedFunctorPlus ⟶
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).rightDerivedFunctorPlus ⋙
        (overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlus)
    (hτ : Functor.whiskerRight
        (overPushforward S.coarseCoverage.toGrothendieck f).rightDerivedFunctorPlusUnit
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage
          Y).rightDerivedFunctorPlus ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh τ =
        derivedComparisonBaseChangeOnHomotopy S f) :
    τ = derivedComparisonBaseChange S f :=
  Functor.rightDerived_ext _ _
    (HomotopyCategory.Plus.quasiIso (AbelianSheaves S.coarseCoverage.toGrothendieck X)) _ _ _
    (hτ.trans (derivedComparisonBaseChange_fac S f).symm)

/-- The unit of the change-of-topology adjunction, applied degreewise on bounded below
homotopy categories. -/
def abelianComparisonHomotopyUnit (S : CohomologyComparison C) (X : C) :
    (𝟭 (AbelianSheaves S.coarseCoverage.toGrothendieck X)).mapHomotopyCategoryPlus ⟶
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
        abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk
    ((NatTrans.mapHomotopyCategory (abelianComparisonAdjunction S.fineCoverage
      S.coarseCoverage S.coarse_le_fine X).unit (ComplexShape.up ℤ)).app K.obj)
  naturality := by
    intro K L f
    ext
    exact (NatTrans.mapHomotopyCategory (abelianComparisonAdjunction S.fineCoverage
      S.coarseCoverage S.coarse_le_fine X).unit (ComplexShape.up ℤ)).naturality f.hom

/-- **The canonical map `K' ⟶ Rε_{X,*}(ε_X^{-1} K')` on bounded below derived categories**:
the transformation whose restriction along the localization functor is the ordinary adjunction
unit followed by the unit of right derivation of `ε_{X,*}` and the degreewise description of the
action of the exact functor `ε_X^{-1}`. -/
def derivedComparisonUnit (S : CohomologyComparison C) (X : C) :
    𝟭 (DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X)) ⟶
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapDerivedCategoryPlus ⋙
        (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).rightDerivedFunctorPlus :=
  let A := AbelianSheaves S.coarseCoverage.toGrothendieck X
  let L := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let R := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A) _).preimage
      (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdComparison A)
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (abelianComparisonHomotopyUnit S X) DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ R))).inv
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus)

/-- After restriction along the localization functor, the derived unit is the ordinary
adjunction unit followed by the unit of right derivation and the degreewise description of the
action of the exact functor `ε_X^{-1}`. -/
theorem derivedComparisonUnit_fac (S : CohomologyComparison C) (X : C) :
    Functor.whiskerLeft DerivedCategory.Plus.Qh (derivedComparisonUnit S X) =
      (let A := AbelianSheaves S.coarseCoverage.toGrothendieck X
      let L := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
      let R := abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X
      Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdComparison A)
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (abelianComparisonHomotopyUnit S X) DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ R))).inv
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerLeft L.mapHomotopyCategoryPlus R.rightDerivedFunctorPlusUnit ≫
        Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv R.rightDerivedFunctorPlus) :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso
      (AbelianSheaves S.coarseCoverage.toGrothendieck X)) _).map_preimage _

end Stacks.ComparingTopologies
