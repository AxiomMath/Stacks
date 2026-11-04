module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedSquareCommutes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-! # Cohomology is computed after the derived change-of-topology direct image

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3 and let `X` be
an object of `C`. Global sections over the localized sites satisfy the strict identity
`Γ_{τ'}(X, ε_{X,*} F) = Γ_τ(X, F)`, because the change-of-topology direct image does not alter
the underlying presheaf of a sheaf; it only remembers a weaker sheaf condition.

This file proves the derived form of that identity,

`RΓ_{τ'}(X, -) ∘ Rε_{X,*} = RΓ_τ(X, -)`

as functors `D(Ab(C_τ/X)) ⥤ D(Ab)`, an instance of Stacks 0D6H for abelian sheaves.

## Main results

* `Stacks.ComparingTopologies.derivedGlobalSectionsComparisonIso`:
  `Rε_{X,*} ⋙ RΓ_{τ'}(X, -) ≅ RΓ_τ(X, -)`.
* `Stacks.ComparingTopologies.derivedGlobalSectionsComparisonPlusIso`: the same isomorphism with
  the bounded below derived categories and the right derived functors of
  `CategoryTheory.Functor.rightDerivedFunctorPlus` in all three slots.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

universe v u w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- Global sections over the terminal object of the coarser localized site, precomposed with the
change-of-topology direct image, *are* global sections over the terminal object of the finer
localized site. -/
theorem abelianComparisonPushforward_comp_globalSectionsOver (S : CohomologyComparison C)
    (X : C) :
    abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        globalSectionsOver S.coarseCoverage.toGrothendieck X =
      globalSectionsOver S.fineCoverage.toGrothendieck X :=
  rfl

/-- Cohomology on the finer localized site over `X` is computed by the derived change-of-topology
direct image followed by cohomology on the coarser localized site, for arbitrary right derived
functors `Rε_{X,*}`, `RΓ_{τ'}(X, -)` and `RΓ_τ(X, -)` with their units. -/
def derivedGlobalSectionsComparisonIso (S : CohomologyComparison C) (X : C)
    [HasDerivedCategory.{w₁} (AbelianSheaves S.fineCoverage.toGrothendieck X)]
    [HasDerivedCategory.{w₂} (AbelianSheaves S.coarseCoverage.toGrothendieck X)]
    [HasDerivedCategory.{w₃} Ab.{max u v}]
    (RεX : DerivedCategory (AbelianSheaves S.fineCoverage.toGrothendieck X) ⥤
      DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (RΓcoarse : DerivedCategory (AbelianSheaves S.coarseCoverage.toGrothendieck X) ⥤
      DerivedCategory Ab.{max u v})
    (RΓfine : DerivedCategory (AbelianSheaves S.fineCoverage.toGrothendieck X) ⥤
      DerivedCategory Ab.{max u v})
    (αεX : homotopyToDerived (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X) ⟶ DerivedCategory.Qh ⋙ RεX)
    (αΓcoarse : homotopyToDerived (globalSectionsOver S.coarseCoverage.toGrothendieck X) ⟶
      DerivedCategory.Qh ⋙ RΓcoarse)
    (αΓfine : homotopyToDerived (globalSectionsOver S.fineCoverage.toGrothendieck X) ⟶
      DerivedCategory.Qh ⋙ RΓfine)
    [RεX.IsRightDerivedFunctor αεX (HomotopyCategory.quasiIso
      (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ))]
    [RΓcoarse.IsRightDerivedFunctor αΓcoarse (HomotopyCategory.quasiIso
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) (ComplexShape.up ℤ))]
    [RΓfine.IsRightDerivedFunctor αΓfine (HomotopyCategory.quasiIso
      (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ))] :
    RεX ⋙ RΓcoarse ≅ RΓfine := by
  let εX := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let Γcoarse := globalSectionsOver S.coarseCoverage.toGrothendieck X
  let W := HomotopyCategory.quasiIso
    (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)
  let _ : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves S.fineCoverage.toGrothendieck X) :=
    sheaf_isGrothendieckAbelian (S.fineCoverage.toGrothendieck.over X)
  let _ : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) :=
    sheaf_isGrothendieckAbelian (S.coarseCoverage.toGrothendieck.over X)
  let αleft := derivedCompositeUnit εX Γcoarse RεX RΓcoarse αεX αΓcoarse
  have hleft : (RεX ⋙ RΓcoarse).IsRightDerivedFunctor αleft W := by
    apply derivedComposite_isRightDerived εX Γcoarse RεX RΓcoarse αεX αΓcoarse
    intro I hI
    let _ : IsIso (αεX.app ((HomotopyCategory.quotient
        (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective _ RεX αεX I hI
    let _ : IsIso (αΓcoarse.app ((εX.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (AbelianSheaves S.fineCoverage.toGrothendieck X)
          (ComplexShape.up ℤ)).obj I))) :=
      rightDerivedUnit_isIso_app_of_isKInjective _ RΓcoarse αΓcoarse
        ((εX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (abelianComparisonPushforward_map_isKInjective S X I hI)
    dsimp [derivedCompositeUnit]
    infer_instance
  exact Functor.rightDerivedNatIso (RεX ⋙ RΓcoarse) RΓfine αleft αΓfine W (Iso.refl _)

attribute [local instance] HasDerivedCategory.standard

/-- **Cohomology on the finer localized site over `X` is computed by the derived
change-of-topology direct image followed by cohomology on the coarser one, on bounded below
derived categories**:

`Rε_{X,*} ⋙ RΓ_{τ'}(X, -) ≅ RΓ_τ(X, -)`

as functors `D⁺(Ab(C_τ/X)) ⥤ D⁺(Ab)`, where all three right derived functors are the canonical
ones of `CategoryTheory.Functor.rightDerivedFunctorPlus`. -/
def derivedGlobalSectionsComparisonPlusIso (S : CohomologyComparison C) (X : C) :
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).rightDerivedFunctorPlus ⋙
        (globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerivedFunctorPlus ≅
      (globalSectionsOver S.fineCoverage.toGrothendieck X).rightDerivedFunctorPlus :=
  (Stacks.DerivedIndexing.rightDerivedPlusCompIso
    (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
    (globalSectionsOver S.coarseCoverage.toGrothendieck X)).symm

end Stacks.ComparingTopologies

end
