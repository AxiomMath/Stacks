module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence

/-!
# The derived unit of an exact adjunction, two constructions

Let `f ⊣ g` be an adjunction between abelian categories with `f` exact. The canonical map
`K ⟶ Rg(f̄K)` on bounded below derived categories is built in this library twice: as
`Stacks.LerayPullbackComparison.derivedUnit`, through which the pullback on derived sections
`Stacks.LerayPullbackComparison.lerayPullback` is defined, and as the unit of the derived
adjunction `f̄ ⊣ Rg` of `Stacks.ComparingTopologies.derivedPlusAdjunction`. This file proves that
the two agree: both are the unit of `f ⊣ g` applied degreewise followed by the unit of `Rg`, on
the image of the localization functor.

## Main results

* `Stacks.LerayPullbackComparison.derivedUnit_eq_derivedPlusAdjunction_unit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.LerayPullbackComparison

variable {D₀ D : Type*} [Category* D₀] [Category* D] [Abelian D₀] [Abelian D]
  [HasDerivedCategory D₀] [HasDerivedCategory D] [EnoughInjectives D₀] [EnoughInjectives D]
  {f : D₀ ⥤ D} {g : D ⥤ D₀} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

omit [EnoughInjectives D₀] in
/-- **The derived unit of the Leray comparison is the unit of the derived adjunction.** -/
theorem derivedUnit_eq_derivedPlusAdjunction_unit (adj : f ⊣ g) :
    derivedUnit adj = (Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso D₀)
  intro K
  have : f.mapDerivedCategoryPlus.IsLeftDerivedFunctor
      f.mapDerivedCategoryPlusFactorsh.hom (HomotopyCategory.Plus.quasiIso D₀) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso D₀) _
      f.mapDerivedCategoryPlusFactorsh
  have : (f.mapDerivedCategoryPlus ⋙ g.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        f.mapDerivedCategoryPlusFactorsh.hom g.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso D₀) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso D₀) _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        f.mapDerivedCategoryPlusFactorsh g.rightDerivedFunctorPlus)
  rw [derivedUnit_app_Qh]
  have h := Adjunction.derivedη_fac_app adj.mapHomotopyCategoryPlus
    (HomotopyCategory.Plus.quasiIso D₀) f.mapDerivedCategoryPlusFactorsh.hom
    g.rightDerivedFunctorPlusUnith K
  have h' : (adj.mapHomotopyCategoryPlus.derivedη (HomotopyCategory.Plus.quasiIso D₀)
      f.mapDerivedCategoryPlusFactorsh.hom g.rightDerivedFunctorPlusUnith).app
        (DerivedCategory.Plus.Qh.obj K) =
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
        g.rightDerivedFunctorPlusUnith.app (f.mapHomotopyCategoryPlus.obj K)) ≫
          g.rightDerivedFunctorPlus.map (f.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    rw [← h, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm.trans
      (congrArg (_ ≫ ·) (g.rightDerivedFunctorPlus.map_id _).symm)
  refine Eq.trans ?_ h'.symm
  simp only [Category.assoc]
  rfl

end Stacks.LerayPullbackComparison

end
