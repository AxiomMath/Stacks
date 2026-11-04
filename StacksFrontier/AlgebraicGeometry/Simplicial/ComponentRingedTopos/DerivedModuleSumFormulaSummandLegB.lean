module

public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormulaSummandLeg
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegCaseB
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegSituation

/-!
# The derived summand description of Stacks 0D72 (6) in case (B) of Stacks 09WE

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `P` be a sheaf of commutative rings on its total site. Granted the case-(B)
leg equation `CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB` and flatness of
the structure-sheaf transitions, the summand inclusions of the derived componentwise direct-sum
formula are the canonical maps.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEq_situation_of_legEqB`: the
  situation-level leg equation of Stacks 0D72 (6) in case (B), from the case-(B) one.
* `CategoryTheory.CocontinuousSimplicialSite.derivedModuleSumFormulaSummand_of_legEqB`:
  Stacks 0D72 (6) on derived categories of modules in case (B), from the case-(B) leg equation and
  flatness of the structure-sheaf transitions.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})

/-- In case (B), the case-(B) leg equation
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB` for every map of
`SimplexCategory` gives the situation-level leg equation
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq`. -/
theorem moduleSumFormulaLegEq_situation_of_legEqB
    (hleg : ∀ {n m : SimplexCategory} (φ : n ⟶ m), ModuleSumFormulaLegEqB C P φ) :
    (situation C).ModuleSumFormulaLegEq P :=
  fun φ => hleg φ

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy ((situation C).transitionRingedToposHom P φ)).HasLeftDerivedFunctor
    (targetQuasiIso ((situation C).componentRingedTopos P m))]

/-- In case (B), granted the case-(B) leg equation on sheaves of modules and flatness of the
structure-sheaf transitions, the summand inclusions of the derived componentwise direct-sum
formula are the canonical maps. -/
theorem derivedModuleSumFormulaSummand_of_legEqB
    (hleg : ∀ {n m : SimplexCategory} (φ : n ⟶ m), ModuleSumFormulaLegEqB C P φ)
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m),
      ((situation C).transitionRingedToposHom P φ).IsFlat) :
    SimplicialSiteSituation.DerivedModuleSumFormulaSummand (situation C) P hflat :=
  (situation C).derivedModuleSumFormulaSummand_of_moduleSumFormulaLegEq P
    (moduleSumFormulaLegEq_situation_of_legEqB C P hleg) hflat

end CategoryTheory.CocontinuousSimplicialSite

end
