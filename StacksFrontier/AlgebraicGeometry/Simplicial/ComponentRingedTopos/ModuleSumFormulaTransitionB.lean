module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseBSummand

/-!
# The componentwise direct sum for modules along the transition morphisms, case (B)

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `P` be a sheaf of commutative rings on its total site. The direct-sum
formula of Stacks 0D72 for sheaves of modules is proved in case (B) by
`CategoryTheory.CocontinuousSimplicialSite.componentModuleSumFormulaB`, with the summand at `φ`
the sheafification of the presheaf-level module pullback along the transition functor `u_φ`.
This file gives the same formula with the summand taken along the transition morphism of ringed
topoi, the datum `CategoryTheory.SimplicialSiteSituation.ModuleSumFormula'`.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaB`: the componentwise direct-sum
  formula of Stacks 0D72 for sheaves of modules in case (B), with the summands taken along the
  transition morphisms of ringed topoi.

## Implementation notes

The coproducts of the two families of functors are taken through
`CategoryTheory.Limits.functorCategoryHasColimitsOfShape`, supplied locally rather than left to
instance search: `CategoryTheory.Limits.Sigma.mapIso` asks for all coproducts of the shape, and
this is the route whose term the kernel accepts.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

attribute [local instance] SimplicialSiteSituation.hasWeakSheafifyComponent

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})

/-- **The componentwise direct-sum formula of Stacks 0D72 for sheaves of modules in case
(B).** The restriction to degree `m` of lower shriek `g_{n!}` of
sheaves of `O`-modules is the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the pullbacks
of sheaves of modules along the transition morphisms of ringed topoi.

This is `componentModuleSumFormulaB`, whose summand is the sheafification of the presheaf-level
pullback along the transition functor, transported summandwise along
`transitionPullbackModulesIsoB`. -/
def moduleSumFormulaB (n : SimplexCategory) : (situation C).ModuleSumFormula' P n := fun m ↦
  letI : HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n) ⥤
        SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) m)) :=
    functorCategoryHasColimitsOfShape
  (componentModuleSumFormulaB C P n m).symm ≪≫
    Sigma.mapIso fun φ : n ⟶ m ↦ (transitionPullbackModulesIsoB C P φ).symm

end CategoryTheory.CocontinuousSimplicialSite

end
