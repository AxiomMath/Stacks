module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseASummand

/-!
# The componentwise direct sum for modules along the transition morphisms, case (A)

Let `C` be a simplicial site — case (A) of the simplicial-site situation of Stacks 09WE — and
let `P` be a sheaf of commutative rings on its total site. The direct-sum formula of Stacks 0D72
for sheaves of modules is proved in case (A) by
`CategoryTheory.SimplicialSite.componentModuleSumFormulaA`, with the summand at `φ` the pullback
of sheaves of modules along the ring map `O(φ)`. Stacks 0D74 and Stacks 0D75 consume the formula
with the summand taken along the transition morphism of ringed topoi, which is the datum
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormula`, and this file supplies that datum in
case (A): the summandwise comparison is
`CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA`, and a pointwise isomorphism of
families of functors transports along `CategoryTheory.Limits.Sigma.mapIso`.

This is one of the two halves of
`CategoryTheory.SimplicialSiteSituation.moduleSumFormula`, which supplies the datum for an
arbitrary situation by a case split on it, and so is what discharges the hypothesis of
Stacks 0D74 and Stacks 0D75 once and for all.

## Main definitions

* `CategoryTheory.SimplicialSite.moduleSumFormulaA`: **the componentwise direct-sum formula of
  Stacks 0D72 for sheaves of modules in case (A), in the shape Stacks 0D74 consumes it.**

## Implementation notes

The coproducts of the two families of functors are taken through
`CategoryTheory.Limits.functorCategoryHasColimitsOfShape`, which is the route
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleSumFormulaCaseA.lean`
records as the one whose term the kernel accepts; `CategoryTheory.Limits.Sigma.mapIso` asks for
all coproducts of the shape rather than for the single one, so the instance is supplied as a
`letI` rather than left to search.

Sheafifiability of abelian sheaves on a component — `hasWeakSheafifyComponent` — is what makes
those coproducts exist at all, and it is activated locally here as it is in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriekExact.lean`,
where `ModuleSumFormula'` is defined.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSite

attribute [local instance] SimplicialSiteSituation.hasWeakSheafifyComponent

variable (C : SimplicialSite.{u}) (P : Sheaf (situation C).totalTopology CommRingCat.{u})

/-- **The componentwise direct-sum formula of Stacks 0D72 for sheaves of modules in case (A), in
the shape Stacks 0D74 consumes it.** The restriction to degree `m` of lower shriek `g_{n!}` of
sheaves of `O`-modules is the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the pullbacks
of sheaves of modules along the transition morphisms of ringed topoi.

This is `componentModuleSumFormulaA`, whose summand is the pullback along the ring map `O(φ)`,
transported summandwise along `transitionPullbackModulesIsoA`. -/
def moduleSumFormulaA (n : SimplexCategory) : (situation C).ModuleSumFormula' P n := fun m ↦
  letI : HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n) ⥤
        SheafOfModules.{u} ((situation C).componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) m)) :=
    functorCategoryHasColimitsOfShape
  (componentModuleSumFormulaA C
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) n m).symm ≪≫
    Sigma.mapIso fun φ : n ⟶ m ↦ (transitionPullbackModulesIsoA C P φ).symm

end CategoryTheory.SimplicialSite

end
