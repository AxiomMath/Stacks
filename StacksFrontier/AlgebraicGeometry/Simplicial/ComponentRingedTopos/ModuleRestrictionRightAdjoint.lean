module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek

/-!
# Restriction of modules to a simplicial component has a right adjoint

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. The inclusion
of the degree-`n` component into the total category is continuous and cocontinuous (Stacks 09WG),
so restriction of sheaves of modules along it — the functor `g_n^*` of Stacks 0D72 — has a right
adjoint as well as the left adjoint `g_{n!}` that tag asserts. The right adjoint is the direct
image of sheaves of modules along the morphism of topoi the component inclusion induces as a
cocontinuous functor, that is, right Kan extension on underlying sheaves of abelian groups.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModulePushforward`: the right adjoint
  `g_{n*}` of restriction of sheaves of modules to the degree-`n` component.
* `CategoryTheory.SimplicialSiteSituation.componentModuleRestrictionAdjunction`: the adjunction
  `g_n^* ⊣ g_{n*}`.

## Implementation notes

Both are the general statements of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RestrictRanAdjunction.lean` read at the
component inclusion, with nothing to transport: the component sheaf of rings
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf` *is*
`Stacks.SheafOfModules.RestrictRan.ringSheaf` at that functor, and
`CategoryTheory.SimplicialSiteSituation.componentModuleRestriction` *is*
`SheafOfModules.pushforward` at the identity structure map, both by definition.

Why this is wanted:
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentModuleSumFormulaPresheaf.lean` proves the
direct-sum formula of Stacks 0D72 in case (B) and on presheaves, and its implementation notes say
of case (A) that "the formula has to be obtained on the right-adjoint side, which for modules
needs a right adjoint of module restriction that this development does not have". This is that
right adjoint. The formula itself is not proved here, in either case.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
  (n : SimplexCategory)

/-- The direct image `g_{n*}` of sheaves of modules from the degree-`n` simplicial component to
the total site: the direct image along the morphism of topoi the component inclusion induces as
a cocontinuous functor, which on underlying sheaves of abelian groups is right Kan extension. -/
def componentModulePushforward :
    SheafOfModules.{u} (S.componentRingSheaf O n) ⥤ SheafOfModules.{u} O :=
  Stacks.SheafOfModules.pushforwardCocontinuous (S.componentFunctor n)
    (Stacks.SheafOfModules.RestrictRan.sheafUnit (S.componentFunctor n)
      (S.componentTopology n) S.totalTopology O)

/-- Restriction `g_n^*` of sheaves of modules to the degree-`n` simplicial component is left
adjoint to `g_{n*}`. So `g_n^*` has adjoints on both sides: `g_{n!}` of Stacks 0D72 on the left
and this one on the right. -/
def componentModuleRestrictionAdjunction :
    S.componentModuleRestriction O n ⊣ S.componentModulePushforward O n :=
  Stacks.SheafOfModules.RestrictRan.sheafAdjunction (S.componentFunctor n)
    (S.componentTopology n) S.totalTopology O

end CategoryTheory.SimplicialSiteSituation

end
