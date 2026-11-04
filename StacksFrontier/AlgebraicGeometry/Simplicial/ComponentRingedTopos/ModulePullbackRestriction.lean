module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction

/-!
# Inverse image of modules along the component restriction functor

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. Restriction
of sheaves of `O`-modules to the degree-`n` component is the inverse image of sheaves of modules
along the restriction functor of sheaves of sets, the scalars being compared along
`Stacks.Sheaves.ToposPullback.restrictionRingIso`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleRestriction_eq_restrictionModules`:
  restriction of modules to a component is, on the nose, the general restriction of modules
  along a continuous functor of sites.
* `CategoryTheory.SimplicialSiteSituation.componentModulePullbackRestrictionIso`: the inverse
  image of sheaves of modules along the component restriction functor of sheaves of sets is that
  restriction, followed by restriction of scalars.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
  (n : SimplexCategory)

/-- Restriction of sheaves of modules to the degree-`n` component is the general restriction of
sheaves of modules along a continuous functor of sites, instantiated at the component
inclusion. -/
theorem componentModuleRestriction_eq_restrictionModules :
    restrictionModules (S.componentTopology n) S.totalTopology (componentFunctor S n) O =
      componentModuleRestriction S O n :=
  rfl

/-- The inverse image of sheaves of `O`-modules along the functor of sheaves of sets given by
restriction to the degree-`n` component is restriction of sheaves of modules to that component,
followed by restriction of scalars along
`Stacks.Sheaves.ToposPullback.restrictionRingIso`. -/
noncomputable def componentModulePullbackRestrictionIso :
    pullbackModuleFunctor (S.componentTopology n)
        ((componentFunctor S n).sheafPushforwardContinuous (Type u)
          (S.componentTopology n) S.totalTopology) O ≅
      componentModuleRestriction S O n ⋙
        SheafOfModules.restrictScalars
          (restrictionRingIso (S.componentTopology n) S.totalTopology
            (componentFunctor S n) O).hom :=
  restrictionModuleIso (S.componentTopology n) S.totalTopology (componentFunctor S n) O

end CategoryTheory.SimplicialSiteSituation

end
