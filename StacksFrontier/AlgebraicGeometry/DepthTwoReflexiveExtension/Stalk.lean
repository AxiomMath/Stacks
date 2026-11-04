module

public import StacksFrontier.AlgebraicGeometry.ReflexiveStalkCriterion.Basic

/-!
# The forward half of the stalkwise criterion for reflexivity

The implication (1) ⇒ (2) of [Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3):
every stalk of a reflexive module of finite presentation, whose dual is of finite presentation, is
a reflexive module over the local ring at that point.

## Main results

* `bijective_stalkLinearMap_of_isReflexive`: the stalk map of the canonical bidual map of a
  reflexive module is bijective.
* `isReflexive_stalk_of_isReflexive`: every stalk of a reflexive module of finite presentation
  with dual of finite presentation is a reflexive module over the local ring.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveDualHull
open Stacks.AlgebraicGeometry.ReflexiveStalkCriterion
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

variable {X : Scheme.{u}}

/-- The stalk map of the canonical bidual map of a reflexive module is bijective. -/
theorem bijective_stalkLinearMap_of_isReflexive (F : X.Modules) (h : IsReflexive F) (x : X) :
    Function.Bijective
      (OXModule.stalkLinearMap F (dualSheaf (dualSheaf F)) (toDoubleDual F) x) := by
  let E := (TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso ((PresheafOfModules.toPresheaf _).mapIso
    ((SheafOfModules.forget _).mapIso (@asIso _ _ _ _ (toDoubleDual F) h)))
  exact (ConcreteCategory.isIso_iff_bijective
    (OXModule.stalkMapAdd F (dualSheaf (dualSheaf F)) (toDoubleDual F) x)).1
      ⟨⟨E.inv, E.hom_inv_id, E.inv_hom_id⟩⟩

/-- **(1) ⇒ (2) of Stacks Tag 0AY3.**  Every stalk of a reflexive module of finite presentation
whose dual is of finite presentation is a reflexive module over the local ring at that point. -/
theorem isReflexive_stalk_of_isReflexive (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (h : IsReflexive F) (x : X) :
    Module.IsReflexive (ToType (ringStalk X.sheaf x)) (ToType (modStalk F x)) := by
  have hS := bijective_stalkLinearMap_of_isReflexive F h x
  refine ⟨⟨?_, ?_⟩⟩
  · intro a b hab
    refine hS.injective ((dualSheafStalkDualEquiv X (dualSheaf F) x).injective
      (LinearMap.ext fun t => ?_))
    rw [stalkDualEquiv_toDoubleDual F x a t, stalkDualEquiv_toDoubleDual F x b t]
    exact congrArg (fun psi => psi (dualSheafStalkDualEquiv X F x t)) hab
  · intro psi
    obtain ⟨m, hm⟩ := hS.surjective ((dualSheafStalkDualEquiv X (dualSheaf F) x).symm
      (psi.comp (dualSheafStalkDualEquiv X F x).toLinearMap))
    refine ⟨m, LinearMap.ext fun phi => ?_⟩
    obtain ⟨t, rfl⟩ := (dualSheafStalkDualEquiv X F x).surjective phi
    have hkey := stalkDualEquiv_toDoubleDual F x m t
    rw [hm, (dualSheafStalkDualEquiv X (dualSheaf F) x).apply_symm_apply] at hkey
    exact hkey.symm

end Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension

end
