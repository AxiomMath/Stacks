module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import StacksFrontier.CategoryTheory.Sites.Sheafification.PreservesFiniteLimits
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of extension by zero along an open immersion

Let `X` be a topological space, `U ⊆ X` an open subset and `j : U → X` the inclusion. The
extension-by-zero functor `j_! : Ab(U) → Ab(X)` is exact. Right exactness is formal: `j_!` is
a left adjoint (`ExtensionByZero.jExtAdjunction`), so it preserves all colimits. Left
exactness is the content: `j_!` is the composite of the forgetful functor to presheaves, the
presheaf-level extension by an initial object, and sheafification, and each of the three
preserves finite limits. For the middle functor this is checked objectwise, using that the
presheaf `j_! F` has value `F(j⁻¹V)` on an open `V ⊆ U` and the zero group on an open `V`
not contained in `U`.

## Main results

* `ExtensionByZero.jExt_exactFunctor`: extension by zero is an exact functor on sheaves of
  abelian groups, in the sense of Mathlib's `CategoryTheory.exactFunctor` predicate
  (preservation of finite limits and of finite colimits).

## Implementation notes

An open immersion is presented as the inclusion of its open image, so the source category is
the category of abelian sheaves on `ExtensionByZero.Usp U`, the open set `U` with its subspace
topology.

## References

* [Stacks Project, Tag 01AK](https://stacks.math.columbia.edu/tag/01AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ExtensionByZero

/-- The presheaf-level extension by an initial object preserves finite limits. It is checked
objectwise: evaluating at an open `V ≤ U` gives, up to isomorphism, evaluation of the source
presheaf at `j⁻¹ V`, and evaluating at an open `V` not contained in `U` gives the constant
functor at the initial (hence zero) object. -/
theorem preservesFiniteLimits_extendByInitialFunctor {X : TopCat.{u}} (U : Opens X) :
    PreservesFiniteLimits
      (TopCat.Presheaf.extendByInitialFunctor (C := AddCommGrpCat.{u}) U) := by
  apply preservesFiniteLimits_of_evaluation
  intro V
  by_cases hV : V.unop ≤ U
  · let e : (evaluation (Opens (Usp U))ᵒᵖ AddCommGrpCat.{u}).obj
            (Opposite.op ((Opens.map U.inclusion').obj V.unop)) ≅
          TopCat.Presheaf.extendByInitialFunctor (C := AddCommGrpCat.{u}) U ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V :=
      NatIso.ofComponents (fun F =>
        (eqToIso (TopCat.Presheaf.ExtensionByInitial.obj_of_le U F hV)).symm) (by
          intro F G η
          simp [TopCat.Presheaf.extendByInitialFunctor,
            TopCat.Presheaf.extendByInitial, TopCat.Presheaf.ExtensionByInitial.map,
            TopCat.Presheaf.ExtensionByInitial.mapNat,
            TopCat.Presheaf.ExtensionByInitial.appMap, hV])
    let _ : PreservesFiniteLimits
        ((evaluation (Opens (Usp U))ᵒᵖ AddCommGrpCat.{u}).obj
          (Opposite.op ((Opens.map U.inclusion').obj V.unop))) :=
      instPreservesFiniteLimitsFunctorObjEvaluationOfHasFiniteLimits _
    exact preservesFiniteLimits_of_natIso e
  · let e : (Functor.const (TopCat.Presheaf AddCommGrpCat (Usp U))).obj
            (⊥_ AddCommGrpCat.{u}) ≅
          TopCat.Presheaf.extendByInitialFunctor (C := AddCommGrpCat.{u}) U ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V :=
      NatIso.ofComponents (fun F =>
        (eqToIso (TopCat.Presheaf.ExtensionByInitial.obj_of_not_le U F hV)).symm) (by
          intro F G η
          simp only [Functor.const_obj_obj, Functor.comp_obj, evaluation_obj_obj,
            Functor.const_obj_map, Iso.symm_hom, eqToIso.inv, Category.id_comp,
            Functor.comp_map, evaluation_obj_map]
          apply (initialIsInitial : IsInitial (⊥_ AddCommGrpCat.{u})).hom_ext)
    let _ : PreservesFiniteLimits
        ((Functor.const (TopCat.Presheaf AddCommGrpCat (Usp U))).obj
          (⊥_ AddCommGrpCat.{u})) :=
      ⟨fun J _ _ =>
        (((Functor.const (TopCat.Presheaf AddCommGrpCat (Usp U))).obj
            (⊥_ AddCommGrpCat.{u})).preservesLimitsOfShape_of_isZero
          (((Functor.const (TopCat.Presheaf AddCommGrpCat (Usp U))).obj
            (⊥_ AddCommGrpCat.{u})).isZero (fun _ => by
              dsimp
              exact (isZero_zero (C := AddCommGrpCat.{u})).of_iso
                HasZeroObject.zeroIsoInitial.symm)) J)⟩
    exact preservesFiniteLimits_of_natIso e

/-- **Stacks 01AK.** Extension by zero along the inclusion of an open subspace is an exact
functor on sheaves of abelian groups. -/
@[stacks 01AK]
theorem jExt_exactFunctor {X : TopCat.{u}} (U : Opens X) :
    exactFunctor
      (TopCat.Sheaf AddCommGrpCat.{u} (Usp U))
      (TopCat.Sheaf AddCommGrpCat.{u} X)
      (jExt U) := by
  rw [exactFunctor_iff]
  refine ⟨?_, ⟨fun J _ _ =>
    (jExtAdjunction U).leftAdjoint_preservesColimits.preservesColimitsOfShape⟩⟩
  change PreservesFiniteLimits
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (Usp U) ⋙
      TopCat.Presheaf.extendByInitialFunctor U ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  have := preservesFiniteLimits_extendByInitialFunctor U
  have : PreservesFiniteLimits
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
    apply presheafToSheaf_preservesFiniteLimits
  have : PreservesFiniteLimits
      (TopCat.Presheaf.extendByInitialFunctor (C := AddCommGrpCat.{u}) U ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology (Usp U)) AddCommGrpCat.{u}) _

end ExtensionByZero

end
