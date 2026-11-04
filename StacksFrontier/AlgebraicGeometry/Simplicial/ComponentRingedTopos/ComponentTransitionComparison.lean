module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentPullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTransitionDirectImage
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionNatural
public import StacksFrontier.CategoryTheory.Adjunction.CompositeConjugateUnit

/-!
# Comparing the two transitions of component modules, in pullback and in direct-image form

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`φ : [m] ⟶ [n]` a simplex map. The development carries two transitions comparing the
restrictions of a sheaf of `O`-modules to the components of degrees `m` and `n`, one for each of
the two presentations of restriction that
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ComponentPullbackRestriction.lean`
identifies: `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules` for the literal
restriction and `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition` for the pullback
along the component morphism of ringed topoi. That the two agree under the identification is
what carries the cartesian condition from one presentation to the other.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleFiberTransition_comp_restrictionIso`: the two
  transitions agree under the identification of the two presentations.

## Implementation notes

Both transitions are adjuncts: `fiberTransitionModules` is by definition the adjunct of the
direct-image transition
`CategoryTheory.SimplicialSiteSituation.restrictTransitionModulesApp`, and the comparison asked
for here is therefore an equation between adjuncts. Transposing it is
`CategoryTheory.Adjunction.homEquiv_naturality_left` for the comparison prepended on the source
and `CategoryTheory.Adjunction.homEquiv_naturality_right` for the one appended on the target,
and `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_adj` on the other side. So the
content of the comparison is entirely in direct-image form, where the two sides are maps between
literal restrictions and a direct image of them.

*How the transposed equation is proved.* It is the module analogue of the splitting that
`CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism_commutes` performs for
sheaves of sets: the transpose of `moduleFiberTransition` along the transition adjunction is the
inner half of its transpose along the adjunction of the composite `g_m ∘ f_φ`, which by the
defining property of
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` is
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pushforwardModulesMap` of the 2-morphism
`g_n ⟶ g_m ∘ f_φ`. That transposition is
`Stacks.CategoryTheory.unit_comp_homEquiv_conjugate` and
`Stacks.CategoryTheory.homEquiv_comp_map_eq`, both proved for abstract adjunctions, and what
they leave is the identity of direct images
`CategoryTheory.SimplicialSiteSituation.componentPushforwardTransition_adjunct`, which holds for
sheaves of sets because the direct images of modules have the direct images of the underlying
sheaves of sets underneath on the nose
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.moduleSheafFunctor_map_pushforwardModulesMap`),
the underlying map of the direct-image transition of modules is the direct-image transition of
sheaves of sets, and the identification of the two presentations of restriction is the
comparison of Stacks 09WG on underlying sheaves of sets
(`CategoryTheory.SimplicialSiteSituation.componentPullbackModulesRestrictionIso_underlying`).

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  {m n : SimplexCategory} (φ : m ⟶ n)

/-- **The two transitions of component modules agree under the identification of the two
presentations of restriction.**

The transition for the literal restriction is the adjunct of the direct-image transition of
Stacks 09WF, so the equation of this statement is an equation of adjuncts: the comparison
prepended on the source passes through the adjunction bijection on the left, the one appended on
the target passes through it on the right, and the right-hand side transposes to the direct-image
transition itself. The transposed equation `h` is
`Stacks.CategoryTheory.homEquiv_comp_map_eq` at the compositors of Stacks 03D8 and the
2-morphism of Stacks 04IC, whose two hypotheses are the transposition
`Stacks.CategoryTheory.unit_comp_homEquiv_conjugate` of the mate and the identity
`CategoryTheory.SimplicialSiteSituation.componentPushforwardTransition_adjunct` of direct
images. -/
theorem moduleFiberTransition_comp_restrictionIso
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((componentPullbackModulesRestrictionIso S O m).inv.app M) ≫
        (S.moduleFiberTransition O φ).app M ≫
          (componentPullbackModulesRestrictionIso S O n).hom.app M =
      S.fiberTransitionModules O φ M := by
  have hfun : S.moduleFiberTransition O φ =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
          (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)).inv ≫
        (S.componentRingedTwoMorphism O φ).pullbackModulesMap := rfl
  have happ : (S.moduleFiberTransition O φ).app M =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
          (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)).inv.app M ≫
        (S.componentRingedTwoMorphism O φ).pullbackModulesMap.app M :=
    (congrArg (fun a ↦ NatTrans.app a M) hfun).trans (NatTrans.comp_app _ _ M)
  have hα : (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
          (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)).hom.app M ≫
        (S.moduleFiberTransition O φ).app M =
      (S.componentRingedTwoMorphism O φ).pullbackModulesMap.app M :=
    by rw [happ]; exact Iso.hom_inv_id_app_assoc _ M _
  have hC1 := Stacks.CategoryTheory.unit_comp_homEquiv_conjugate
    (componentRingedToposHom S O m).pullbackAdjPushforwardModules
    (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules
    (componentRingedToposHom S O n).pullbackAdjPushforwardModules
    (AlgebraicGeometry.RingedToposHom.comp (X := S.componentRingedTopos O n)
        (Y := S.componentRingedTopos O m) (Z := S.totalRingedTopos O)
        (componentRingedToposHom S O m)
        (S.transitionRingedToposHom O φ)).pullbackAdjPushforwardModules
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m))
    (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m))
    (AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m))
    (S.componentRingedTwoMorphism O φ).pushforwardModulesMap
    ((S.moduleFiberTransition O φ).app M) hα
  have h' := Stacks.CategoryTheory.homEquiv_comp_map_eq
    (componentRingedToposHom S O m).pullbackAdjPushforwardModules
    (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules
    (componentRingedToposHom S O n).pullbackAdjPushforwardModules
    (AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m))
    (S.componentRingedTwoMorphism O φ).pushforwardModulesMap
    ((S.moduleFiberTransition O φ).app M) hC1
    ((componentPullbackModulesRestrictionIso S O n).hom.app M)
    ((componentPullbackModulesRestrictionIso S O m).hom.app M)
    (S.restrictTransitionModulesApp O φ M)
    (S.componentPushforwardModulesMap_adjunct φ O M)
  have h := (congrArg
      ((componentPullbackModulesRestrictionIso S O m).inv.app M ≫ ·) h').trans
    (Iso.inv_hom_id_app_assoc (componentPullbackModulesRestrictionIso S O m) M
      (S.restrictTransitionModulesApp O φ M))
  refine ((S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules.homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact h.trans (S.fiberTransitionModules_adj O φ M).symm

/-- **The cartesian condition transports from the pullback presentation to the literal
restriction presentation**, one simplex map at a time, as soon as the two transitions have been
compared. This is the step by which Stacks 0D7H (3) — proved for
`CategoryTheory.SimplicialSiteSituation.IsModuleFiberTransitionIso` — becomes a statement about
`CategoryTheory.SimplicialSiteSituation.IsCartesianModule`. -/
theorem isIso_fiberTransitionModules_of_isIso_moduleFiberTransition
    (M : SheafOfModules.{u} (S.totalRingSheaf O))
    (h : (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
            ((componentPullbackModulesRestrictionIso S O m).inv.app M) ≫
          (S.moduleFiberTransition O φ).app M ≫
            (componentPullbackModulesRestrictionIso S O n).hom.app M =
        S.fiberTransitionModules O φ M)
    [IsIso ((S.moduleFiberTransition O φ).app M)] :
    IsIso (S.fiberTransitionModules O φ M) := by
  rw [← h]
  exact (((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapIso
        ((componentPullbackModulesRestrictionIso S O m).app M).symm) ≪≫
      (asIso ((S.moduleFiberTransition O φ).app M) ≪≫
        (componentPullbackModulesRestrictionIso S O n).app M)).isIso_hom

end CategoryTheory.SimplicialSiteSituation

end
