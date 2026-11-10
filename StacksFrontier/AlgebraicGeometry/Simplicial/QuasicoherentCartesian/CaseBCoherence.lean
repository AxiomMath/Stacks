module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseBBridge

/-!
# The localized transition of case (B) is the restricted transition

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice.sliceTransitionModules_app_over`: at
  the restriction of a module on the total site, the localized transition is the Beck–Chevalley
  comparison followed by the restriction of the transition to the slice at `W`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.CocontinuousSimplicialSite.CartesianSlice

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m) {W : (situation C).component m}
  {Q : (situation C).component n} (b : (transitionFunctorB C φ).obj W ⟶ Q)

/-- At the restriction of a module on the total site, the localized direct transition is the
restriction of the direct transition followed by the base change of Stacks 0FN1. -/
theorem sliceDirectTransition_app_over (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (sliceDirectTransition C P φ b).app
        (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) =
      (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology n).over Q)
        ((situation C).componentTopology n) (Over.forget Q) (ringSheafB C P n)).map
          (directTransitionB C P φ F) ≫
        (sliceSquare C P φ b).app
          (((situation C).componentModuleRestriction (totalRing C P) m).obj F) := by
  refine SheafOfModules.hom_ext ?_
  refine (PresheafOfModules.toPresheaf _).map_injective ?_
  refine NatTrans.ext (funext fun Y => Stacks.SheafOfModules.ran_hom_ext
    (sliceTransition C φ b).op _ fun j => ?_)
  refine ConcreteCategory.hom_ext _ _ fun x => ?_
  have hL := ConcreteCategory.congr_hom (sliceDirectPresheaf_app_comp_ranπ C P φ b
    (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))
    Y j) x
  have hR1 := ConcreteCategory.congr_hom (Stacks.SheafOfModules.squareComparisonApp_π
    (J' := ((situation C).componentTopology m).over W)
    (sliceTransition_comp_forget C φ b)
    (((situation C).componentModuleRestriction (totalRing C P) m).obj F) Y j)
    (((directTransitionB C P φ F).val.app (op Y.unop.left)).hom x)
  have hR2 := ranπ_directTransitionB_apply C P φ F (op Y.unop.left)
    (Stacks.SheafOfModules.squareIndex (sliceTransition_comp_forget C φ b) j) x
  refine hL.trans (Eq.trans ?_ (hR1.trans hR2).symm)
  have e : (Stacks.SheafOfModules.squareIndex (sliceTransition_comp_forget C φ b) j).hom =
      (Over.forget Q).op.map j.hom := Category.comp_id _
  refine Eq.trans ?_ (congrArg (fun g => (F.val.presheaf.map
    ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app j.right.unop.left).op).hom
      (((((situation C).componentModuleRestriction (totalRing C P) n).obj F).val.presheaf.map
        g).hom x)) e).symm
  rfl

/-- The adjunct of the right-hand side of `sliceTransitionModules_app_over`. -/
theorem homEquiv_beckChevalleyB_comp (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (slicePullbackAdj C P φ b).homEquiv _ _
        ((beckChevalleyB C P φ b).app
            (((situation C).componentModuleRestriction (totalRing C P) n).obj F) ≫
          (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology m).over W)
            ((situation C).componentTopology m) (Over.forget W) (ringSheafB C P m)).map
            (transitionB C P φ F)) =
      (sliceDirectTransition C P φ b).app
        (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj
          Q)) := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    sliceDirectTransition_app_over]
  have hu := unit_mateEquiv_symm (transitionModulePullbackAdjunctionB C P φ)
    (slicePullbackAdj C P φ b) (sliceSquare C P φ b)
    (((situation C).componentModuleRestriction (totalRing C P) n).obj F)
  have ht : directTransitionB C P φ F =
      (transitionModulePullbackAdjunctionB C P φ).unit.app _ ≫
        (transitionPushforwardB C P φ).map (transitionB C P φ F) :=
    (((transitionModulePullbackAdjunctionB C P φ).homEquiv _ _).apply_symm_apply _).symm.trans
      ((transitionModulePullbackAdjunctionB C P φ).homEquiv_unit _ _ _)
  refine (congrArg (· ≫ _) hu.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((sliceSquare C P φ b).naturality
    (transitionB C P φ F)).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm).trans ?_
  exact congrArg (fun t => (Stacks.SheafOfModules.inverseImage.{u}
    (((situation C).componentTopology n).over Q)
    ((situation C).componentTopology n) (Over.forget Q) (ringSheafB C P n)).map t ≫ _) ht.symm

/-- **The localized transition at the restriction of a module is the restriction of the
transition, read through the Beck–Chevalley comparison.** -/
theorem sliceTransitionModules_app_over (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (sliceTransitionModules C P φ b).app
        (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) =
      (beckChevalleyB C P φ b).app
          (((situation C).componentModuleRestriction (totalRing C P) n).obj F) ≫
        (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology m).over W)
          ((situation C).componentTopology m) (Over.forget W) (ringSheafB C P m)).map
          (transitionB C P φ F) := by
  refine ((slicePullbackAdj C P φ b).homEquiv _ _).injective ?_
  refine (congrArg ((slicePullbackAdj C P φ b).homEquiv _ _)
    (sliceTransitionModules_app C P φ b _)).trans ?_
  exact (Equiv.apply_symm_apply _ _).trans (homEquiv_beckChevalleyB_comp C P φ b F).symm

end CategoryTheory.CocontinuousSimplicialSite.CartesianSlice
