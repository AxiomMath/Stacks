module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseASlice

/-!
# The localized transition of case (A) is the restricted transition

The transition `f_φ^* Mₙ ⟶ M_m` of a module on the total site of a simplicial site of case (A),
restricted to the slice at `u_φ(Q)`, is the localized transition at the restriction of the module
to the total slice at `Q`, once the two pullbacks are compared by the Beck–Chevalley map.

## Main results

* `CategoryTheory.SimplicialSite.CartesianSlice.beckChevalleyA`: the Beck–Chevalley comparison.
* `CategoryTheory.SimplicialSite.CartesianSlice.sliceTransitionModules_app_over`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m) (Q : (situation C).component n)

/-- The transition functor of case (A) followed by the component functor at `m` is continuous
from the degree-`n` component topology to the total topology. -/
instance isContinuous_transitionFunctorA_comp_componentFunctor :
    (transitionFunctorA C φ ⋙ SimplicialSiteSituation.componentFunctor (situation C) m).IsContinuous
      ((situation C).componentTopology n) (situation C).totalTopology :=
  Functor.isContinuous_comp _ _ _ ((situation C).componentTopology m) _

/-- The ring map attached to the arrows `(φ, 𝟙)` is the ring map `O(φ)`. -/
theorem transitionNatTransA_ring :
    (𝟙 ((situation C).componentRingSheaf O n)) ≫
        (Functor.sheafPushforwardContinuousNatTrans (transitionNatTransA C φ) RingCat.{u}
          ((situation C).componentTopology n) (situation C).totalTopology).app O =
      ringTransitionA C O φ ≫
        ((transitionFunctorA C φ).sheafPushforwardContinuous RingCat.{u}
          ((situation C).componentTopology n) ((situation C).componentTopology m)).map
          (𝟙 ((situation C).componentRingSheaf O m)) := by
  ext : 2
  rfl

/-- The direct form of the transition of Stacks 09WF in case (A), with Mathlib's direct image of
sheaves of modules along the ring map `O(φ)`. -/
def directTransitionA :
    (situation C).componentModuleRestriction O n ⟶
      (situation C).componentModuleRestriction O m ⋙
        SheafOfModules.pushforward.{u} (ringTransitionA C O φ) :=
  SheafOfModules.pushforwardNatTrans.{u} (J := (situation C).componentTopology n)
      (K := (situation C).totalTopology)
      (T := (situation C).componentRingSheaf O n) (S := O)
      (F := transitionFunctorA C φ ⋙ SimplicialSiteSituation.componentFunctor (situation C) m)
      (G := SimplicialSiteSituation.componentFunctor (situation C) n)
      (𝟙 ((situation C).componentRingSheaf O n)) (transitionNatTransA C φ) ≫
    (SheafOfModules.pushforwardCongr.{u} (J := (situation C).componentTopology n)
        (K := (situation C).totalTopology)
        (S := (situation C).componentRingSheaf O n) (R := O)
        (F := transitionFunctorA C φ ⋙ SimplicialSiteSituation.componentFunctor (situation C) m)
        (transitionNatTransA_ring C O φ)).hom ≫
      (SheafOfModules.pushforwardComp.{u}
        (J := (situation C).componentTopology n)
        (K := (situation C).componentTopology m)
        (K' := (situation C).totalTopology)
        (F := transitionFunctorA C φ)
        (G := SimplicialSiteSituation.componentFunctor (situation C) m)
        (S := (situation C).componentRingSheaf O n)
        (R := (situation C).componentRingSheaf O m) (R' := O)
        (ringTransitionA C O φ) (𝟙 ((situation C).componentRingSheaf O m))).inv

/-- The transition `f_φ^* M_n ⟶ M_m` for Mathlib's pullback along `O(φ)`. -/
def transitionA (M : SheafOfModules.{u} O) :
    (SheafOfModules.pullback.{u} (ringTransitionA C O φ)).obj
        (((situation C).componentModuleRestriction O n).obj M) ⟶
      ((situation C).componentModuleRestriction O m).obj M :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ)).homEquiv _ _).symm
    ((directTransitionA C O φ).app M)

/-- The square of direct images and restrictions to slices. -/
def overPushforwardIso :
    SheafOfModules.pushforward.{u} (ringTransitionA C O φ) ⋙
        SheafOfModules.overFunctor ((situation C).componentRingSheaf O n) Q ≅
      SheafOfModules.overFunctor ((situation C).componentRingSheaf O m)
          ((transitionFunctorA C φ).obj Q) ⋙ slicePushforward C O φ Q :=
  Iso.refl _


/-- **The Beck–Chevalley comparison** `h^*(M|_Q) ⟶ (f^*M)|_{u Q}`, the mate of the identification
of the two direct images. -/
def beckChevalleyA :
    TwoSquare (SheafOfModules.overFunctor ((situation C).componentRingSheaf O n) Q)
      (SheafOfModules.pullback.{u} (ringTransitionA C O φ)) (slicePullback C O φ Q)
      (SheafOfModules.overFunctor ((situation C).componentRingSheaf O m)
        ((transitionFunctorA C φ).obj Q)) :=
  (mateEquiv (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ))
    (slicePullbackAdj C O φ Q)).symm (TwoSquare.mk _ _ _ _ (overPushforwardIso C O φ Q).hom)

/-- At the restriction of a module on the total site, the localized direct transition is the
restriction of the direct transition. -/
theorem sliceDirectTransition_app_over (F : SheafOfModules.{u} O) :
    (sliceDirectTransition C O φ Q).app
        (F.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) =
      (SheafOfModules.overFunctor ((situation C).componentRingSheaf O n) Q).map
        ((directTransitionA C O φ).app F) := by
  ext V : 3
  rfl

/-- The adjunct of the right-hand side of `sliceTransitionModules_app_over`. -/
theorem homEquiv_beckChevalleyA_comp (F : SheafOfModules.{u} O) :
    (slicePullbackAdj C O φ Q).homEquiv _ _
        ((beckChevalleyA C O φ Q).app
            (((situation C).componentModuleRestriction O n).obj F) ≫
          (SheafOfModules.overFunctor ((situation C).componentRingSheaf O m)
            ((transitionFunctorA C φ).obj Q)).map (transitionA C O φ F)) =
      (SheafOfModules.overFunctor ((situation C).componentRingSheaf O n) Q).map
        ((directTransitionA C O φ).app F) := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  have hu := unit_mateEquiv_symm
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ))
    (slicePullbackAdj C O φ Q) (TwoSquare.mk _ _ _ _ (overPushforwardIso C O φ Q).hom)
    (((situation C).componentModuleRestriction O n).obj F)
  have e1 := hu.symm.trans (Category.comp_id _)
  have ht : (directTransitionA C O φ).app F =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ)).unit.app _ ≫
        (SheafOfModules.pushforward.{u} (ringTransitionA C O φ)).map (transitionA C O φ F) :=
    (((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ)).homEquiv _ _
      ).apply_symm_apply _).symm.trans
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringTransitionA C O φ)).homEquiv_unit
        _ _ _)
  exact (congrArg (· ≫ _) e1).trans ((Functor.map_comp _ _ _).symm.trans
    (congrArg (SheafOfModules.overFunctor ((situation C).componentRingSheaf O n) Q).map ht.symm))

/-- **The localized transition at the restriction of a module is the restriction of the
transition, read through the Beck–Chevalley comparison.** -/
theorem sliceTransitionModules_app_over (F : SheafOfModules.{u} O) :
    (sliceTransitionModules C O φ Q).app
        (F.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) =
      (beckChevalleyA C O φ Q).app (((situation C).componentModuleRestriction O n).obj F) ≫
        (SheafOfModules.overFunctor ((situation C).componentRingSheaf O m)
          ((transitionFunctorA C φ).obj Q)).map (transitionA C O φ F) := by
  have h2 : (slicePullbackAdj C O φ Q).homEquiv _ _ ((sliceTransitionModules C O φ Q).app
        (F.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))) =
      (SheafOfModules.overFunctor ((situation C).componentRingSheaf O n) Q).map
        ((directTransitionA C O φ).app F) := by
    rw [sliceTransitionModules_app, Equiv.apply_symm_apply, sliceDirectTransition_app_over]
  exact ((slicePullbackAdj C O φ Q).homEquiv _ _).injective
    (h2.trans (homEquiv_beckChevalleyA_comp C O φ Q F).symm)

end CategoryTheory.SimplicialSite.CartesianSlice
