module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseBBeckChevalley
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition

/-!
# The transition of case (B) read in the ringed-topos development

The direct form `Mₙ ⟶ f_* M_m` of the transition of Stacks 09WF in case (B), for the direct image
along the cocontinuous transition functor, its transpose `f^* Mₙ ⟶ M_m`, and their identification
with the transitions in the cartesian condition of Stacks 07TF (2).

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice.fiberTransitionModules_eq_transitionB`.
* `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice.ranπ_directTransitionB_apply`: the legs
  of the direct form.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.CocontinuousSimplicialSite.CartesianSlice

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m)

/-- The direct form `M_n ⟶ f_*M_m` of the transition of Stacks 09WF in case (B), for the direct
image along the cocontinuous transition functor. -/
def directTransitionB (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    ((situation C).componentModuleRestriction (totalRing C P) n).obj F ⟶
      (transitionPushforwardB C P φ).obj
        (((situation C).componentModuleRestriction (totalRing C P) m).obj F) :=
  (situation C).restrictTransitionModulesApp P φ F ≫
    (transitionRingedToposPushforwardModulesIsoB C P φ).inv.app _

/-- The transition `f_φ^* M_n ⟶ M_m` of case (B). -/
def transitionB (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (transitionModulePullbackB C P n m φ).obj
        (((situation C).componentModuleRestriction (totalRing C P) n).obj F) ⟶
      ((situation C).componentModuleRestriction (totalRing C P) m).obj F :=
  ((transitionModulePullbackAdjunctionB C P φ).homEquiv _ _).symm (directTransitionB C P φ F)

/-- The direct-image transition of the ringed-topos development is the direct form of case (B),
followed by the comparison of the two direct images. -/
theorem restrictTransitionModulesApp_eq_directTransitionB
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (situation C).restrictTransitionModulesApp P φ F =
      directTransitionB C P φ F ≫ (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app _ :=
  (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((transitionRingedToposPushforwardModulesIsoB C P φ).inv_hom_id_app _))).trans
      (Category.comp_id _)).symm

/-- The transition in the cartesian condition is the transition of case (B), up to the
comparison of the two pullbacks. -/
theorem fiberTransitionModules_eq_transitionB
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (situation C).fiberTransitionModules P φ F =
      (transitionPullbackModulesIsoB C P φ).hom.app _ ≫ transitionB C P φ F := by
  refine (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv
    _ _).injective ?_
  refine ((situation C).fiberTransitionModules_adj P φ F).trans ?_
  refine (restrictTransitionModulesApp_eq_directTransitionB C P φ F).trans ?_
  refine Eq.trans ?_ (homEquiv_transitionPullbackModulesIsoB_hom_app_comp C P φ
    (((situation C).componentModuleRestriction (totalRing C P) n).obj F)
    (((situation C).componentModuleRestriction (totalRing C P) m).obj F)
    (transitionB C P φ F)).symm
  exact congrArg (· ≫ _) (((transitionModulePullbackAdjunctionB C P φ).homEquiv
    _ _).apply_symm_apply _).symm

/-- **The legs of the direct form of the transition.** -/
theorem ranπ_directTransitionB_apply (F : SheafOfModules.{u} ((situation C).totalRingSheaf P))
    (V : ((situation C).component n)ᵒᵖ) (j : StructuredArrow V (transitionFunctorB C φ).op)
    (x : (((situation C).componentModuleRestriction (totalRing C P) n).obj F).val.obj V) :
    (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
        (((situation C).componentModuleRestriction (totalRing C P) m).obj F).val.presheaf V j).hom
        (((directTransitionB C P φ F).val.app V).hom x) =
      (F.val.presheaf.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app
          j.right.unop).op).hom
        (((((situation C).componentModuleRestriction (totalRing C P) n).obj F).val.presheaf.map
          j.hom).hom x) := by
  have h1 := Stacks.SheafOfModules.ranπ_ranCompIso_hom_app (transitionFunctorB C φ)
    (((situation C).componentModuleRestriction (totalRing C P) m).obj F).val.presheaf V j
    (((directTransitionB C P φ F).val.app V).hom x)
  refine h1.symm.trans ?_
  have h3 := congrArg (fun t => (t.val.app V).hom x)
    (restrictTransitionModulesApp_eq_directTransitionB C P φ F)
  refine (congrArg (Stacks.SheafOfModules.ranπ (transitionFunctorB C φ).op
    ((((situation C).componentModuleRestriction (totalRing C P) m).obj F).val.presheaf ⋙
      forget AddCommGrpCat.{u}) V j) h3.symm).trans ?_
  exact ranπ_restrictTransition C φ
    (Sheaf.moduleSheaf.{u, u, u} ((situation C).totalRingSheaf P) F) V j x

end CategoryTheory.CocontinuousSimplicialSite.CartesianSlice
