module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableTransitionCoherence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianSections
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The transitions of a sheaf of modules on `(C/K)_total`, on sections

Let `(C, O_C)` be a ringed site and `K` a simplicial semi-representable object of `C`, with the
total site `(C/K)_total` of Stacks 0D9W and its sheaf of rings `O = a⁻¹O_C`. For a sheaf of
`O`-modules `M` and a simplex map `φ : [m] ⟶ [n]`, the transition `f_φ^*M_m ⟶ M_n` of Stacks 09WF
is defined as a mate under the adjunction of the morphism of ringed topoi `f_φ`. Reading `f_φ^*`
as restriction along the relocalization functor `r_φ : C/K_n ⥤ C/K_m`
(`CategoryTheory.SimplicialSemiRepresentable.transitionPullbackModulesIso`), this file computes
the transition on sections: it is restriction along the cross-fibre arrow `(φ, 𝟙)` of the total
category.

## Main results

All in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

* `transitionSheafAdjunction_homEquiv_moduleSheafFunctor_map`: transposes along
  `transitionRestrictionPushforwardAdjunction` lie over the transposes of sheaves of sets.
* `transitionRestrictionPushforwardAdjunction_homEquiv_transition`: the transition, read through
  restriction along `r_φ`, transposes to the direct-image transition.
* `transitionSheafAdjunction_homEquiv_symm_restrictTransition_hom_app`: the inverse transpose of
  the direct-image transition of a sheaf of sets is restriction along the cross-fibre arrow.
* `moduleSheafFunctor_map_transitionPullbackModulesIso_inv_comp_transition`: the transition of a
  sheaf of modules is the inverse transpose of the direct-image transition of its underlying
  sheaf of sets.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SemiRepresentable

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **Transposes along `r_φ^{-1} ⊣ (f_φ)_*` lie over the transposes of sheaves of sets** along
the restriction–direct-image adjunction of `r_φ`: forgetting the module structure carries the
unit of the first to the unit of the second
(`CategoryTheory.SimplicialSemiRepresentable.moduleSheafFunctor_map_unit_app_comm`), and both
functors of the first adjunction to those of the second, through the identity commutation
isomorphisms. -/
@[sga "4 IV 11.2.2" "special case"]
theorem transitionSheafAdjunction_homEquiv_moduleSheafFunctor_map
    {m n : SimplexCategory} (φ : m ⟶ n) {M : SheafOfModules.{u} (componentRing X K m)}
    {N : SheafOfModules.{u} (componentRing X K n)}
    (T : (transitionRestriction X K φ).obj M ⟶ N) :
    (transitionSheafAdjunction X K φ).homEquiv _ _
        ((moduleSheafTransitionRestrictionIso X K φ).hom.app M ≫
          (Sheaf.moduleSheafFunctor (componentRing X K n)).map T) =
      (Sheaf.moduleSheafFunctor (componentRing X K m)).map
          ((transitionRestrictionPushforwardAdjunction X K φ).homEquiv M N T) ≫
        (moduleSheafTransitionPushforwardIso X K φ).inv.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← moduleSheafFunctor_map_unit_app_comm, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1

/-- **The transition, transposed along `r_φ^{-1} ⊣ (f_φ)_*`, is the direct-image transition.**
Composed with the identification `transitionPullbackModulesIso` of `f_φ^*` with restriction along
`r_φ`, the transition `f_φ^*M_m ⟶ M_n` of Stacks 09WF transposes to the direct-image transition,
read in the direct image of the transition morphism of ringed topoi. -/
theorem transitionRestrictionPushforwardAdjunction_homEquiv_transition
    {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} ((situation X.J K).totalRingSheaf (structureSheaf X K))) :
    (transitionRestrictionPushforwardAdjunction X K φ).homEquiv _ _
        ((transitionPullbackModulesIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
          ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app M) =
      (situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M ≫
        ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
          φ).toModulesPushforwardIso.inv.app _ := by
  refine (Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp
    ((situation X.J K).transitionPullbackAdj (structureSheaf X K) φ)
    (transitionRestrictionPushforwardAdjunction X K φ) (transitionPullbackModulesIso X K φ) rfl
    _ _).trans ?_
  have h : ((situation X.J K).transitionPullbackAdj (structureSheaf X K) φ).homEquiv _ _
        ((situation X.J K).fiberTransitionModules (structureSheaf X K) φ M) ≫
        ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
          φ).toModulesPushforwardIso.hom.app _ =
      (situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M :=
    (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).symm.trans
      ((situation X.J K).fiberTransitionModules_adj (structureSheaf X K) φ M)
  refine (Iso.eq_comp_inv (((situation X.J K).transitionRingedToposHom (structureSheaf X K)
    φ).toModulesPushforwardIso.app _)).2 ?_
  exact (congrArg (fun t => ((situation X.J K).transitionPullbackAdj (structureSheaf X K)
      φ).homEquiv _ _ t ≫ ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
          φ).toModulesPushforwardIso.hom.app _)
    ((situation X.J K).componentModuleTransition_app (structureSheaf X K) φ M)).trans h

/-- **The inverse transpose of the direct-image transition of a sheaf of sets**, along the
restriction–direct-image adjunction of `r_φ`, is restriction along the cross-fibre arrow
`(φ, 𝟙)` on sections. -/
theorem transitionSheafAdjunction_homEquiv_symm_restrictTransition_hom_app
    {m n : SimplexCategory} (φ : m ⟶ n) (F : Sheaf (situation X.J K).totalTopology (Type u))
    (V : ((CocontinuousSimplicialSite.situation (simplicialSite X.J K)).component n)) :
    (((transitionSheafAdjunction X K φ).homEquiv _ _).symm
        (((situation X.J K).restrictTransition φ).app F)).hom.app (op V) =
      F.obj.map ((Grothendieck.ιNatTrans
          (F := (simplicialSite X.J K).underlying) φ.op).app V).op := by
  have h₄ : (((transitionSheafAdjunction X K φ).homEquiv _ _).symm
        (((situation X.J K).restrictTransition φ).app F)).hom =
      (((transitionSiteFunctor X K φ).op.ranAdjunction (Type u)).homEquiv _ _).symm
        (((situation X.J K).restrictTransition φ).app F).hom := by
    refine (Equiv.eq_symm_apply _).2 ?_
    refine (Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom (transitionSiteFunctor X K φ)
      (Type u) (componentRingedTopos X K n).J (componentRingedTopos X K m).J _).symm.trans ?_
    exact Sheaf.hom_ext_iff.1 (((transitionSheafAdjunction X K φ).homEquiv _ _).apply_symm_apply _)
  rw [h₄]
  exact SimplicialSiteSituation.restrictTransition_inr_app (simplicialSite X.J K) φ F V

/-- **The transition of a sheaf of modules on the total site is the inverse transpose of the
direct-image transition of its underlying sheaf of sets.** Read through the identification of
`f_φ^*` with restriction along `r_φ` and with the module structure forgotten, the transition
`f_φ^*M_m ⟶ M_n` of Stacks 09WF is the inverse transpose along the restriction–direct-image
adjunction of `r_φ` of the transition of Stacks 09WF of the underlying sheaf of sets. -/
theorem moduleSheafFunctor_map_transitionPullbackModulesIso_inv_comp_transition
    {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{u} ((situation X.J K).totalRingSheaf (structureSheaf X K))) :
    (moduleSheafTransitionRestrictionIso X K φ).hom.app
        (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
      (Sheaf.moduleSheafFunctor (componentRing X K n)).map
        ((transitionPullbackModulesIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
          ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app M) =
      ((transitionSheafAdjunction X K φ).homEquiv _ _).symm
        (((situation X.J K).restrictTransition φ).app
          (Sheaf.moduleSheaf.{u, u, u} ((situation X.J K).totalRingSheaf (structureSheaf X K))
            M)) := by
  have h₁ := transitionSheafAdjunction_homEquiv_moduleSheafFunctor_map X K φ
    ((transitionPullbackModulesIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
          ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app M)
  rw [transitionRestrictionPushforwardAdjunction_homEquiv_transition] at h₁
  have h₂ : (Sheaf.moduleSheafFunctor (componentRing X K m)).map
        (((situation X.J K).transitionRingedToposHom (structureSheaf X K)
          φ).toModulesPushforwardIso.inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M)) ≫
      (moduleSheafTransitionPushforwardIso X K φ).inv.app
        (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M) =
        𝟙 _ := rfl
  have h₃ : (Sheaf.moduleSheafFunctor (componentRing X K m)).map
        ((situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M ≫
          ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
            φ).toModulesPushforwardIso.inv.app
            (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M)) ≫
        (moduleSheafTransitionPushforwardIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M) =
      (Sheaf.moduleSheafFunctor (componentRing X K m)).map
        ((situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M) := by
    exact (congrArg (· ≫ _) ((Sheaf.moduleSheafFunctor (componentRing X K m)).map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.comp_id _)))
  exact (Equiv.eq_symm_apply _).2 (h₁.trans (h₃.trans
    ((situation X.J K).moduleSheafFunctor_map_restrictTransitionModules_app (structureSheaf X K)
      φ M)))

end CategoryTheory.SimplicialSemiRepresentable

end
