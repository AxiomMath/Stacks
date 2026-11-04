module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseBSummand
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# The module transitions on the total site, on sections

For a module `M` on the total ringed topos of a simplicial semi-representable object, the
transition maps between its components are described on sections: they are the restriction maps
of the module sheaf of `M` along the morphisms of the total site.

## Main definitions

* `transitionOfRestriction`: The pullback transition of `M`, read as restriction along `r_φ`.

## Main results

* `moduleSheafFunctor_map_transitionOfRestriction_app_apply`: On sections over `V`, the
  transition of `M` along `φ` is the restriction map of the module sheaf of `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable (X : RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- Under the restriction–pushforward adjunction along `φ`, the pullback transition of `M`
corresponds to `restrictTransitionModulesApp` followed by the inverse of the pushforward
comparison isomorphism. -/
theorem homEquiv_transitionPullbackModulesIso_inv_app_comp_componentModulesTransition_app
    {m n : SimplexCategory} (φ : m ⟶ n)
    (M : ((situation X.J K).totalRingedTopos (structureSheaf X K)).Modules) :
    (transitionRestrictionPushforwardAdjunction X K φ).homEquiv _ _
        ((transitionPullbackModulesIso X K φ).inv.app
            (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
          ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app M) =
      (situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M ≫
        ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
          φ).toModulesPushforwardIso.inv.app _ := by
  refine (Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp _ _ _ rfl _ _).trans ?_
  have h1 := Adjunction.homEquiv_ofNatIsoRight_apply
    ((situation X.J K).transitionPullbackAdj (structureSheaf X K) φ)
    ((situation X.J K).transitionRingedToposHom (structureSheaf X K) φ).toModulesPushforwardIso
    (((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app M)
  have h2 := ((situation X.J K).componentModuleTransition_app (structureSheaf X K) φ M)
  have h3 := (situation X.J K).fiberTransitionModules_adj (structureSheaf X K) φ M
  exact (Iso.eq_comp_inv (((situation X.J K).transitionRingedToposHom (structureSheaf X K)
    φ).toModulesPushforwardIso.app _)).2 (h1.symm.trans ((congrArg _ h2).trans h3))

/-- The pullback transition of `M`, read as restriction along `r_φ`. -/
abbrev transitionOfRestriction {m n : SimplexCategory} (φ : m ⟶ n)
    (M : ((situation X.J K).totalRingedTopos (structureSheaf X K)).Modules) :
    (transitionRestriction X K φ).obj
        (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ⟶
      ((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M :=
  (transitionPullbackModulesIso X K φ).inv.app
      (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
    ((situation X.J K).componentModulesTransition (structureSheaf X K) φ).app M

/-- On underlying sheaves of modules, the adjoint transpose of `transitionOfRestriction X K φ M`
under `transitionSheafAdjunction X K φ` is the image of `restrictTransitionModulesApp` followed
by the pushforward comparison isomorphisms. -/
theorem sheafAdjunction_homEquiv_moduleSheafFunctor_map_transitionOfRestriction
    {m n : SimplexCategory} (φ : m ⟶ n)
    (M : ((situation X.J K).totalRingedTopos (structureSheaf X K)).Modules) :
    (transitionSheafAdjunction X K φ).homEquiv
        ((Sheaf.moduleSheafFunctor (componentRing X K m)).obj
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M))
        ((Sheaf.moduleSheafFunctor (componentRing X K n)).obj
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M))
        ((moduleSheafTransitionRestrictionIso X K φ).hom.app
            (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M) ≫
          (Sheaf.moduleSheafFunctor (componentRing X K n)).map
            (transitionOfRestriction X K φ M)) =
      (Sheaf.moduleSheafFunctor (componentRing X K m)).map
          ((situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M ≫
            ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
              φ).toModulesPushforwardIso.inv.app _) ≫
        (moduleSheafTransitionPushforwardIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M) := by
  have h := homEquiv_transitionPullbackModulesIso_inv_app_comp_componentModulesTransition_app
    X K φ M
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (Sheaf.moduleSheafFunctor (componentRing X K m)).map h
  have hu := moduleSheafFunctor_map_unit_app_comm X K φ
    (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M)
  have hn := (moduleSheafTransitionPushforwardIso X K φ).hom.naturality
    (transitionOfRestriction X K φ M)
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  have hn' : ((transitionSiteFunctor X K φ).sheafPushforwardCocontinuous (Type u)
        (componentRingedTopos X K n).J (componentRingedTopos X K m).J).map
        ((Sheaf.moduleSheafFunctor (componentRing X K n)).map (transitionOfRestriction X K φ M)) =
      (moduleSheafTransitionPushforwardIso X K φ).hom.app _ ≫
        (Sheaf.moduleSheafFunctor (componentRing X K m)).map
          (((situation X.J K).transitionPushforwardModules (structureSheaf X K) φ).map
            (transitionOfRestriction X K φ M)) ≫
        (moduleSheafTransitionPushforwardIso X K φ).inv.app _ :=
    (Iso.eq_comp_inv ((moduleSheafTransitionPushforwardIso X K φ).app _)).2 hn
  rw [Functor.map_comp, ← Category.assoc, ← hu, hn', Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Category.assoc, ← Functor.map_comp, h']
  rfl

/-- On underlying sheaves of modules, `restrictTransitionModulesApp` composed with the
pushforward comparison isomorphisms is the component at `M` of the restriction transition
`restrictTransition φ` of the total site. -/
theorem moduleSheafFunctor_map_restrictTransitionModulesApp_comp
    {m n : SimplexCategory} (φ : m ⟶ n)
    (M : ((situation X.J K).totalRingedTopos (structureSheaf X K)).Modules) :
    (Sheaf.moduleSheafFunctor (componentRing X K m)).map
          ((situation X.J K).restrictTransitionModulesApp (structureSheaf X K) φ M ≫
            ((situation X.J K).transitionRingedToposHom (structureSheaf X K)
              φ).toModulesPushforwardIso.inv.app _) ≫
        (moduleSheafTransitionPushforwardIso X K φ).inv.app
          (((situation X.J K).componentModulesRestriction (structureSheaf X K) n).obj M) =
      ((situation X.J K).restrictTransition φ).app
        (Sheaf.moduleSheaf.{u, u, u}
          ((situation X.J K).totalRingSheaf (structureSheaf X K)) M) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  rfl

/-- On sections over `V`, the transition `transitionOfRestriction X K φ M` is the restriction map
of the module sheaf of `M` along the morphism of the total site induced by `φ`. -/
theorem moduleSheafFunctor_map_transitionOfRestriction_app_apply
    {m n : SimplexCategory} (φ : m ⟶ n)
    (M : ((situation X.J K).totalRingedTopos (structureSheaf X K)).Modules)
    (V : ((simplicialSite X.J K).underlying.obj (op n) : Type u))
    (y : ((Sheaf.moduleSheafFunctor (componentRing X K n)).obj ((transitionRestriction X K φ).obj
      (((situation X.J K).componentModulesRestriction (structureSheaf X K) m).obj M))).obj.obj
        (op V)) :
    ((Sheaf.moduleSheafFunctor (componentRing X K n)).map
        (transitionOfRestriction X K φ M)).hom.app (op V) y =
      (Sheaf.moduleSheaf.{u, u, u}
          ((situation X.J K).totalRingSheaf (structureSheaf X K)) M).obj.map
        ((Grothendieck.ιNatTrans (F := (simplicialSite X.J K).underlying) φ.op).app V).op y := by
  have e := congrArg (fun t => t.hom)
    ((sheafAdjunction_homEquiv_moduleSheafFunctor_map_transitionOfRestriction X K φ M).trans
      (moduleSheafFunctor_map_restrictTransitionModulesApp_comp X K φ M))
  rw [Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom] at e
  have e' := (Equiv.eq_symm_apply _).mpr e
  have e'' := congrArg (fun t => t.app (op V) y) e'
  refine e''.trans ?_
  exact ConcreteCategory.congr_hom
    (SimplicialSiteSituation.restrictTransition_inr_app (simplicialSite X.J K) φ
      (Sheaf.moduleSheaf.{u, u, u} ((situation X.J K).totalRingSheaf (structureSheaf X K)) M) V) y

end CategoryTheory.SimplicialSemiRepresentable

end
