module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitTranspose
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition

/-!
# The structure sheaf of the total site is cartesian

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on
its total site. The restriction of `O`, viewed as a module over itself, to the degree-`n`
component is the structure sheaf `O_n` of that component, and for a simplex map `φ : m ⟶ n`
the transition `f_φ^*O_m ⟶ O_n` of Stacks 09WF is the unit comparison `f_φ^*O_m ≅ O_n` of
Stacks 03LU: its transpose `O_m ⟶ f_{φ*}O_n` is the structure map of `f_φ`. So `O` is a
cartesian module in the sense of Stacks 07TF (2).

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleRestriction_obj_unit_unitTransition`:
  the restriction of the unit module to a component is the component structure sheaf, on the
  nose.
* `CategoryTheory.SimplicialSiteSituation.isIso_fiberTransitionModules_unit_unitTransition`:
  the transition of the unit module along every simplex map is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The restriction of the unit module of the total site to the degree-`n` component is, on the
nose, the structure sheaf of that component viewed as a module over itself. -/
theorem componentModuleRestriction_obj_unit_unitTransition (n : SimplexCategory) :
    (S.componentModuleRestriction (S.totalRingSheaf O) n).obj
        (SheafOfModules.unit (S.totalRingSheaf O)) =
      SheafOfModules.unit (componentRingSheaf S (S.totalRingSheaf O) n) :=
  rfl

/-- **The structure sheaf of the total site is cartesian along every simplex map.** The
transition `f_φ^*O_m ⟶ O_n` of the unit module is the unit comparison of Stacks 03LU, read
through the identifications of the restricted unit modules with the component structure
sheaves. -/
theorem isIso_fiberTransitionModules_unit_unitTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (S.fiberTransitionModules O φ (SheafOfModules.unit (S.totalRingSheaf O))) :=
  (S.transitionRingedToposHom O φ).isIso_homEquiv_symm_of_eq_unit
    (S.componentModuleRestriction_obj_unit_unitTransition O m)
    (S.componentModuleRestriction_obj_unit_unitTransition O n)
    (S.restrictTransitionModulesApp O φ _)
    (heq_of_eq (S.transitionRingedToposHom_fSharpRing_forget O φ).symm)

end CategoryTheory.SimplicialSiteSituation

end
