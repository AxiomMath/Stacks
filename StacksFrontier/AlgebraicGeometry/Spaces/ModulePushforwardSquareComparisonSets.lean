module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnit
public import StacksFrontier.CategoryTheory.Adjunction.MateSheafSections

/-!
# The comparison of composite direct images of modules on underlying sheaves of sets

For a commutative square `i ≫ f = f' ≫ g` of algebraic spaces, the comparison
`i_* f_* ⟶ f'_* g_*` of the two composite direct images of modules (Stacks 03LU) is, on
sections, the comparison of the composite direct images of the underlying sheaves of sets of
Stacks 03G2, part (3).

## Main results

* `AlgebraicGeometry.Space.modulePushforwardSquare_val_app`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The transport of direct images of modules along an equality of morphisms of algebraic
spaces is, on underlying sheaves of sets, the transport of the direct images of sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToHom_modulePushforward_congr_app {k₁ k₂ : X' ⟶ Y}
    (h : k₁ = k₂) (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) h)).app N) =
      (eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
        h)).app ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N) := by
  subst h
  simp only [eqToHom_refl, NatTrans.id_app]
  exact (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map_id _

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_eqToHom_modulePushforward_congr_app` on
sections. -/
theorem eqToHom_modulePushforward_congr_app_val_app {k₁ k₂ : X' ⟶ Y} (h : k₁ = k₂)
    (N : Modules.{u, u} B S hS X'.1 X'.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ((modulePushforward B S hS k₁).obj N).val.obj W) :
    ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) h)).app N).val.app W z =
      ((eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
        h)).app ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W z :=
  (Stacks.ChartUnitComp.moduleSheafFunctor_map_hom_app_apply
      ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) h)).app N) W z).symm.trans
    (Sheaf.hom_congr_app_apply
      (moduleSheafFunctor_map_eqToHom_modulePushforward_congr_app B S hS h N) W z)

/-- **The comparison of the two composite direct images of modules around a commutative square
is, on sections, the comparison of the two composite direct images of sheaves of sets** of
Stacks 03G2, part (3). -/
theorem modulePushforwardSquare_val_app (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ((modulePushforward B S hS f).obj ((modulePushforward B S hS i).obj N)).val.obj W) :
    ((modulePushforwardCompIso B S hS i f).hom.app N ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) w)).app N ≫
        (modulePushforwardCompIso B S hS f' g).inv.app N).val.app W z =
      (((smallToposMorphismTypeU_comp B S hS i f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
          w) ≫
        (smallToposMorphismTypeU_comp B S hS f' g).inv).app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W z := by
  refine (Stacks.CategoryTheory.SheafOfModules.comp₃_val_app
    ((modulePushforwardCompIso B S hS i f).hom.app N)
    ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) w)).app N)
    ((modulePushforwardCompIso B S hS f' g).inv.app N) W z).trans ?_
  refine (modulePushforwardCompIso_inv_app_val_app B S hS f' g N W
    (((eqToHom (congrArg (fun k : X' ⟶ Y => modulePushforward B S hS k) w)).app N).val.app W
      (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W z))).trans ?_
  refine (congrArg (fun t => ((smallToposMorphismTypeU_comp B S hS f' g).inv.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W t)
    (eqToHom_modulePushforward_congr_app_val_app B S hS w N W
      (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W z))).trans ?_
  refine (congrArg (fun t => ((smallToposMorphismTypeU_comp B S hS f' g).inv.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W
      (((eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
        w)).app ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W t))
    (modulePushforwardCompIso_hom_app_val_app B S hS i f N W z)).trans ?_
  exact (Stacks.CategoryTheory.Sheaf.comp₃_app_hom_app (smallToposMorphismTypeU_comp B S hS i f).hom
    (eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward) w))
    (smallToposMorphismTypeU_comp B S hS f' g).inv
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N) W z).symm

end AlgebraicGeometry.Space

end
