module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleUnderlying
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphismAdjunction

/-!
# Cartesian modules over a cartesian structure sheaf

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site
whose underlying sheaf of sets is cartesian. Then every simplicial transition
`f_φ : (Sh(C_n), O_n) ⟶ (Sh(C_m), O_m)` has invertible structure map `f_φ⁻¹O_m ⟶ O_n`, so the
pullback of modules along it is the inverse image on underlying sheaves, and the module
transition `f_φ^*F_m ⟶ F_n` of a sheaf of `O`-modules `F` is the transition `f_φ⁻¹F_m ⟶ F_n` of
its underlying sheaf of sets. Hence `F` is a cartesian `O`-module (Stacks 07TF (2)) exactly when
its underlying sheaf of sets is cartesian (Stacks 07TF (1)).

## Main results

* `isIso_fiberTransitionModules_iff_cartesianModuleIffCartesianSheaf`: a module transition is
  invertible exactly when the transition of the underlying sheaf of sets is.
* `isCartesianModule_iff_isCartesianSheaf_cartesianModuleIffCartesianSheaf`: cartesian modules are
  the modules with cartesian underlying sheaf.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local implicit_reducible] CategoryTheory.SimplicialSiteSituation.restrict
  CategoryTheory.SimplicialSiteSituation.componentRingedTopos

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **Stacks 09WF, modules versus sets.** Along a simplicial transition with invertible structure
map, the module transition `f_φ^*F_m ⟶ F_n` is invertible exactly when the transition
`f_φ⁻¹F_m ⟶ F_n` of the underlying sheaf of sets is. -/
theorem isIso_fiberTransitionModules_iff_cartesianModuleIffCartesianSheaf
    {m n : SimplexCategory} (φ : m ⟶ n)
    [IsIso (S.transitionRingedToposHom O φ).fSharpInverseImage]
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    IsIso (S.fiberTransitionModules O φ M) ↔
      IsIso ((S.fiberTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) := by
  have hft : (S.fiberTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) =
      ((S.transitionMorphism φ).adj.homEquiv _ _).symm
        ((S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M)) := by
    rw [← S.fiberTransition_adj φ (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M),
      Equiv.symm_apply_apply]
  have hη := Iso.isIso_hom ((RingedToposHom.pullbackUnitUnderlyingIso
    (S.transitionRingedToposHom O φ)).app
      ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj M))
  have e : (RingedToposHom.pullbackUnitUnderlyingIso
        (S.transitionRingedToposHom O φ)).hom.app
          ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj M) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (S.componentRingedTopos O n).J) (S.componentRingedTopos O n).O)).map
            (S.fiberTransitionModules O φ M) =
      ((S.transitionRingedToposHom O φ).toToposHom.adj.homEquiv _ _).symm
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)).map
            (S.restrictTransitionModulesApp O φ M)) :=
    open RingedToposHom in
    moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv_symm_ringedToposMorphismAdjunction
      (S.transitionRingedToposHom O φ) _ _ (S.restrictTransitionModulesApp O φ M)
  have hiff : IsIso (((S.transitionRingedToposHom O φ).toToposHom.adj.homEquiv _ _).symm
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O)).map
            (S.restrictTransitionModulesApp O φ M))) ↔
      IsIso (((S.transitionMorphism φ).adj.homEquiv _ _).symm
        ((S.restrictTransition φ).app (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M))) :=
    Iff.rfl
  rw [hft, ← hiff, ← e]
  exact (isIso_iff_of_reflects_iso _ (Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (S.componentRingedTopos O n).J) (S.componentRingedTopos O n).O))).symm.trans
    (@isIso_comp_left_iff _ _ _ _ _ _ _ hη).symm

/-- **Stacks 07TF, cartesian modules versus cartesian sheaves.** Over a structure sheaf whose
underlying sheaf of sets is cartesian, a sheaf of `O`-modules is cartesian exactly when its
underlying sheaf of sets is. -/
theorem isCartesianModule_iff_isCartesianSheaf_cartesianModuleIffCartesianSheaf
    (hO : S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O))
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    S.IsCartesianModule O M ↔
      S.IsCartesianSheaf (Sheaf.moduleSheaf.{u, u, u} (S.totalRingSheaf O) M) := by
  refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun φ => ?_
  have := S.isIso_transitionRingedToposHom_fSharpInverseImage O hO φ
  exact S.isIso_fiberTransitionModules_iff_cartesianModuleIffCartesianSheaf O φ M

end CategoryTheory.SimplicialSiteSituation

end
