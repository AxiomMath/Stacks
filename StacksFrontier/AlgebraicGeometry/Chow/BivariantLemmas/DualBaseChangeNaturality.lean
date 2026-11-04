module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility

/-!
# The dual base-change map is natural in the module

Let `g : W ⟶ Y` be a morphism of schemes and `c : M' ⟶ M` a morphism of modules on `Y`. The dual
base-change map `Stacks.Chow.pullbackDualMap` of [Stacks Project, Tag 0GMX] intertwines
`g^*(c^∨)` with `(g^*c)^∨`, and the pulled-back evaluation pairing is natural in the same way.

## Main results

* `Stacks.Chow.pullbackEvaluation_naturality`, `Stacks.Chow.pullbackDualMap_naturality` — the
  pulled-back evaluation pairing and the dual base-change map are natural in the module.

## Implementation notes

As for `Stacks.Chow.pullbackEvaluation_comp` and `Stacks.Chow.pullbackDualMap_comp`, the pairing
identity is checked on the canonical images of local sections
(`Stacks.Chow.tensor_hom_ext_of_pullbackUnit`), and the map identity is read off it by
`Stacks.Chow.pullbackDualMap_eval` and extensionality for morphisms into a dual module
(`Stacks.Chow.hom_ext_dualSheaf_of_terminal`).

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.PullbackUnitGenerators
open scoped TensorProduct

universe u

namespace Stacks.Chow

noncomputable section

variable {W Y : Scheme.{u}}

/-! ### Naturality in the module -/

/-- **The pulled-back evaluation pairing is natural in the module.** For `c : M' ⟶ M` and
`g : W ⟶ Y`, the pairing `g^*(M^∨) ⊗ g^*M' ⟶ 𝒪_W` obtained from the pulled-back evaluation
pairing of `M` through `g^*c` is the one obtained from the pulled-back evaluation pairing of `M'`
through `g^*(c^∨)`: both send `s ⊗ m` to `s(c(m))`. -/
theorem pullbackEvaluation_naturality (g : W ⟶ Y) {M M' : Y.Modules} (c : M' ⟶ M) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 _, (modulePullback g.toLRSHom.toShHom).map c) : (_, _) ⟶ (_, _)) ≫
        pullbackEvaluation g M =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (((modulePullback g.toLRSHom.toShHom).map (dualMap c), 𝟙 _) : (_, _) ⟶ (_, _)) ≫
        pullbackEvaluation g M' := by
  refine tensor_hom_ext_of_pullbackUnit g (dualSheaf M) M' (fun U s m => ?_)
  refine (comp_val_app _ _ _ _).trans ?_
  refine Eq.trans ?_ (comp_val_app _ _ _ _).symm
  refine (val_app_congr _ _ ((tensorSheafMap_tensorSheafPure _ _ _ _ _).trans
    (tensorSheafPure_congr _ _ _ rfl (pullback_map_unit_app g c U m)))).trans ?_
  refine Eq.trans ?_ (val_app_congr _ _ ((tensorSheafMap_tensorSheafPure _ _ _ _ _).trans
    (tensorSheafPure_congr _ _ _ (pullback_map_unit_app g (dualMap c) U s) rfl))).symm
  exact (pullbackEvaluation_unit_tmul g M U s _).trans
    (pullbackEvaluation_unit_tmul g M' U ((dualMap c).val.app (op U) s) m).symm

/-- **The dual base-change map is natural in the module.** For `c : M' ⟶ M` and `g : W ⟶ Y`,
the dual base-change maps `g^*(M^∨) ⟶ (g^*M)^∨` and `g^*(M'^∨) ⟶ (g^*M')^∨` of
[Stacks Project, Tag 0GMX] intertwine `g^*(c^∨)` and `(g^*c)^∨`. -/
theorem pullbackDualMap_naturality (g : W ⟶ Y) {M M' : Y.Modules} (c : M' ⟶ M) :
    (modulePullback g.toLRSHom.toShHom).map (dualMap c) ≫ pullbackDualMap g M' =
      pullbackDualMap g M ≫ dualMap ((modulePullback g.toLRSHom.toShHom).map c) := by
  refine hom_ext_dualSheaf_of_terminal (fun V a b => ?_)
  have hnat := congrArg (fun φ => φ.val.app (op V)
      (tensorSheafPure W ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M))
        ((modulePullback g.toLRSHom.toShHom).obj M') V (a ⊗ₜ[W.presheaf.obj (op V)] b)))
    (pullbackEvaluation_naturality g c)
  have hL := (comp_val_app _ _ _ _).symm.trans (hnat.symm.trans (comp_val_app _ _ _ _))
  refine (pullbackDualMap_eval g M' V _ b).trans ?_
  refine (val_app_congr (pullbackEvaluation g M') V (tensorSheafMap_tensorSheafPure
    ((modulePullback g.toLRSHom.toShHom).map (dualMap c)) (𝟙 _) V a b)).symm.trans ?_
  refine hL.trans ?_
  refine (val_app_congr (pullbackEvaluation g M) V (tensorSheafMap_tensorSheafPure (𝟙 _)
    ((modulePullback g.toLRSHom.toShHom).map c) V a b)).trans ?_
  exact (pullbackDualMap_eval g M V a _).symm

end

end Stacks.Chow

end
