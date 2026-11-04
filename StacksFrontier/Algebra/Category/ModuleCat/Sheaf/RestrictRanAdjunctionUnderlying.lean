module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction

/-!
# The adjunction between restriction and direct image along a cocontinuous functor, underneath

The adjunction `Stacks.SheafOfModules.RestrictRan.sheafAdjunction` between restriction of sheaves of
modules along a continuous and cocontinuous functor and the direct image along it is, on
underlying presheaves of abelian groups, the right Kan extension adjunction: this file records it
for the counit and for the transposition.

## Main results

* `Stacks.SheafOfModules.RestrictRan.toPresheaf_map_adjunction_counit_app`.
* `Stacks.SheafOfModules.RestrictRan.sheafAdjunction_counit_app_val`.
* `Stacks.SheafOfModules.RestrictRan.sheafAdjunction_homEquiv_val`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂

namespace Stacks.SheafOfModules.RestrictRan

section Presheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (T : Yᵒᵖ ⥤ RingCat.{r})
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]

/-- **The counit of the adjunction on presheaves of modules is, on underlying presheaves of
abelian groups, the counit of the Kan-extension adjunction.** -/
theorem toPresheaf_map_adjunction_counit_app (N : PresheafOfModules.{v} (w.op ⋙ T)) :
    (PresheafOfModules.toPresheaf _).map ((adjunction.{v} w T).counit.app N) =
      (w.op.ranAdjunction AddCommGrpCat.{v}).counit.app N.presheaf := by
  rw [← Adjunction.homEquiv_symm_id]
  simp only [adjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact ((w.op.ranAdjunction AddCommGrpCat.{v}).homEquiv_symm_id _).trans rfl

end Presheaf

section Sheaf

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY] (OY : Sheaf JY RingCat.{r})
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]

/-- **The counit of the adjunction on sheaves of modules is the counit on presheaves.** -/
theorem sheafAdjunction_counit_app_val (N : _root_.SheafOfModules.{v} (ringSheaf w JX JY OY)) :
    ((sheafAdjunction.{v} w JX JY OY).counit.app N).val =
      (adjunction.{v} w OY.obj).counit.app N.val := by
  change (_root_.SheafOfModules.forget.{v} (ringSheaf w JX JY OY)).map
    ((sheafAdjunction.{v} w JX JY OY).counit.app N) = _
  refine (Adjunction.map_restrictFullyFaithful_counit_app (adjunction.{v} w OY.obj)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} OY)
    (_root_.SheafOfModules.fullyFaithfulForget.{v} (ringSheaf w JX JY OY)) _ _ N).trans ?_
  exact (Category.id_comp _).trans ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
    (Category.id_comp _))

/-- **The bijection of the adjunction on sheaves of modules is the bijection on presheaves.** -/
theorem sheafAdjunction_homEquiv_val {M : _root_.SheafOfModules.{v} OY}
    {N : _root_.SheafOfModules.{v} (ringSheaf w JX JY OY)}
    (a : (_root_.SheafOfModules.pushforward.{v} (F := w) (R := OY) (S := ringSheaf w JX JY OY)
      (𝟙 (ringSheaf w JX JY OY))).obj M ⟶ N) :
    ((sheafAdjunction.{v} w JX JY OY).homEquiv M N a).val =
      (adjunction.{v} w OY.obj).homEquiv M.val N.val a.val := by
  exact (congrArg (fun f : M ⟶ (pushforwardCocontinuous.{v} w (sheafUnit w JX JY OY)).obj N =>
      f.val) ((sheafAdjunction.{v} w JX JY OY).homEquiv_unit M N a)).trans
    ((congrArg (· ≫ (ranPushforward.{v} w (unitRingHom w (T := OY.obj))).map a.val)
      (sheafAdjunction_unit_app_val.{v} w JX JY OY M)).trans
      (Adjunction.homEquiv_unit _ _ _ _).symm)

end Sheaf

end Stacks.SheafOfModules.RestrictRan
