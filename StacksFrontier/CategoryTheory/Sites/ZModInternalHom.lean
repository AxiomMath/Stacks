module

public import Mathlib.Algebra.Module.ZMod
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The internal Hom of sheaves of `ℤ/n`-modules is the abelian internal Hom

For sheaves of `ℤ/n`-modules `G` and `F` on a site, a morphism of the underlying abelian sheaves
`G|_U ⟶ F|_U` is automatically `ℤ/n`-linear. So the abelian sheaf underlying the internal Hom
`ℋom_{ℤ/n}(G, F)` (`Stacks.ConstantSheaf.moduleSheafHom`) is the abelian internal Hom
`ℋom_ℤ(G, F)` (`internalHomSheaf`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe v u

namespace Stacks.ModuleInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (n : ℕ)
  (G F : Sheaf K (ModuleCat.{max u v} (ZMod n)))

/-- Forgetting the `ℤ/n`-linearity of local morphisms. -/
def zmodHomForgetNatTrans :
    ((sheafCompose K (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).obj
        (moduleSheafHom K (ZMod n) G F)).obj ⟶
      (internalHomSheaf K (Stacks.AbelianInternalHom.toAb K G)
        (Stacks.AbelianInternalHom.toAb K F)).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := fun (α : (K.overPullback (ModuleCat.{max u v} (ZMod n)) U.unop).obj G ⟶
          (K.overPullback (ModuleCat.{max u v} (ZMod n)) U.unop).obj F) =>
        Functor.whiskerRight α.hom (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := rfl

/-- An additive morphism `G|_U ⟶ F|_U` of the underlying abelian presheaves, regarded as a
`ℤ/n`-linear morphism of sheaves of `ℤ/n`-modules on `C/U`. -/
def zmodHomLift (U : Cᵒᵖ)
    (β : (Over.forget U.unop).op ⋙ (Stacks.AbelianInternalHom.toAb K G).obj ⟶
      (Over.forget U.unop).op ⋙ (Stacks.AbelianInternalHom.toAb K F).obj) :
    (K.overPullback (ModuleCat.{max u v} (ZMod n)) U.unop).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} (ZMod n)) U.unop).obj F :=
  ObjectProperty.homMk
    { app W := ModuleCat.ofHom
        ({ toFun := fun (x : G.obj.obj (op W.unop.left)) =>
              ((β.app W).hom x : F.obj.obj (op W.unop.left))
           map_add' := fun a b => (β.app W).hom.map_add a b
           map_smul' := fun r x =>
             let f : (G.obj.obj (op W.unop.left) : Type (max u v)) →+
                 (F.obj.obj (op W.unop.left) : Type (max u v)) := (β.app W).hom
             ZMod.map_smul f r x } :
          (G.obj.obj (op W.unop.left) : Type (max u v)) →ₗ[ZMod n]
            (F.obj.obj (op W.unop.left) : Type (max u v)))
      naturality W W' a := by
        ext x
        exact ConcreteCategory.congr_hom (β.naturality a) x }

/-- On each object `U`, forgetting `ℤ/n`-linearity is a bijection from morphisms `G|_U ⟶ F|_U` of
sheaves of `ℤ/n`-modules to additive morphisms of the underlying abelian presheaves. -/
lemma bijective_zmodHomForgetNatTrans_app (U : Cᵒᵖ) :
    Function.Bijective ((zmodHomForgetNatTrans K n G F).app U).hom := by
  refine ⟨fun a b h => ?_, fun β => ⟨zmodHomLift K n G F U β, rfl⟩⟩
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ModuleCat.hom_ext
    (LinearMap.ext fun x => ?_)))
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h W) x

/-- The natural transformation `zmodHomForgetNatTrans` is an isomorphism. -/
instance isIso_zmodHomForgetNatTrans : IsIso (zmodHomForgetNatTrans K n G F) := by
  have : ∀ U, IsIso ((zmodHomForgetNatTrans K n G F).app U) := fun U => by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_zmodHomForgetNatTrans_app K n G F U
  exact NatIso.isIso_of_isIso_app _

/-- **The abelian sheaf underlying `ℋom_{ℤ/n}(G, F)` is `ℋom_ℤ(G, F)`.** -/
def zmodHomForgetIso :
    (sheafCompose K (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).obj
        (moduleSheafHom K (ZMod n) G F) ≅
      internalHomSheaf K (Stacks.AbelianInternalHom.toAb K G)
        (Stacks.AbelianInternalHom.toAb K F) :=
  ObjectProperty.isoMk _ (asIso (zmodHomForgetNatTrans K n G F))

/-- On sections over `U`, the isomorphism `zmodHomForgetIso` sends a morphism `α : G|_U ⟶ F|_U` to
its whiskering with the forgetful functor to abelian groups. -/
lemma zmodHomForgetIso_hom_hom_app_apply (U : Cᵒᵖ)
    (α : (K.overPullback (ModuleCat.{max u v} (ZMod n)) U.unop).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} (ZMod n)) U.unop).obj F) :
    ((zmodHomForgetIso K n G F).hom.hom.app U).hom α =
      Functor.whiskerRight α.hom (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v}) :=
  rfl

end Stacks.ModuleInternalHom
