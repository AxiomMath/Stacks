module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Pullback of presheaves of modules along a functor into a large category

For a functor `F : C ⥤ D` from a small category to a category whose morphisms live in the
universe of the objects of `C`, and a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, the
pushforward of presheaves of modules along `φ` has a left adjoint. No smallness hypothesis is
imposed on `D`.

## Main results

* `Stacks.ModulePullback.isRightAdjoint_pushforward`: the pushforward of presheaves of modules
  along `φ : S ⟶ F.op ⋙ R` has a left adjoint.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Functor PresheafOfModules

namespace Stacks.ModulePullback

variable {C : Type u} [SmallCategory C] {D : Type v} [Category.{u} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- Morphisms from the free presheaf of modules on the representable presheaf of `X` into the
pushforward of `M` are the sections of `M` at `F.obj X`. -/
public noncomputable def pushforwardFreeYonedaEquiv (M : PresheafOfModules.{u} R) (X : C) :
    ((free S).obj (yoneda.obj X) ⟶ (pushforward φ).obj M) ≃ (M.obj (op (F.obj X)) : Type u) :=
  freeYonedaEquiv

/-- The identification of `Stacks.ModulePullback.pushforwardFreeYonedaEquiv` is natural in the
presheaf of modules. -/
public theorem pushforwardFreeYonedaEquiv_comp {M N : PresheafOfModules.{u} R} (X : C)
    (g : M ⟶ N) (m : (free S).obj (yoneda.obj X) ⟶ (pushforward φ).obj M) :
    pushforwardFreeYonedaEquiv φ N X (m ≫ (pushforward φ).map g)
      = ConcreteCategory.hom (g.app (op (F.obj X))) (pushforwardFreeYonedaEquiv φ M X m) :=
  freeYonedaEquiv_comp m ((pushforward φ).map g)

/-- The partial left adjoint of `PresheafOfModules.pushforward φ` is defined on the free
presheaf of modules on a representable, where it takes the value prescribed by the functor. -/
public noncomputable def pushforwardCorepresentableBy (X : C) :
    (pushforward φ ⋙ coyoneda.obj (op ((free S).obj (yoneda.obj X)))).CorepresentableBy
      ((free R).obj (yoneda.obj (F.obj X))) where
  homEquiv {M} := freeYonedaEquiv.trans (pushforwardFreeYonedaEquiv φ M X).symm
  homEquiv_comp {M N} g f := (pushforwardFreeYonedaEquiv φ N X).injective (by
    change (pushforwardFreeYonedaEquiv φ N X)
        ((pushforwardFreeYonedaEquiv φ N X).symm (freeYonedaEquiv (f ≫ g))) =
      (pushforwardFreeYonedaEquiv φ N X)
        ((pushforwardFreeYonedaEquiv φ M X).symm (freeYonedaEquiv f) ≫ (pushforward φ).map g)
    rw [Equiv.apply_symm_apply, pushforwardFreeYonedaEquiv_comp, Equiv.apply_symm_apply,
      freeYonedaEquiv_comp])

/-- The partial left adjoint of `PresheafOfModules.pushforward φ` is defined on the free
presheaves on representables. -/
public theorem pullbackObjIsDefined_free_yoneda (X : C) :
    pullbackObjIsDefined φ ((free S).obj (yoneda.obj X)) :=
  (pushforwardCorepresentableBy φ X).isCorepresentable

/-- The partial left adjoint of `PresheafOfModules.pushforward φ` is defined on every presheaf
of modules. -/
public theorem pullbackObjIsDefined_eq_top : pullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _) <;>
    exact leftAdjointObjIsDefined_colimit _ fun _ ↦ pullbackObjIsDefined_free_yoneda _ _

/-- The pushforward of presheaves of modules along a morphism of presheaves of rings over a
functor out of a small category has a left adjoint, with no smallness hypothesis on the
target. -/
public instance isRightAdjoint_pushforward : (pushforward.{u} φ).IsRightAdjoint :=
  isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (pullbackObjIsDefined_eq_top φ)

end Stacks.ModulePullback

end
