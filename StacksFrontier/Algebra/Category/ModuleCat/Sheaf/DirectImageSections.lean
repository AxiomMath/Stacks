module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage

/-!
# Sections of a direct image of sheaves of modules, as compatible families

The direct image `SheafOfModules.directImage` along a continuous and cocontinuous functor
`f : C ⥤ D` has, over an object `x` of `D`, the compatible families of sections indexed by
`StructuredArrow x f.op` as its module of sections. This file records that identification for
the variant `SheafOfModules.directImageOfEq`, in which the structure sheaf of the source is only
equal to the restriction of that of the target, as a natural isomorphism of functors to types:
the sections over `x` of the direct image are the sections of the functor
`StructuredArrow.proj x f.op ⋙ ℱ` attached to the underlying presheaf of sets `ℱ` of the module.

It also records the elementary fact that a natural bijection between the underlying sets of two
additive functors to abelian groups, one of which is corepresented, is additive.

## Main definitions

* `SheafOfModules.directImageOfEqSectionsIso`: the sections of the direct image over `x` are the
  sections of `StructuredArrow.proj x f.op ⋙ ℱ`, naturally in the module.
* `CategoryTheory.preadditiveCoyonedaIsoOfForget`: a natural bijection between
  `Hom(X, -)` and an additive functor `Φ`, on underlying sets, is an isomorphism of functors to
  abelian groups.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe r w vC vD uC uD v u

namespace CategoryTheory

/-- **A natural bijection between a corepresented functor and an additive functor to abelian
groups is additive.** If `α : Hom(X, -) ≅ Φ` on underlying sets, naturally, then `α` at `M` sends
`a : X ⟶ M` to `Φ(a)(α(𝟙_X))` by naturality, which is additive in `a` because `Φ` is. -/
def preadditiveCoyonedaIsoOfForget {C : Type u} [Category.{v} C] [Preadditive C] (X : C)
    (Φ : C ⥤ AddCommGrpCat.{v}) [Φ.Additive]
    (α : preadditiveCoyoneda.obj (op X) ⋙ forget AddCommGrpCat ≅ Φ ⋙ forget AddCommGrpCat) :
    preadditiveCoyoneda.obj (op X) ≅ Φ :=
  have key : ∀ (M : C) (a : X ⟶ M),
      α.hom.app M a = Φ.map a (α.hom.app X (𝟙 X)) := fun M a => by
    have h : α.hom.app M a = α.hom.app M (𝟙 X ≫ a) := by rw [Category.id_comp]
    exact h.trans (NatTrans.naturality_apply α.hom a (𝟙 X))
  NatIso.ofComponents (fun M =>
      (AddEquiv.mk ((α.app M).toEquiv) (fun (a b : X ⟶ M) => by
        change α.hom.app M (a + b) = α.hom.app M a + α.hom.app M b
        rw [key M (a + b), key M a, key M b, Φ.map_add]
        rfl)).toAddCommGrpIso)
    (fun {M N} g => by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
      exact NatTrans.naturality_apply α.hom g a)

end CategoryTheory

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})

/-- **The sections over `x` of the direct image `SheafOfModules.directImageOfEq` are the compatible
families of sections over `StructuredArrow x f.op`**, naturally in the module: the sections over
`x` of the direct image of `N` are the sections of `StructuredArrow.proj x f.op ⋙ ℱ`, for `ℱ` the
underlying presheaf of sets of `N`. -/
def directImageOfEqSectionsIso {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) (x : Dᵒᵖ) :
    directImageOfEq.{r, w} f J K O hT ⋙ SheafOfModules.forget O ⋙
        PresheafOfModules.evaluation O.obj x ⋙ CategoryTheory.forget (ModuleCat (O.obj.obj x)) ≅
      SheafOfModules.forget T ⋙ PresheafOfModules.toPresheaf T.obj ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat) ⋙
        (Functor.whiskeringLeft _ _ _).obj (StructuredArrow.proj x f.op) ⋙
        Functor.sectionsFunctor _ := by
  subst hT
  exact NatIso.ofComponents (fun N => Equiv.toIso
      { toFun := fun s => ⟨fun j => s.1 j, fun {j k} g => s.2 g⟩
        invFun := fun s => ⟨fun j => s.1 j, fun {j k} g => s.2 g⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

end SheafOfModules

end
