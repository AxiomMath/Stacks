module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# A presheaf whose relocalization is representable

For `a : A ⟶ X` in a category `C`, the relocalization `Λ_a` carries presheaves on `C/A` to
presheaves on `C/X`.  This file proves that if `Λ_a F` is representable by `V : C/X`, then `F` is
representable, by `V` viewed over `A` through the factorization `V ⟶ (A ⟶ X)` which the
representing isomorphism carries.

## Main results

* `CategoryTheory.OverShriek.nonempty_iso_yoneda_of_relocalize`.

This statement extends `StacksFrontier/CategoryTheory/Sites/Localization/RelocalizeRestrict.lean`.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X) (F : (Over A)ᵒᵖ ⥤ Type v)

/-- **A presheaf whose relocalization is representable is representable.**  If `Λ_a F` is
represented by `V : C/X`, then `F` is represented by `V` viewed over `A` through the
factorization `V ⟶ (A ⟶ X)` that the representing isomorphism carries: a section of `F` over
`W : C/A` is a section of `Λ_a F` over `W ⟶ A ⟶ X` whose factorization is the structure morphism
of `W`, that is, a morphism `W ⟶ V` over `X` whose composite with that factorization is the
structure morphism of `W`. -/
theorem nonempty_iso_yoneda_of_relocalize {V : Over X}
    (ι : (relocalizePresheafFunctor a).obj F ≅ yoneda.obj V) :
    Nonempty (F ≅ yoneda.obj
      (Over.mk (yoneda.preimage (ι.inv ≫ relocalizeToYoneda a F)).left)) := by
  set ψ := yoneda.preimage (ι.inv ≫ relocalizeToYoneda a F)
  have hψ : ∀ {Z : Over X} (m : Z ⟶ V),
      m ≫ ψ = (relocalizeToYoneda a F).app (op Z) (ι.inv.app (op Z) m) := fun {Z} m =>
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Functor.map_preimage yoneda (ι.inv ≫ relocalizeToYoneda a F)) (op Z)) m
  have hinv : ∀ {Z : (Over X)ᵒᵖ} (x : ((relocalizePresheafFunctor a).obj F).obj Z),
      ι.inv.app Z (ι.hom.app Z x) = x := fun {Z} x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app ι.hom_inv_id Z) x
  have hinv' : ∀ {Z : (Over X)ᵒᵖ} (m : (yoneda.obj V).obj Z), ι.hom.app Z (ι.inv.app Z m) = m :=
    fun {Z} m => ConcreteCategory.congr_hom (NatTrans.congr_app ι.inv_hom_id Z) m
  let β := relocalizeToRestricted a ι.hom
  have hβ : ∀ (W : (Over A)ᵒᵖ) (s : F.obj W), (β.app W s).left ≫ ψ.left = W.unop.hom :=
    fun W s => congrArg CommaMorphism.left
      ((hψ (β.app W s)).trans (congrArg ((relocalizeToYoneda a F).app _) (hinv _)))
  let α : F ⟶ yoneda.obj (Over.mk ψ.left) :=
    { app W := ↾fun s => Over.homMk (β.app W s).left (hβ W s)
      naturality W W' k := by
        ext s
        refine Over.OverMorphism.ext ?_
        show (β.app W' (F.map k s)).left = k.unop.left ≫ (β.app W s).left
        exact congrArg CommaMorphism.left (ConcreteCategory.congr_hom (β.naturality k) s) }
  have hbij : ∀ W, Function.Bijective (α.app W) := by
    intro W
    refine ⟨fun s t hst => ?_, fun n => ?_⟩
    · have h₀ : (α.app W s).left = (α.app W t).left := congrArg CommaMorphism.left hst
      have h₂ := congrArg (ι.inv.app _) (Over.OverMorphism.ext h₀ : β.app W s = β.app W t)
      change ι.inv.app _ (ι.hom.app _
          (relocalizeMk a F (W := op (Over.mk (W.unop.hom ≫ a))) W.unop.hom s rfl)) =
        ι.inv.app _ (ι.hom.app _
          (relocalizeMk a F (W := op (Over.mk (W.unop.hom ≫ a))) W.unop.hom t rfl)) at h₂
      rw [hinv, hinv] at h₂
      have h' : (⟨W.unop.hom, s⟩ : Σ φ : W.unop.left ⟶ A, F.obj (op (Over.mk φ))) =
        ⟨W.unop.hom, t⟩ := congrArg Subtype.val h₂
      exact eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h').2
    · have hn : n.left ≫ V.hom = W.unop.hom ≫ a := by
        rw [← Over.w ψ, ← Category.assoc]
        exact congrArg (· ≫ a) (Over.w n)
      let m : Over.mk (W.unop.hom ≫ a) ⟶ V := Over.homMk n.left hn
      have hm := hψ m
      generalize hx : ι.inv.app (op (Over.mk (W.unop.hom ≫ a))) m = x at hm
      obtain ⟨⟨φ, s⟩, hφ⟩ := x
      have hφW : φ = W.unop.hom := (congrArg CommaMorphism.left hm).symm.trans (Over.w n)
      subst hφW
      refine ⟨s, Over.OverMorphism.ext ?_⟩
      have hs : β.app W s = ι.hom.app (op (Over.mk (W.unop.hom ≫ a)))
          (ι.inv.app (op (Over.mk (W.unop.hom ≫ a))) m) := by
        rw [hx]
        rfl
      exact (congrArg CommaMorphism.left (hs.trans (hinv' m)) : _)
  have : ∀ W, IsIso (α.app W) := fun W => (isIso_iff_bijective _).2 (hbij W)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α⟩

end CategoryTheory.OverShriek

end
