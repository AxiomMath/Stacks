module

public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDesc

/-!
# The fibre of a morphism out of a tensor product of sheaves of modules

Let `Φ` be a point of a site. The fibre functor `Φ.sheafFiber` is monoidal (Mathlib), so the
morphism of sheaves `CategoryTheory.Sheaf.tensorDesc β hβ : F ⊗ G ⟶ H` defined by a natural
family of bilinear maps `β` induces `F_Φ ⊗ G_Φ ≅ (F ⊗ G)_Φ ⟶ H_Φ` on fibres. This file computes it
on germs: the germ of `a ⊗ b` goes to the germ of `β a b`. This is the stalk of the pairing of
coefficients `ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), on which its perfectness is tested.

## Main results

* `CategoryTheory.Sheaf.toPresheafFiber_tensorHom_μ_sheafFiber_map_tensorDesc`: the fibre of
  `tensorDesc β hβ` on germs, as an equality of morphisms.
* `CategoryTheory.Sheaf.sheafFiber_tensorDesc_tmul`: the same on elements.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite Functor

universe w' w v₁ u₁ u

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type u} [CommRing R]
  (Φ : J.Point.{w'}) [LocallySmall.{w'} C]
  [HasColimitsOfSize.{w', w'} (ModuleCat.{max w u} R)] [HasProducts.{w'} (ModuleCat.{max w u} R)]
  [∀ X : ModuleCat.{max w u} R, PreservesFilteredColimitsOfSize.{w', w'} (tensorLeft X)]
  [∀ X : ModuleCat.{max w u} R, PreservesFilteredColimitsOfSize.{w', w'} (tensorRight X)]

attribute [local instance] monoidalCategory

variable [(J.W (A := ModuleCat.{max w u} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{max w u} R)]

/-- **The fibre of `tensorDesc` on germs**: composed with the germs at `x ∈ Φ(U)` and the
monoidal structure of the fibre functor, the fibre of `tensorDesc β hβ` is the germ of `β` on
sections over `U`. -/
theorem toPresheafFiber_tensorHom_μ_sheafFiber_map_tensorDesc
    {F G H : Sheaf J (ModuleCat.{max w u} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) (U : C) (x : Φ.fiber.obj U) :
    (Φ.toPresheafFiber U x F.obj ⊗ₘ Φ.toPresheafFiber U x G.obj) ≫
        LaxMonoidal.μ Φ.sheafFiber F G ≫ Φ.sheafFiber.map (tensorDesc β hβ) =
      (presheafTensorDesc β hβ).app (op U) ≫ Φ.toPresheafFiber U x H.obj := by
  let A := ModuleCat.{max w u} R
  let L := presheafToSheaf J A
  let e := Φ.presheafToSheafCompSheafFiberIso A
  have he : ∀ P : Cᵒᵖ ⥤ A, e.inv.app P = Φ.presheafFiber.map (toSheafify J P) := fun _ => rfl
  have hi : ∀ K : Sheaf J A, Φ.sheafFiber.map (sheafificationIso K).hom = e.inv.app K.obj := by
    intro K
    rw [he]
    show Φ.presheafFiber.map (isoSheafify J K.2).hom = _
    rw [isoSheafify_hom]
  have hμ : LaxMonoidal.μ Φ.sheafFiber (L.obj F.obj) (L.obj G.obj) =
      (e.hom.app _ ⊗ₘ e.hom.app _) ≫ LaxMonoidal.μ Φ.presheafFiber F.obj G.obj ≫
        e.inv.app _ ≫ Φ.sheafFiber.map (OplaxMonoidal.δ L _ _) :=
    Localization.Monoidal.functorMonoidalOfComp_μ L J.W Φ.sheafFiber Φ.presheafFiber _ _
  have hc : e.inv.app H.obj ≫ Φ.sheafFiber.map ((sheafificationAdjunction J A).counit.app H) =
      𝟙 _ := by
    rw [he]
    show Φ.presheafFiber.map (toSheafify J H.obj) ≫
      Φ.presheafFiber.map
        ((sheafToPresheaf J A).map ((sheafificationAdjunction J A).counit.app H)) = _
    rw [← Φ.presheafFiber.map_comp]
    have h3 := (sheafificationAdjunction J A).right_triangle_components H
    rw [sheafificationAdjunction_unit_app] at h3
    exact (congrArg Φ.presheafFiber.map h3).trans (Φ.presheafFiber.map_id _)
  have hnat := e.inv.naturality (presheafTensorDesc β hβ)
  dsimp only [Functor.comp_map] at hnat
  have key : LaxMonoidal.μ Φ.sheafFiber F G ≫ Φ.sheafFiber.map (tensorDesc β hβ) =
      (LaxMonoidal.μ Φ.presheafFiber F.obj G.obj ≫ Φ.presheafFiber.map (presheafTensorDesc β hβ) :
        Φ.presheafFiber.obj F.obj ⊗ Φ.presheafFiber.obj G.obj ⟶ Φ.presheafFiber.obj H.obj) := by
    simp only [tensorDesc, Adjunction.homEquiv_counit, Functor.map_comp, tensorIso_hom,
      Functor.Monoidal.μIso_hom]
    have hi' : ∀ K : Sheaf J A,
        Φ.sheafFiber.map (sheafificationIso K).hom ≫ e.hom.app K.obj = 𝟙 _ := fun K =>
      (congrArg (· ≫ e.hom.app K.obj) (hi K)).trans (e.inv_hom_id_app K.obj)
    have h0 : (Φ.sheafFiber.map (sheafificationIso F).hom ⊗ₘ
          Φ.sheafFiber.map (sheafificationIso G).hom) ≫ (e.hom.app F.obj ⊗ₘ e.hom.app G.obj) ≫
          LaxMonoidal.μ Φ.presheafFiber F.obj G.obj =
        LaxMonoidal.μ Φ.presheafFiber F.obj G.obj := by
      rw [tensorHom_comp_tensorHom_assoc, hi', hi']
      exact (congrArg (· ≫ LaxMonoidal.μ Φ.presheafFiber F.obj G.obj)
        (id_tensorHom_id (Φ.presheafFiber.obj F.obj) (Φ.presheafFiber.obj G.obj))).trans
          (Category.id_comp _)
    have h2 : Φ.sheafFiber.map (OplaxMonoidal.δ L F.obj G.obj) ≫
        Φ.sheafFiber.map (LaxMonoidal.μ L F.obj G.obj) = 𝟙 _ := by
      rw [← Φ.sheafFiber.map_comp, Monoidal.δ_μ, Functor.map_id]
    have h3 : e.inv.app (F.obj ⊗ G.obj) ≫ Φ.sheafFiber.map (L.map (presheafTensorDesc β hβ)) =
        Φ.presheafFiber.map (presheafTensorDesc β hβ) ≫ e.inv.app H.obj := hnat.symm
    rw [← LaxMonoidal.μ_natural_assoc, hμ]
    simp only [Category.assoc]
    rw [reassoc_of% h0, reassoc_of% h2, reassoc_of% h3, hc]
    exact congrArg (LaxMonoidal.μ Φ.presheafFiber F.obj G.obj ≫ ·) (Category.comp_id _)
  have := congrArg (fun k => (Φ.toPresheafFiber U x F.obj ⊗ₘ Φ.toPresheafFiber U x G.obj) ≫ k) key
  exact this.trans ((Φ.tensorHom_comp_toPresheafFiber_μ_assoc U x F.obj G.obj
    (Φ.presheafFiber.map (presheafTensorDesc β hβ))).trans
      (Φ.toPresheafFiber_naturality (presheafTensorDesc β hβ) U x))

/-- **The fibre of `tensorDesc` on germs, elementwise**: the germ of `a ⊗ b` at `x ∈ Φ(U)` goes
to the germ of `β a b`. -/
theorem sheafFiber_tensorDesc_tmul {F G H : Sheaf J (ModuleCat.{max w u} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) (U : C) (x : Φ.fiber.obj U)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    (LaxMonoidal.μ Φ.sheafFiber F G ≫ Φ.sheafFiber.map (tensorDesc β hβ)).hom
        ((Φ.toPresheafFiber U x F.obj).hom a ⊗ₜ (Φ.toPresheafFiber U x G.obj).hom b) =
      (Φ.toPresheafFiber U x H.obj).hom (β (op U) a b) :=
  ConcreteCategory.congr_hom
    (toPresheafFiber_tensorHom_μ_sheafFiber_map_tensorDesc Φ β hβ U x) (a ⊗ₜ b)

end CategoryTheory.Sheaf
