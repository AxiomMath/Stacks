module

public import StacksFrontier.CategoryTheory.Monoidal.BraidedEquivalenceInverse
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Pairs

/-!
# Existence of the braided extension

We prove (E) of `StacksFrontier.CategoryTheory.Monoidal.InvertingObject`. With `V` an inverse of
`F(L)`, the first projection `Pairs.pr₁` of the category of pairs of
`StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Pairs` is a braided equivalence onto `ℳ`,
and the extension is its inverse followed by the second projection.

## Main definitions

* `CategoryTheory.InvertingObject.Pairs.pr₁Equiv`: the first projection, as an equivalence.
* `CategoryTheory.InvertingObject.Pairs.ext`: the extension `ℳ ⥤ 𝒞` of `F`.
* `CategoryTheory.InvertingObject.Pairs.extIso`: the monoidal isomorphism `K ⋙ ext ≅ F`.

## Main results

* `CategoryTheory.InvertingObject.existence`: (E).
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.InvertingObject

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open Expr

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [SymmetricCategory 𝒜]
  {ℳ : Type u₂} [Category.{v₂} ℳ] [MonoidalCategory ℳ] [SymmetricCategory ℳ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] (F : 𝒜 ⥤ 𝒞) [F.Braided] {L : 𝒜} {T : ℳ}
  (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (hL : HasInverse (F.obj L))

namespace Pairs

/-- The atoms, as objects of `Pairs`. -/
abbrev ι : 𝒜 ⥤ Pairs K F ℓ hL := Graph.ι _ _ _ _

/-- `ι` followed by the first projection is `K`. -/
def ιPr₁ : ι K F ℓ hL ⋙ pr₁ K F ℓ hL ≅ K :=
  NatIso.ofComponents (fun A => Iso.refl (K.obj A))
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- `ι` followed by the second projection is `F`. -/
def ιPr₂ : ι K F ℓ hL ⋙ pr₂ K F ℓ hL ≅ F :=
  NatIso.ofComponents (fun A => Iso.refl (F.obj A))
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The isomorphism `ιPr₁` is monoidal. -/
instance : NatTrans.IsMonoidal (ιPr₁ K F ℓ hL).hom where
  unit := by
    change ((𝟙 _ ≫ (𝟙 _ : _ ⟶ _)) ≫ (ε (K.prod' F)).1) ≫ 𝟙 _ = ε K
    rw [Category.comp_id, Category.id_comp, Category.id_comp, Functor.prod'_ε_fst]
  tensor A B := by
    change ((𝟙 _ ≫ (𝟙 _ : _ ⟶ _)) ≫ (μ (K.prod' F) A B).1) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ K A B
    rw [Category.comp_id, Category.id_comp, Category.id_comp, id_tensorHom_id, Category.id_comp,
      Functor.prod'_μ_fst]

/-- The isomorphism `ιPr₂` is monoidal. -/
instance : NatTrans.IsMonoidal (ιPr₂ K F ℓ hL).hom where
  unit := by
    change ((𝟙 _ ≫ (𝟙 _ : _ ⟶ _)) ≫ (ε (K.prod' F)).2) ≫ 𝟙 _ = ε F
    rw [Category.comp_id, Category.id_comp, Category.id_comp, Functor.prod'_ε_snd]
  tensor A B := by
    change ((𝟙 _ ≫ (𝟙 _ : _ ⟶ _)) ≫ (μ (K.prod' F) A B).2) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ μ F A B
    rw [Category.comp_id, Category.id_comp, Category.id_comp, id_tensorHom_id, Category.id_comp,
      Functor.prod'_μ_snd]

variable [K.Full] [K.Faithful]
  (hess : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n))

include hess in
/-- The first projection `pr₁` is an equivalence of categories. -/
theorem pr₁_isEquivalence : (pr₁ K F ℓ hL).IsEquivalence where
  essSurj := pr₁_essSurj K F ℓ hL hess

/-- The first projection, as an equivalence. -/
def pr₁Equiv : Pairs K F ℓ hL ≌ ℳ :=
  @Functor.asEquivalence _ _ _ _ (pr₁ K F ℓ hL) (pr₁_isEquivalence K F ℓ hL hess)

/-- The functor of `pr₁Equiv` is braided. -/
instance : (pr₁Equiv K F ℓ hL hess).functor.Braided := inferInstanceAs (pr₁ K F ℓ hL).Braided

attribute [local instance] Equivalence.inverseMonoidal Equivalence.inverseBraided

/-- **The extension of `F` along `K`**: the inverse of the first projection, followed by the
second projection. -/
abbrev ext : ℳ ⥤ 𝒞 := (pr₁Equiv K F ℓ hL hess).inverse ⋙ pr₂ K F ℓ hL

/-- `ι` followed by the equivalence is `K`. -/
def ιPr₁' : ι K F ℓ hL ⋙ (pr₁Equiv K F ℓ hL hess).functor ≅ K := ιPr₁ K F ℓ hL

/-- The isomorphism `ιPr₁'` is monoidal. -/
instance : NatTrans.IsMonoidal (ιPr₁' K F ℓ hL hess).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (ιPr₁ K F ℓ hL).hom)

/-- The isomorphism `K ⋙ ext ≅ F`. -/
def extIso : K ⋙ ext K F ℓ hL hess ≅ F :=
  Functor.isoWhiskerRight (ιPr₁' K F ℓ hL hess).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pr₁Equiv K F ℓ hL hess).unitIso.symm _ ≪≫ Functor.leftUnitor _) ≪≫
    ιPr₂ K F ℓ hL

/-- The isomorphism `extIso` is monoidal. -/
instance : NatTrans.IsMonoidal (extIso K F ℓ hL hess).hom := by
  have i₁ : NatTrans.IsMonoidal (Functor.whiskerRight (ιPr₁' K F ℓ hL hess).inv
      (ext K F ℓ hL hess) ≫ (Functor.associator _ _ _).hom) := inferInstance
  have i₂ : NatTrans.IsMonoidal ((Functor.associator (pr₁Equiv K F ℓ hL hess).functor
      (pr₁Equiv K F ℓ hL hess).inverse (pr₂ K F ℓ hL)).inv ≫
        Functor.whiskerRight (pr₁Equiv K F ℓ hL hess).unitIso.inv (pr₂ K F ℓ hL) ≫
          (pr₂ K F ℓ hL).leftUnitor.hom) := inferInstance
  have i₃ : NatTrans.IsMonoidal (Functor.whiskerLeft (ι K F ℓ hL)
      ((Functor.associator (pr₁Equiv K F ℓ hL hess).functor
      (pr₁Equiv K F ℓ hL hess).inverse (pr₂ K F ℓ hL)).inv ≫
        Functor.whiskerRight (pr₁Equiv K F ℓ hL hess).unitIso.inv (pr₂ K F ℓ hL) ≫
          (pr₂ K F ℓ hL).leftUnitor.hom) ≫ (ιPr₂ K F ℓ hL).hom) := inferInstance
  have h : (extIso K F ℓ hL hess).hom =
      Functor.whiskerRight (ιPr₁' K F ℓ hL hess).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (pr₁Equiv K F ℓ hL hess).unitIso.inv _ ≫
            (Functor.leftUnitor _).hom) ≫ (ιPr₂ K F ℓ hL).hom := rfl
  rw [h, ← Category.assoc]
  infer_instance

end Pairs

section

attribute [local instance] Equivalence.inverseMonoidal Equivalence.inverseBraided

variable (𝒞 : Type u₃) [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] [K.Full] [K.Faithful] (L : 𝒜) (T : ℳ)

/-- **(E)**: the existence statement `CategoryTheory.InvertingObject.Existence` holds. -/
theorem existence : Existence 𝒞 K L T := by
  intro ℓ _ hess F _ hF
  obtain ⟨hL⟩ := hF
  exact ⟨Pairs.ext K F ℓ hL hess, inferInstance, Pairs.extIso K F ℓ hL hess, inferInstance⟩

end

end CategoryTheory.InvertingObject
