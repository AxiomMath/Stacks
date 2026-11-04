module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Reflections onto a full subcategory

A functor `L : C ⥤ C` together with a map `η : 𝟭 C ⟶ L` whose values land in a full
subcategory `P`, which is an isomorphism on `P` and which satisfies `L (η A) = η (L A)`,
exhibits `L` as a left adjoint of the inclusion of `P`.

## Main definitions

* `Stacks.CategoryTheory.reflectionHomEquiv`: the hom equivalence `(L A ⟶ B) ≃ (A ⟶ B)` for
  `B` in `P`.
* `Stacks.CategoryTheory.reflectionAdjunction`: the adjunction `P.lift L hL ⊣ P.ι`.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace Stacks.CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Postcomposing with `eqToHom h` for `h : B = B` is the identity. -/
theorem comp_eqToHom_self {A B : C} (f : A ⟶ B) (h : B = B) : f ≫ eqToHom h = f :=
  (congrArg (fun g => f ≫ g) (eqToHom_refl B h)).trans (Category.comp_id f)

/-- The hom equivalence of a reflection onto a full subcategory. -/
noncomputable def reflectionHomEquiv (P : ObjectProperty C) (L : C ⥤ C) (η : 𝟭 C ⟶ L)
    (hL : ∀ A, P (L.obj A)) (hη : ∀ A, P A → IsIso (η.app A))
    (hmap : ∀ A, L.map (η.app A) = η.app (L.obj A))
    (A : C) (B : P.FullSubcategory) :
    ((P.lift L hL).obj A ⟶ B) ≃ (A ⟶ P.ι.obj B) :=
  haveI : IsIso (η.app B.obj) := hη B.obj B.property
  { toFun := fun φ => η.app A ≫ φ.hom
    invFun := fun ψ => ObjectProperty.homMk (L.map ψ ≫ inv (η.app B.obj))
    left_inv := fun φ => by
      apply ObjectProperty.hom_ext
      have hnat : φ.hom ≫ η.app B.obj = η.app (L.obj A) ≫ L.map φ.hom :=
        η.naturality φ.hom
      change L.map (η.app A ≫ φ.hom) ≫ inv (η.app B.obj) = φ.hom
      rw [L.map_comp, hmap A, ← hnat]
      simp
    right_inv := fun ψ => by
      have hnat : ψ ≫ η.app B.obj = η.app A ≫ L.map ψ := η.naturality ψ
      change η.app A ≫ L.map ψ ≫ inv (η.app B.obj) = ψ
      rw [← Category.assoc, ← hnat]
      simp }

/-- `reflectionHomEquiv` sends `φ : L A ⟶ B` to `η A ≫ φ`. -/
theorem reflectionHomEquiv_apply (P : ObjectProperty C) (L : C ⥤ C) (η : 𝟭 C ⟶ L)
    (hL : ∀ A, P (L.obj A)) (hη : ∀ A, P A → IsIso (η.app A))
    (hmap : ∀ A, L.map (η.app A) = η.app (L.obj A))
    (A : C) (B : P.FullSubcategory) (φ : (P.lift L hL).obj A ⟶ B) :
    reflectionHomEquiv P L η hL hη hmap A B φ = η.app A ≫ φ.hom :=
  rfl

/-- **A unit-characterized reflection.**  If `L` lands in `P`, is an isomorphism on objects
of `P`, and satisfies `L (η A) = η (L A)`, then `L` is left adjoint to the inclusion of `P`. -/
noncomputable def reflectionAdjunction (P : ObjectProperty C) (L : C ⥤ C) (η : 𝟭 C ⟶ L)
    (hL : ∀ A, P (L.obj A)) (hη : ∀ A, P A → IsIso (η.app A))
    (hmap : ∀ A, L.map (η.app A) = η.app (L.obj A)) :
    P.lift L hL ⊣ P.ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := reflectionHomEquiv P L η hL hη hmap
      homEquiv_naturality_left_symm := fun {A' A B} f g => by
        apply ObjectProperty.hom_ext
        have : IsIso (η.app B.obj) := hη B.obj B.property
        change L.map (f ≫ g) ≫ inv (η.app B.obj) =
          L.map f ≫ L.map g ≫ inv (η.app B.obj)
        rw [L.map_comp, Category.assoc]
      homEquiv_naturality_right := fun {A B B'} φ k => by
        change η.app A ≫ (φ ≫ k).hom = (η.app A ≫ φ.hom) ≫ k.hom
        rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] }

/-- The unit of `reflectionAdjunction` at `A` is `η A`. -/
theorem reflectionAdjunction_unit_app (P : ObjectProperty C) (L : C ⥤ C) (η : 𝟭 C ⟶ L)
    (hL : ∀ A, P (L.obj A)) (hη : ∀ A, P A → IsIso (η.app A))
    (hmap : ∀ A, L.map (η.app A) = η.app (L.obj A)) (A : C) :
    (reflectionAdjunction P L η hL hη hmap).unit.app A = η.app A := by
  refine Eq.trans (reflectionHomEquiv_apply P L η hL hη hmap A
    ((P.lift L hL).obj A) (𝟙 _)) ?_
  rw [ObjectProperty.FullSubcategory.id_hom]
  exact Category.comp_id _

end Stacks.CategoryTheory
