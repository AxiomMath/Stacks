module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Transporting monoid objects and their endomorphisms

## Main results

* `CategoryTheory.MonObj.ofIso_whiskerRight_mul` and `CategoryTheory.Functor.map_whiskerRight_mul`:
  an endomorphism commuting with the multiplication still does so after transport along an
  isomorphism or a lax monoidal functor.
* `CategoryTheory.ObjectProperty.monObjOfObj` and
  `CategoryTheory.ObjectProperty.isCommMonObjOfObj`: a (commutative) monoid structure on the
  underlying object of an object of a full monoidal subcategory is one on the object itself.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- **An endomorphism commuting with the multiplication, transported by
`CategoryTheory.MonObj.ofIso`**: if `(κ ⊗ 1) ≫ μ = μ ≫ κ` on `M`, the conjugate of `κ` by `e`
commutes with the transported multiplication of `N`. -/
theorem MonObj.ofIso_whiskerRight_mul {M N : C} [MonObj M] (e : M ≅ N) (κ : M ⟶ M)
    (hκ : κ ▷ M ≫ μ[M] = μ[M] ≫ κ) :
    letI := MonObj.ofIso e
    (e.inv ≫ κ ≫ e.hom) ▷ N ≫ μ[N] = μ[N] ≫ e.inv ≫ κ ≫ e.hom := by
  let := MonObj.ofIso e
  change (e.inv ≫ κ ≫ e.hom) ▷ N ≫ (e.inv ⊗ₘ e.inv) ≫ μ[M] ≫ e.hom =
    ((e.inv ⊗ₘ e.inv) ≫ μ[M] ≫ e.hom) ≫ e.inv ≫ κ ≫ e.hom
  have h1 : (e.inv ≫ κ ≫ e.hom) ▷ N ≫ (e.inv ⊗ₘ e.inv) = (e.inv ⊗ₘ e.inv) ≫ κ ▷ M := by
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  rw [reassoc_of% h1, reassoc_of% hκ]
  simp

/-- **A lax monoidal functor carries an endomorphism commuting with the multiplication to one
commuting with the multiplication of the image monoid.** -/
theorem Functor.map_whiskerRight_mul {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D)
    [F.LaxMonoidal] {M : C} [MonObj M] (κ : M ⟶ M) (hκ : κ ▷ M ≫ μ[M] = μ[M] ≫ κ) :
    letI := Functor.monObjObj (F := F) (X := M)
    F.map κ ▷ F.obj M ≫ μ[F.obj M] = μ[F.obj M] ≫ F.map κ := by
  let := Functor.monObjObj (F := F) (X := M)
  change F.map κ ▷ F.obj M ≫ Functor.LaxMonoidal.μ F M M ≫ F.map μ[M] =
    (Functor.LaxMonoidal.μ F M M ≫ F.map μ[M]) ≫ F.map κ
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, hκ, F.map_comp, Category.assoc]

namespace ObjectProperty

variable (P : ObjectProperty C) [P.IsMonoidal]

/-- A monoid structure on the underlying object of an object of a full monoidal subcategory is a
monoid structure on that object. -/
@[instance_reducible]
def monObjOfObj (X : P.FullSubcategory) [MonObj X.obj] : MonObj X where
  one := ObjectProperty.homMk η[X.obj]
  mul := ObjectProperty.homMk μ[X.obj]
  one_mul := by ext; exact MonObj.one_mul X.obj
  mul_one := by ext; exact MonObj.mul_one X.obj
  mul_assoc := by ext; exact MonObj.mul_assoc X.obj

/-- Commutativity transfers to the full monoidal subcategory. -/
theorem isCommMonObjOfObj [BraidedCategory C] (X : P.FullSubcategory) [MonObj X.obj]
    [IsCommMonObj X.obj] :
    letI := monObjOfObj P X
    IsCommMonObj X := by
  let := monObjOfObj P X
  exact ⟨by ext; exact IsCommMonObj.mul_comm X.obj⟩

/-- An endomorphism commuting with the multiplication of the underlying object commutes with the
multiplication in the full monoidal subcategory. -/
theorem whiskerRight_mul_monObjOfObj (X : P.FullSubcategory) [MonObj X.obj] (κ : X ⟶ X)
    (hκ : κ.hom ▷ X.obj ≫ μ[X.obj] = μ[X.obj] ≫ κ.hom) :
    letI := monObjOfObj P X
    κ ▷ X ≫ μ[X] = μ[X] ≫ κ := by
  let := monObjOfObj P X
  ext
  exact hκ

end ObjectProperty

end CategoryTheory
