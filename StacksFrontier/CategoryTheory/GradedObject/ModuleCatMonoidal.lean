module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksCore.CategoryTheory.GradedObject.Abelian
public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace
public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding

/-!
# Graded modules: the monoidal structure on elements

Let `R` be a commutative ring and `GradedObject ℤ (ModuleCat R)` the category of `ℤ`-graded
`R`-modules with Mathlib's monoidal structure `(X ⊗ Y)ⁿ = ⨁_{p+q=n} Xᵖ ⊗_R Y^q`
(Stacks, Homology, Example 0FFX). This file records how the structure acts on elements of the
summands `Xᵖ ⊗_R Y^q`, through the inclusions `GradedObject.Monoidal.ιTensorObj`, and that the
tensor product is additive in each variable.

## Main results

* `CategoryTheory.GradedObject.Monoidal.monoidalPreadditive`: the tensor product of graded modules
  is additive in each variable.
* `CategoryTheory.GradedObject.Monoidal.tensorObj_hom_ext`: two maps out of `(X ⊗ Y)ⁿ` agree as
  soon as they agree on the elements `x ⊗ y` of the summands.
* `CategoryTheory.GradedObject.Monoidal.tensorHom_apply_ιTensorObj`,
  `associator_hom_apply_ιTensorObj`, `leftUnitor_hom_apply_ιTensorObj`,
  `rightUnitor_hom_apply_ιTensorObj`, `koszulBraiding_hom_apply_ιTensorObj`: the tensor product of
  morphisms, the constraints and the Koszul-signed commutativity constraint on elements.

The category of graded modules is abelian (`CategoryTheory.GradedObject.abelian`, given
`Mathlib.Algebra.Category.ModuleCat.Abelian`, imported here), hence idempotent complete by
Mathlib's `CategoryTheory.Idempotents.isIdempotentComplete_of_abelian`; no separate instance is
needed.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
-/

@[expose] public section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory
open scoped TensorProduct

universe w

variable {R : Type w} [CommRing R]

/-! ### Whiskering on summands -/

/-- On the summand `Xᵖ ⊗ Y^q`, the whiskering `X ◁ φ` is `Xᵖ ◁ φ q`. -/
@[reassoc]
lemma ιTensorObj_whiskerLeft (X : GradedObject ℤ (ModuleCat.{w} R))
    {Y Y' : GradedObject ℤ (ModuleCat.{w} R)} (φ : Y ⟶ Y') (p q n : ℤ) (h : p + q = n) :
    ιTensorObj X Y p q n h ≫ (X ◁ φ) n = (X p ◁ φ q) ≫ ιTensorObj X Y' p q n h :=
  (ι_tensorHom (𝟙 X) φ p q n h).trans (congrArg (· ≫ ιTensorObj X Y' p q n h)
    (id_tensorHom (X p) (φ q)))

/-- On the summand `Xᵖ ⊗ Y^q`, the whiskering `φ ▷ Y` is `φ p ▷ Y^q`. -/
@[reassoc]
lemma ιTensorObj_whiskerRight {X X' : GradedObject ℤ (ModuleCat.{w} R)} (φ : X ⟶ X')
    (Y : GradedObject ℤ (ModuleCat.{w} R)) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj X Y p q n h ≫ (φ ▷ Y) n = (φ p ▷ Y q) ≫ ιTensorObj X' Y p q n h :=
  (ι_tensorHom φ (𝟙 Y) p q n h).trans (congrArg (· ≫ ιTensorObj X' Y p q n h)
    (tensorHom_id (φ p) (Y q)))

/-- **The tensor product of graded modules is additive in each variable.** -/
instance monoidalPreadditive : MonoidalPreadditive (GradedObject ℤ (ModuleCat.{w} R)) where
  whiskerLeft_zero {X Y Z} := by
    refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_ext _ _ fun p q h ↦ ?_
    rw [ιTensorObj_whiskerLeft]
    simp
  zero_whiskerRight {X Y Z} := by
    refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_ext _ _ fun p q h ↦ ?_
    rw [ιTensorObj_whiskerRight]
    simp
  whiskerLeft_add {X Y Z} f g := by
    refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_ext _ _ fun p q h ↦ ?_
    change _ = ιTensorObj X Y p q n h ≫ ((X ◁ f) n + (X ◁ g) n)
    rw [ιTensorObj_whiskerLeft, Preadditive.comp_add, ιTensorObj_whiskerLeft,
      ιTensorObj_whiskerLeft]
    change (X p ◁ (f q + g q)) ≫ _ = _
    simp
  add_whiskerRight {X Y Z} f g := by
    refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_ext _ _ fun p q h ↦ ?_
    change _ = ιTensorObj Y X p q n h ≫ ((f ▷ X) n + (g ▷ X) n)
    rw [ιTensorObj_whiskerRight, Preadditive.comp_add, ιTensorObj_whiskerRight,
      ιTensorObj_whiskerRight]
    change ((f p + g p) ▷ X q) ≫ _ = _
    simp

-- Graded modules are idempotent complete, being abelian (with `ModuleCat.Abelian` imported).
example : IsIdempotentComplete (GradedObject ℤ (ModuleCat.{w} R)) := inferInstance

/-! ### Elementwise formulas -/

variable {X Y Z X' Y' : GradedObject ℤ (ModuleCat.{w} R)}

/-- Two maps out of `(X ⊗ Y)ⁿ` agree as soon as they agree on the elements `x ⊗ y` of the
summands `Xᵖ ⊗ Y^q`, `p + q = n`. -/
lemma tensorObj_hom_ext {A : ModuleCat.{w} R} {n : ℤ} {f g : (X ⊗ Y) n ⟶ A}
    (h : ∀ (p q : ℤ) (hpq : p + q = n) (x : X p) (y : Y q),
      f.hom ((ιTensorObj X Y p q n hpq).hom (x ⊗ₜ y)) =
        g.hom ((ιTensorObj X Y p q n hpq).hom (x ⊗ₜ y))) : f = g :=
  tensorObj_ext _ _ fun p q hpq ↦ ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ h p q hpq x y

/-- The tensor product of morphisms on elements: `(f ⊗ g)(x ⊗ y) = f x ⊗ g y`. -/
lemma tensorHom_apply_ιTensorObj (f : X ⟶ X') (g : Y ⟶ Y') (p q n : ℤ) (h : p + q = n)
    (x : X p) (y : Y q) :
    ((f ⊗ₘ g) n).hom ((ιTensorObj X Y p q n h).hom (x ⊗ₜ y)) =
      (ιTensorObj X' Y' p q n h).hom ((f p).hom x ⊗ₜ (g q).hom y) :=
  congrArg (fun φ ↦ φ.hom (x ⊗ₜ[R] y)) (ι_tensorHom f g p q n h)

/-- The associator on elements: `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`. -/
lemma associator_hom_apply_ιTensorObj (p q r pq qr n : ℤ) (hpq : p + q = pq)
    (hqr : q + r = qr) (h : pq + r = n) (h' : p + qr = n) (x : X p) (y : Y q) (z : Z r) :
    ((α_ X Y Z).hom n).hom ((ιTensorObj (X ⊗ Y) Z pq r n h).hom
        ((ιTensorObj X Y p q pq hpq).hom (x ⊗ₜ y) ⊗ₜ z)) =
      (ιTensorObj X (Y ⊗ Z) p qr n h').hom (x ⊗ₜ (ιTensorObj Y Z q r qr hqr).hom (y ⊗ₜ z)) := by
  subst hpq hqr
  have h₁ := congrArg (fun φ ↦ φ.hom ((x ⊗ₜ[R] y) ⊗ₜ[R] z))
    (ιTensorObj₃'_associator_hom X Y Z p q r n h)
  simp only [ιTensorObj₃'] at h₁
  rwa [ιTensorObj₃_eq X Y Z p q r n h (q + r) rfl] at h₁

/-- The unit element `1 ∈ (𝟙_ _)⁰ = R` of the graded unit. -/
noncomputable def unitOne : (𝟙_ (GradedObject ℤ (ModuleCat.{w} R))) 0 :=
  (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} R)).inv.hom (1 : R)

/-- If an isomorphism of graded modules sends `x` to `z` in degree `n`, its inverse sends `z`
back to `x`. -/
private lemma iso_hom_apply_of_inv_apply {A B : GradedObject ℤ (ModuleCat.{w} R)} (e : A ≅ B)
    {n : ℤ} {x : B n} {z : A n} (h : (e.inv n).hom x = z) : (e.hom n).hom z = x := by
  rw [← h]
  change ((e.inv ≫ e.hom) n).hom x = x
  rw [Iso.inv_hom_id]
  rfl

/-- The left unitor on elements: `1 ⊗ x ↦ x`. -/
lemma leftUnitor_hom_apply_ιTensorObj (n : ℤ) (h : 0 + n = n) (x : X n) :
    ((λ_ X).hom n).hom ((ιTensorObj (𝟙_ _) X 0 n n h).hom (unitOne ⊗ₜ x)) = x := by
  refine iso_hom_apply_of_inv_apply (λ_ X) ?_
  change ((Monoidal.leftUnitor X).inv n).hom x = _
  rw [leftUnitor_inv_apply]
  rfl

/-- The right unitor on elements: `x ⊗ 1 ↦ x`. -/
lemma rightUnitor_hom_apply_ιTensorObj (n : ℤ) (h : n + 0 = n) (x : X n) :
    ((ρ_ X).hom n).hom ((ιTensorObj X (𝟙_ _) n 0 n h).hom (x ⊗ₜ unitOne)) = x := by
  refine iso_hom_apply_of_inv_apply (ρ_ X) ?_
  change ((Monoidal.rightUnitor X).inv n).hom x = _
  rw [rightUnitor_inv_apply]
  rfl

/-- The Koszul-signed commutativity constraint on elements: `x ⊗ y ↦ (-1)^{pq} y ⊗ x` for
`x ∈ Xᵖ`, `y ∈ Y^q` (Stacks, Homology, Example 0FFX). -/
lemma koszulBraiding_hom_apply_ιTensorObj (p q n : ℤ) (h : p + q = n) (h' : q + p = n)
    (x : X p) (y : Y q) :
    ((koszulBraiding X Y).hom n).hom ((ιTensorObj X Y p q n h).hom (x ⊗ₜ y)) =
      ((p * q).negOnePow : ℤ) • (ιTensorObj Y X q p n h').hom (y ⊗ₜ x) := by
  refine (congrArg (fun φ ↦ φ.hom (x ⊗ₜ[R] y)) (ι_koszulBraiding_hom X Y p q n h)).trans ?_
  rw [Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rfl

end CategoryTheory.GradedObject.Monoidal

end
