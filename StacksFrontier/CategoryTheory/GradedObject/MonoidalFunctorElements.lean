module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace

/-!
# Lax monoidal functors into graded vector spaces, on elements

Let `G : D ⥤ GradedObject ℤ (ModuleCat F)` be a lax monoidal functor into `ℤ`-graded `F`-vector
spaces (Stacks, Homology, Example 0FFX). By the degreewise formula
`(V ⊗ W)ᵏ = ⨁_{i+j=k} Vⁱ ⊗_F Wʲ`, its tensorator `μ : G X ⊗ G Y ⟶ G (X ⊗ Y)` is a family of
bilinear maps `G(X)ⁱ × G(Y)ʲ → G(X ⊗ Y)ᵏ`, and its unit `ε : 𝟏 ⟶ G 𝟙` is an element of
`G(𝟙)⁰`. This file records the coherence laws of `G` as identities between these products of
elements: naturality, associativity and unitality.

## Main definitions

* `CategoryTheory.Functor.gradedMul`: the product `G(X)ⁱ × G(Y)ʲ → G(X ⊗ Y)ᵏ`, `i + j = k`.
* `CategoryTheory.Functor.gradedOne`: the image of `1` under `ε` in `G(𝟙)⁰`.

## Main results

* `CategoryTheory.Functor.map_whiskerRight_gradedMul`,
  `CategoryTheory.Functor.map_whiskerLeft_gradedMul`: naturality.
* `CategoryTheory.Functor.map_associator_gradedMul`: associativity.
* `CategoryTheory.Functor.map_leftUnitor_gradedMul`,
  `CategoryTheory.Functor.map_rightUnitor_gradedMul`: unitality.
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory Category Limits MonoidalCategory GradedObject GradedObject.Monoidal
open scoped TensorProduct

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  (G : D ⥤ GradedObject ℤ (ModuleCat.{w} F)) [G.LaxMonoidal]

/-- The product `G(X)ⁱ × G(Y)ʲ → G(X ⊗ Y)ᵏ`, for `i + j = k`, of a lax monoidal functor into
graded vector spaces: the restriction of the tensorator to the summand `G(X)ⁱ ⊗ G(Y)ʲ`. -/
noncomputable def gradedMul (X Y : D) (i j k : ℤ) (h : i + j = k) :
    G.obj X i →ₗ[F] G.obj Y j →ₗ[F] G.obj (X ⊗ Y) k :=
  TensorProduct.curry (ιTensorObj (G.obj X) (G.obj Y) i j k h ≫ LaxMonoidal.μ G X Y k).hom

/-- `gradedMul G X Y i j k h x y` is the image of `x ⊗ y` under the summand inclusion followed by
the tensorator. -/
lemma gradedMul_apply (X Y : D) (i j k : ℤ) (h : i + j = k) (x : G.obj X i) (y : G.obj Y j) :
    gradedMul G X Y i j k h x y =
      (ιTensorObj (G.obj X) (G.obj Y) i j k h ≫ LaxMonoidal.μ G X Y k) (x ⊗ₜ y) :=
  rfl

/-- The unit `1 ∈ G(𝟙)⁰` of a lax monoidal functor into graded vector spaces. -/
noncomputable def gradedOne : G.obj (𝟙_ D) 0 :=
  (LaxMonoidal.ε G 0) ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).inv (1 : F))

variable {G}

/-- Naturality of the product in both factors. -/
private lemma map_tensorHom_gradedMul {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') (i j k : ℤ)
    (h : i + j = k) (x : G.obj X i) (y : G.obj Y j) :
    G.map (f ⊗ₘ g) k (gradedMul G X Y i j k h x y) =
      gradedMul G X' Y' i j k h (G.map f i x) (G.map g j y) := by
  have H := ConcreteCategory.congr_hom
    (ιTensorObj (G.obj X) (G.obj Y) i j k h ≫= congr($(LaxMonoidal.μ_natural G f g) k))
    (x ⊗ₜ y)
  simp only [categoryOfGradedObjects_comp] at H
  erw [ι_tensorHom_assoc] at H
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at H
  exact H.symm

/-- Naturality of the product in the left factor. -/
lemma map_whiskerRight_gradedMul {X X' : D} (f : X ⟶ X') (Y : D) (i j k : ℤ) (h : i + j = k)
    (x : G.obj X i) (y : G.obj Y j) :
    G.map (f ▷ Y) k (gradedMul G X Y i j k h x y) = gradedMul G X' Y i j k h (G.map f i x) y := by
  simpa using map_tensorHom_gradedMul f (𝟙 Y) i j k h x y

/-- Naturality of the product in the right factor. -/
lemma map_whiskerLeft_gradedMul (X : D) {Y Y' : D} (f : Y ⟶ Y') (i j k : ℤ) (h : i + j = k)
    (x : G.obj X i) (y : G.obj Y j) :
    G.map (X ◁ f) k (gradedMul G X Y i j k h x y) = gradedMul G X Y' i j k h x (G.map f j y) := by
  simpa using map_tensorHom_gradedMul (𝟙 X) f i j k h x y

/-- Associativity of a lax monoidal functor, on the summand `G(X)ⁱ ⊗ G(Y)ʲ ⊗ G(Z)ˡ`. -/
lemma map_associator_gradedMul_hom (X Y Z : D) (i j l k : ℤ) (h : i + j + l = k) :
    (ιTensorObj (G.obj X) (G.obj Y) i j (i + j) rfl ≫ LaxMonoidal.μ G X Y (i + j)) ▷
          G.obj Z l ≫
        ιTensorObj (G.obj (X ⊗ Y)) (G.obj Z) (i + j) l k h ≫ LaxMonoidal.μ G (X ⊗ Y) Z k ≫
          G.map (α_ X Y Z).hom k =
      (α_ (G.obj X i) (G.obj Y j) (G.obj Z l)).hom ≫
        G.obj X i ◁ (ιTensorObj (G.obj Y) (G.obj Z) j l (j + l) rfl ≫
          LaxMonoidal.μ G Y Z (j + l)) ≫
        ιTensorObj (G.obj X) (G.obj (Y ⊗ Z)) i (j + l) k (by rw [← h, add_assoc]) ≫
          LaxMonoidal.μ G X (Y ⊗ Z) k := by
  have H := ιTensorObj₃' (G.obj X) (G.obj Y) (G.obj Z) i j l k h ≫=
    congr($(LaxMonoidal.associativity G X Y Z) k)
  simp only [categoryOfGradedObjects_comp, Monoidal.whiskerRight_apply,
    Monoidal.whiskerLeft_apply, Monoidal.associator_hom_apply] at H
  rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃'_eq _ _ _ i j l k h (i + j) rfl,
    ιTensorObj₃_eq _ _ _ i j l k h (j + l) rfl] at H
  simpa using H

/-- Associativity of the product of a lax monoidal functor. -/
lemma map_associator_gradedMul (X Y Z : D) (i j l k : ℤ) (h : i + j + l = k) (x : G.obj X i)
    (y : G.obj Y j) (z : G.obj Z l) :
    G.map (α_ X Y Z).hom k
        (gradedMul G (X ⊗ Y) Z (i + j) l k h (gradedMul G X Y i j (i + j) rfl x y) z) =
      gradedMul G X (Y ⊗ Z) i (j + l) k (by rw [← h, add_assoc]) x
        (gradedMul G Y Z j l (j + l) rfl y z) := by
  have H := ConcreteCategory.congr_hom (map_associator_gradedMul_hom X Y Z i j l k h)
    ((x ⊗ₜ y) ⊗ₜ z)
  simp only [ConcreteCategory.comp_apply] at H
  exact H

/-- Left unitality of a lax monoidal functor, on the summand `G(𝟙)⁰ ⊗ G(X)ⁱ`. -/
lemma map_leftUnitor_gradedMul_hom (X : D) (i : ℤ) :
    LaxMonoidal.ε G 0 ▷ G.obj X i ≫ ιTensorObj (G.obj (𝟙_ D)) (G.obj X) 0 i i (zero_add i) ≫
        LaxMonoidal.μ G (𝟙_ D) X i ≫ G.map (λ_ X).hom i =
      (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).hom ▷ G.obj X i ≫
        (λ_ (G.obj X i)).hom := by
  have H := ιTensorObj (𝟙_ _) (G.obj X) 0 i i (zero_add i) ≫=
    congr($(LaxMonoidal.left_unitality G X) i)
  simp only [categoryOfGradedObjects_comp, Monoidal.whiskerRight_apply,
    Monoidal.leftUnitor_hom_apply, ιTensorObj_leftUnitor_hom] at H
  simpa using H.symm

/-- Right unitality of a lax monoidal functor, on the summand `G(X)ⁱ ⊗ G(𝟙)⁰`. -/
lemma map_rightUnitor_gradedMul_hom (X : D) (i : ℤ) :
    G.obj X i ◁ LaxMonoidal.ε G 0 ≫ ιTensorObj (G.obj X) (G.obj (𝟙_ D)) i 0 i (add_zero i) ≫
        LaxMonoidal.μ G X (𝟙_ D) i ≫ G.map (ρ_ X).hom i =
      G.obj X i ◁ (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).hom ≫
        (ρ_ (G.obj X i)).hom := by
  have H := ιTensorObj (G.obj X) (𝟙_ _) i 0 i (add_zero i) ≫=
    congr($(LaxMonoidal.right_unitality G X) i)
  simp only [categoryOfGradedObjects_comp, Monoidal.whiskerLeft_apply,
    Monoidal.rightUnitor_hom_apply, ιTensorObj_rightUnitor_hom] at H
  simpa using H.symm

/-- Left unitality of the product of a lax monoidal functor. -/
lemma map_leftUnitor_gradedMul (X : D) (i : ℤ) (x : G.obj X i) :
    G.map (λ_ X).hom i (gradedMul G (𝟙_ D) X 0 i i (zero_add i) (gradedOne G) x) = x := by
  have H := ConcreteCategory.congr_hom (map_leftUnitor_gradedMul_hom (G := G) X i)
    ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).inv (1 : F) ⊗ₜ x)
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    Iso.inv_hom_id_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul] at H
  exact H

/-- Right unitality of the product of a lax monoidal functor. -/
lemma map_rightUnitor_gradedMul (X : D) (i : ℤ) (x : G.obj X i) :
    G.map (ρ_ X).hom i (gradedMul G X (𝟙_ D) i 0 i (add_zero i) x (gradedOne G)) = x := by
  have H := ConcreteCategory.congr_hom (map_rightUnitor_gradedMul_hom (G := G) X i)
    (x ⊗ₜ (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).inv (1 : F))
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    Iso.inv_hom_id_apply, ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul] at H
  exact H

end CategoryTheory.Functor
