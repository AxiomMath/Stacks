module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monoid objects among the untwisted triples

Let `C` be a graded monoidal category and `X` an object of `C`. A monoid structure on `X` whose
unit and multiplication are homogeneous of degree zero is a monoid structure on the triple
`(X, 𝟙, 0)` of the twisted Karoubi envelope, and likewise for commutativity and for morphisms
of monoids. All identities are checked on underlying morphisms of `C`, where they are those of
`X`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.ofObjHom`: a morphism of degree zero
  `X ⟶ Y` as a morphism of triples `(X, 𝟙, 0) ⟶ (Y, 𝟙, 0)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.monObjOfObj`: the monoid `(X, 𝟙, 0)`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.isCommMonObj_ofObj`: it is commutative when `X`
  is.
* `CategoryTheory.GradedCategory.TwistedKaroubi.isMonHom_ofObjHom`: morphisms of monoids of
  degree zero are morphisms of monoids of triples.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj Category

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- A morphism `X ⟶ Y` homogeneous of degree zero, as a morphism `(X, 𝟙, 0) ⟶ (Y, 𝟙, 0)`. -/
def ofObjHom {X Y : C} (f : X ⟶ Y) (hf : f ∈ grade (R := R) X Y 0) :
    ofObj (R := R) X ⟶ ofObj (R := R) Y :=
  Hom.mk f (mem_homSubmodule_ofObj.2 hf)

/-- The underlying morphism of `ofObjHom f hf` is `f`. -/
@[simp]
theorem ofObjHom_val {X Y : C} (f : X ⟶ Y) (hf : f ∈ grade (R := R) X Y 0) :
    (ofObjHom f hf).val = f :=
  rfl

/-- `ofObjHom` sends a composite of morphisms of degree zero to the composite. -/
theorem ofObjHom_comp {X Y Z : C} (f : X ⟶ Y) (hf : f ∈ grade (R := R) X Y 0) (g : Y ⟶ Z)
    (hg : g ∈ grade (R := R) Y Z 0) :
    ofObjHom f hf ≫ ofObjHom g hg =
      ofObjHom (f ≫ g) (by simpa using comp_mem (R := R) hg hf) :=
  rfl

/-- `ofObjHom` sends the identity of `X` to the identity of `(X, 𝟙, 0)`. -/
theorem ofObjHom_id (X : C) : ofObjHom (R := R) (𝟙 X) (id_mem X) = 𝟙 (ofObj (R := R) X) :=
  rfl

/-- Equal morphisms of degree zero give equal morphisms `(X, 𝟙, 0) ⟶ (Y, 𝟙, 0)`. -/
theorem ofObjHom_congr {X Y : C} {f g : X ⟶ Y} (hf : f ∈ grade (R := R) X Y 0)
    (hg : g ∈ grade (R := R) X Y 0) (h : f = g) : ofObjHom f hf = ofObjHom g hg :=
  hom_ext h

variable [MonoidalCategory C] [IsGradedMonoidal R C]

/- The tensor product of triples is elaborated through `MonoidalCategory.toMonoidalCategoryStruct`,
as in the monoid-object API, rather than through the direct instance
`CategoryTheory.GradedCategory.TwistedKaroubi.monoidalCategoryStruct`, so that statements here
meet `MonObj.mul` without converting between the two instance paths. -/
attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

/-- The multiplication of `(X, 𝟙, 0)`: that of `X`. -/
def ofObjMul (X : C) [MonObj X] (hμ : μ[X] ∈ grade (R := R) (X ⊗ X) X 0) :
    ofObj (R := R) X ⊗ ofObj (R := R) X ⟶ ofObj (R := R) X :=
  Hom.mk μ[X] ⟨grade_cast hμ (by simp),
    (congrArg (· ≫ μ[X]) (id_tensorHom_id X X)).trans (Category.id_comp _), Category.comp_id _⟩

/-- The unit of `(X, 𝟙, 0)`: that of `X`. -/
def ofObjOne (X : C) [MonObj X] (hη : η[X] ∈ grade (R := R) (𝟙_ C) X 0) :
    𝟙_ (TwistedKaroubi R C) ⟶ ofObj (R := R) X :=
  Hom.mk η[X] ⟨grade_cast hη (by simp), Category.id_comp _, Category.comp_id _⟩

/-- **A monoid of `C` with unit and multiplication of degree zero is a monoid of triples**:
`(X, 𝟙, 0)` with the unit and multiplication of `X`. -/
@[instance_reducible]
def monObjOfObj (X : C) [MonObj X] (hη : η[X] ∈ grade (R := R) (𝟙_ C) X 0)
    (hμ : μ[X] ∈ grade (R := R) (X ⊗ X) X 0) : MonObj (ofObj (R := R) X) where
  one := ofObjOne X hη
  mul := ofObjMul X hμ
  one_mul := by
    have h : (η[X] ⊗ₘ 𝟙 X) ≫ μ[X] = (𝟙 (𝟙_ C) ⊗ₘ 𝟙 X) ≫ (λ_ X).hom := by
      rw [tensorHom_id, id_tensorHom_id, id_comp]
      exact MonObj.one_mul X
    exact hom_ext h
  mul_one := by
    have h : (𝟙 X ⊗ₘ η[X]) ≫ μ[X] = (𝟙 X ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ X).hom := by
      rw [id_tensorHom, id_tensorHom_id, id_comp]
      exact MonObj.mul_one X
    exact hom_ext h
  mul_assoc := by
    have h : (μ[X] ⊗ₘ 𝟙 X) ≫ μ[X] =
        (((𝟙 X ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom) ≫ (𝟙 X ⊗ₘ μ[X]) ≫ μ[X] := by
      rw [id_tensorHom_id, id_tensorHom_id, id_comp, tensorHom_id, id_tensorHom]
      exact MonObj.mul_assoc X
    exact hom_ext h

/-- The underlying morphism of the multiplication of `monObjOfObj X hη hμ` is `μ[X]`. -/
theorem monObjOfObj_mul_val (X : C) [MonObj X] (hη : η[X] ∈ grade (R := R) (𝟙_ C) X 0)
    (hμ : μ[X] ∈ grade (R := R) (X ⊗ X) X 0) :
    (letI := monObjOfObj X hη hμ; μ[ofObj (R := R) X]).val = μ[X] :=
  rfl

/-- The underlying morphism of the unit of `monObjOfObj X hη hμ` is `η[X]`. -/
theorem monObjOfObj_one_val (X : C) [MonObj X] (hη : η[X] ∈ grade (R := R) (𝟙_ C) X 0)
    (hμ : μ[X] ∈ grade (R := R) (X ⊗ X) X 0) :
    (letI := monObjOfObj X hη hμ; η[ofObj (R := R) X]).val = η[X] :=
  rfl

/-- Morphisms of monoids of degree zero are morphisms of the monoids of triples. -/
theorem isMonHom_ofObjHom {X Y : C} [MonObj X] [MonObj Y]
    (hηX : η[X] ∈ grade (R := R) (𝟙_ C) X 0) (hμX : μ[X] ∈ grade (R := R) (X ⊗ X) X 0)
    (hηY : η[Y] ∈ grade (R := R) (𝟙_ C) Y 0) (hμY : μ[Y] ∈ grade (R := R) (Y ⊗ Y) Y 0)
    (f : X ⟶ Y) [IsMonHom f] (hf : f ∈ grade (R := R) X Y 0) :
    letI := monObjOfObj X hηX hμX
    letI := monObjOfObj Y hηY hμY
    IsMonHom (ofObjHom f hf) := by
  let _ := monObjOfObj X hηX hμX
  let _ := monObjOfObj Y hηY hμY
  exact ⟨hom_ext (IsMonHom.one_hom f), hom_ext (IsMonHom.mul_hom f)⟩

/-- A morphism of triples `(X, 𝟙, 0) ⟶ (Y, 𝟙, 0)` is a morphism of monoids as soon as its
underlying morphism of `C` preserves the unit and the multiplication. -/
theorem isMonHom_of_val {X Y : C} [MonObj X] [MonObj Y]
    (hηX : η[X] ∈ grade (R := R) (𝟙_ C) X 0) (hμX : μ[X] ∈ grade (R := R) (X ⊗ X) X 0)
    (hηY : η[Y] ∈ grade (R := R) (𝟙_ C) Y 0) (hμY : μ[Y] ∈ grade (R := R) (Y ⊗ Y) Y 0)
    (g : ofObj (R := R) X ⟶ ofObj (R := R) Y) (h₁ : η[X] ≫ g.val = η[Y])
    (h₂ : μ[X] ≫ g.val = (g.val ⊗ₘ g.val) ≫ μ[Y]) :
    letI := monObjOfObj X hηX hμX
    letI := monObjOfObj Y hηY hμY
    IsMonHom g := by
  let _ := monObjOfObj X hηX hμX
  let _ := monObjOfObj Y hηY hμY
  exact ⟨hom_ext h₁, hom_ext h₂⟩

/-- If `(a ⊗ b) ≫ μ : X ⊗ Y ⟶ P` is an isomorphism of `C` with an inverse of degree zero, the
corresponding morphism `(X, 𝟙, 0) ⊗ (Y, 𝟙, 0) ⟶ (P, 𝟙, 0)` of triples is an isomorphism. -/
theorem isIso_tensorHom_ofObjHom_mul {X Y P : C} [MonObj P]
    (hη : η[P] ∈ grade (R := R) (𝟙_ C) P 0) (hμ : μ[P] ∈ grade (R := R) (P ⊗ P) P 0)
    (a : X ⟶ P) (ha : a ∈ grade (R := R) X P 0) (b : Y ⟶ P) (hb : b ∈ grade (R := R) Y P 0)
    (c : P ⟶ X ⊗ Y) (hc : c ∈ grade (R := R) P (X ⊗ Y) 0)
    (e₁ : ((a ⊗ₘ b) ≫ μ[P]) ≫ c = 𝟙 (X ⊗ Y)) (e₂ : c ≫ (a ⊗ₘ b) ≫ μ[P] = 𝟙 P) :
    letI := monObjOfObj P hη hμ
    IsIso ((ofObjHom a ha ⊗ₘ ofObjHom b hb) ≫ μ[ofObj (R := R) P]) := by
  let _ := monObjOfObj P hη hμ
  exact ⟨Hom.mk c ⟨grade_cast hc (by simp), Category.id_comp _,
      (congrArg (c ≫ ·) (id_tensorHom_id X Y)).trans (Category.comp_id _)⟩,
    hom_ext (e₁.trans (id_tensorHom_id X Y).symm), hom_ext e₂⟩

/-- A commutative monoid of `C` with unit and multiplication of degree zero is a commutative
monoid of triples. -/
theorem isCommMonObj_ofObj [BraidedCategory C] [IsGradedBraided R C] (X : C) [MonObj X]
    [IsCommMonObj X] (hη : η[X] ∈ grade (R := R) (𝟙_ C) X 0)
    (hμ : μ[X] ∈ grade (R := R) (X ⊗ X) X 0) :
    letI := monObjOfObj X hη hμ
    IsCommMonObj (ofObj (R := R) X) := by
  let _ := monObjOfObj X hη hμ
  have h : ((𝟙 X ⊗ₘ 𝟙 X) ≫ (β_ X X).hom) ≫ μ[X] = μ[X] := by
    rw [id_tensorHom_id, id_comp]
    exact IsCommMonObj.mul_comm X
  exact ⟨hom_ext h⟩

end CategoryTheory.GradedCategory.TwistedKaroubi

end
