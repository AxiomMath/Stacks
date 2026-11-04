module

public import StacksFrontier.CategoryTheory.Graded.DegreeZero
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonoidal
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The degree-zero category of a graded symmetric monoidal category

Let `C` be a category graded over a ring `R`. Its degree-zero category `DegreeZero R C`
(Stacks 09ML) has the same objects and the homogeneous morphisms of degree zero. These form a
submodule of each morphism module, so `DegreeZero R C` is `R`-linear. If `C` carries a graded
monoidal structure (`CategoryTheory.GradedCategory.IsGradedMonoidal`: degrees add under the
tensor product, and the constraints have degree zero), the tensor product and the constraints of
`C` restrict to `DegreeZero R C`, which is then monoidal; it is braided, or symmetric, if `C` is
and the commutativity constraint has degree zero.

For the graded category of correspondences between smooth projective schemes over a field this
is the symmetric monoidal category of correspondences of degree zero of Stacks 0FG7, on which the
functors of Stacks 0FGH are defined.

## Main definitions

* `CategoryTheory.GradedCategory.DegreeZero.ι`: the faithful functor `DegreeZero R C ⥤ C`.
* `CategoryTheory.GradedCategory.DegreeZero.preadditive`, `...linear`: the `R`-linear structure.
* `CategoryTheory.GradedCategory.DegreeZero.monoidalCategory`, `...braidedCategory`,
  `...symmetricCategory`: the monoidal, braided and symmetric structures, for which `ι` is
  braided monoidal with identity comparison morphisms.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category

namespace CategoryTheory.GradedCategory.DegreeZero

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- An object of the degree-zero category, as an object of `C`. -/
abbrev toC (X : DegreeZero R C) : C := X

/-- A morphism of the degree-zero category from a homogeneous morphism of degree zero. -/
abbrev homMk {X Y : DegreeZero R C} (f : X.toC ⟶ Y.toC) (hf : f ∈ grade (R := R) X.toC Y.toC 0) :
    X ⟶ Y :=
  ⟨f, hf⟩

/-- The underlying morphism of `C` of a morphism of the degree-zero category. -/
abbrev val {X Y : DegreeZero R C} (f : X ⟶ Y) : X.toC ⟶ Y.toC :=
  Subtype.val (p := fun a ↦ a ∈ grade (R := R) X.toC Y.toC 0) f

/-- The underlying morphism of a morphism of the degree-zero category is homogeneous of degree
zero. -/
theorem val_mem {X Y : DegreeZero R C} (f : X ⟶ Y) : val f ∈ grade (R := R) X.toC Y.toC 0 :=
  f.2

/-- Two morphisms of the degree-zero category are equal if their underlying morphisms of `C`
are. -/
@[ext]
theorem hom_ext {X Y : DegreeZero R C} {f g : X ⟶ Y} (h : val f = val g) : f = g :=
  Subtype.ext h

/-- The underlying morphism of `homMk f hf` is `f`. -/
@[simp]
theorem homMk_val {X Y : DegreeZero R C} (f : X.toC ⟶ Y.toC)
    (hf : f ∈ grade (R := R) X.toC Y.toC 0) : val (homMk f hf) = f :=
  rfl

/-- The underlying morphism of an identity is the identity of `C`. -/
@[simp]
theorem id_val (X : DegreeZero R C) : val (𝟙 X) = 𝟙 X.toC :=
  rfl

/-- The underlying morphism of a composite is the composite in `C`. -/
@[simp]
theorem comp_val {X Y Z : DegreeZero R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    val (f ≫ g) = val f ≫ val g :=
  rfl

variable (R C) in
/-- The inclusion of the degree-zero category into the graded category. -/
@[simps]
def ι : DegreeZero R C ⥤ C where
  obj X := X.toC
  map f := val f

/-- The inclusion of the degree-zero category is faithful. -/
instance : (ι R C).Faithful where
  map_injective h := hom_ext h

/-! ### The linear structure -/

/-- The degree-zero category is preadditive: the degree-zero morphisms form a subgroup. -/
instance preadditive : Preadditive (DegreeZero R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (grade (R := R) X.toC Y.toC 0))
  add_comp _ _ _ _ _ _ := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _)

/-- The underlying morphism of a sum is the sum in `C`. -/
@[simp]
theorem add_val {X Y : DegreeZero R C} (f g : X ⟶ Y) : val (f + g) = val f + val g :=
  rfl

/-- The underlying morphism of the zero morphism is the zero morphism of `C`. -/
@[simp]
theorem zero_val (X Y : DegreeZero R C) : val (0 : X ⟶ Y) = 0 :=
  rfl

/-- The degree-zero category is `R`-linear: the degree-zero morphisms form a submodule. -/
instance linear : Linear R (DegreeZero R C) where
  homModule X Y := inferInstanceAs (Module R (grade (R := R) X.toC Y.toC 0))
  smul_comp _ _ _ _ _ _ := Subtype.ext (Linear.smul_comp _ _ _ _ _ _)
  comp_smul _ _ _ _ _ _ := Subtype.ext (Linear.comp_smul _ _ _ _ _ _)

/-- The underlying morphism of a scalar multiple is the scalar multiple in `C`. -/
@[simp]
theorem smul_val {X Y : DegreeZero R C} (r : R) (f : X ⟶ Y) : val (r • f) = r • val f :=
  rfl

/-- The inclusion of the degree-zero category is additive. -/
instance : (ι R C).Additive where

/-- The inclusion of the degree-zero category is `R`-linear. -/
instance : Functor.Linear R (ι R C) where

/-! ### The monoidal structure -/

section Monoidal

variable [MonoidalCategory C] [IsGradedMonoidal R C]

/-- The tensor product of two homogeneous morphisms of degree zero has degree zero. -/
theorem tensorHom_mem {X₁ Y₁ X₂ Y₂ : C} {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂}
    (hf : f ∈ grade (R := R) X₁ Y₁ 0) (hg : g ∈ grade (R := R) X₂ Y₂ 0) :
    f ⊗ₘ g ∈ grade (R := R) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) 0 := by
  simpa using IsGradedMonoidal.tensorHom_mem (R := R) hf hg

/-- An isomorphism of `C` whose two directions have degree zero, as an isomorphism of the
degree-zero category. -/
def isoMk {X Y : DegreeZero R C} (e : X.toC ≅ Y.toC) (hhom : e.hom ∈ grade (R := R) _ _ 0)
    (hinv : e.inv ∈ grade (R := R) _ _ 0) : X ≅ Y where
  hom := homMk e.hom hhom
  inv := homMk e.inv hinv
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

/-- The monoidal data on the degree-zero category: those of `C`. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (DegreeZero R C) where
  tensorObj X Y := (X.toC ⊗ Y.toC : C)
  whiskerLeft X _ _ f := homMk (X.toC ◁ val f) (by
    rw [← id_tensorHom]; exact tensorHom_mem (id_mem _) (val_mem f))
  whiskerRight f Y := homMk (val f ▷ Y.toC) (by
    rw [← tensorHom_id]; exact tensorHom_mem (val_mem f) (id_mem _))
  tensorHom f g := homMk (val f ⊗ₘ val g) (tensorHom_mem (val_mem f) (val_mem g))
  tensorUnit := (𝟙_ C : C)
  associator X Y Z := isoMk (α_ X.toC Y.toC Z.toC)
    (IsGradedMonoidal.associator_hom_mem _ _ _) (IsGradedMonoidal.associator_inv_mem _ _ _)
  leftUnitor X := isoMk (λ_ X.toC) (IsGradedMonoidal.leftUnitor_hom_mem _)
    (IsGradedMonoidal.leftUnitor_inv_mem _)
  rightUnitor X := isoMk (ρ_ X.toC) (IsGradedMonoidal.rightUnitor_hom_mem _)
    (IsGradedMonoidal.rightUnitor_inv_mem _)

/-- The data needed to induce the monoidal axioms along `ι`: the tensor product, the unit and
the constraints are sent to those of `C` on the nose. -/
def inducingFunctorData : Monoidal.InducingFunctorData (ι R C) where
  μIso X Y := Iso.refl (X.toC ⊗ Y.toC)
  εIso := Iso.refl (𝟙_ C)
  whiskerLeft_eq X Y Y' f := by
    change X.toC ◁ val f = 𝟙 _ ≫ X.toC ◁ val f ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  whiskerRight_eq f Y := by
    change val f ▷ Y.toC = 𝟙 _ ≫ val f ▷ Y.toC ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  tensorHom_eq f g := by
    change val f ⊗ₘ val g = 𝟙 _ ≫ (val f ⊗ₘ val g) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  associator_eq X Y Z := by
    change (α_ X.toC Y.toC Z.toC).hom =
      (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (α_ X.toC Y.toC Z.toC).hom ≫ ((𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _)
    simp
  leftUnitor_eq X := by
    change (λ_ X.toC).hom = (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (λ_ X.toC).hom
    simp
  rightUnitor_eq X := by
    change (ρ_ X.toC).hom = (𝟙 _ ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫ (ρ_ X.toC).hom
    simp

/-- The degree-zero category of a graded monoidal category is monoidal. -/
instance monoidalCategory : MonoidalCategory (DegreeZero R C) :=
  Monoidal.induced (ι R C) inducingFunctorData

/-- The inclusion of the degree-zero category is monoidal. -/
instance ιMonoidal : (ι R C).Monoidal :=
  Monoidal.fromInducedMonoidal (ι R C) inducingFunctorData

/-- The underlying morphism of a tensor product of morphisms is their tensor product in `C`. -/
@[simp] theorem tensorHom_val {X₁ Y₁ X₂ Y₂ : DegreeZero R C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    val (f ⊗ₘ g) = val f ⊗ₘ val g := rfl

/-- The underlying morphism of a left whiskering is the left whiskering in `C`. -/
@[simp] theorem whiskerLeft_val (X : DegreeZero R C) {Y Y' : DegreeZero R C} (f : Y ⟶ Y') :
    val (X ◁ f) = X.toC ◁ val f := rfl

/-- The underlying morphism of a right whiskering is the right whiskering in `C`. -/
@[simp] theorem whiskerRight_val {X X' : DegreeZero R C} (f : X ⟶ X') (Y : DegreeZero R C) :
    val (f ▷ Y) = val f ▷ Y.toC := rfl

/-- The associator of the degree-zero category is that of `C`. -/
@[simp] theorem associator_hom_val (X Y Z : DegreeZero R C) :
    val (α_ X Y Z).hom = (α_ X.toC Y.toC Z.toC).hom := rfl

/-- The inverse associator of the degree-zero category is that of `C`. -/
@[simp] theorem associator_inv_val (X Y Z : DegreeZero R C) :
    val (α_ X Y Z).inv = (α_ X.toC Y.toC Z.toC).inv := rfl

/-- The left unitor of the degree-zero category is that of `C`. -/
@[simp] theorem leftUnitor_hom_val (X : DegreeZero R C) : val (λ_ X).hom = (λ_ X.toC).hom := rfl

/-- The inverse left unitor of the degree-zero category is that of `C`. -/
@[simp] theorem leftUnitor_inv_val (X : DegreeZero R C) : val (λ_ X).inv = (λ_ X.toC).inv := rfl

/-- The right unitor of the degree-zero category is that of `C`. -/
@[simp] theorem rightUnitor_hom_val (X : DegreeZero R C) : val (ρ_ X).hom = (ρ_ X.toC).hom := rfl

/-- The inverse right unitor of the degree-zero category is that of `C`. -/
@[simp] theorem rightUnitor_inv_val (X : DegreeZero R C) : val (ρ_ X).inv = (ρ_ X.toC).inv := rfl

end Monoidal

section Braided

variable [MonoidalCategory C] [IsGradedMonoidal R C] [BraidedCategory C] [IsGradedBraided R C]

/-- The degree-zero category of a graded braided monoidal category is braided, for the
commutativity constraint of `C`. -/
instance braidedCategory : BraidedCategory (DegreeZero R C) :=
  BraidedCategory.ofFaithful (ι R C)
    (fun X Y ↦ isoMk (β_ X.toC Y.toC)
      (IsGradedBraided.braiding_hom_mem _ _) (IsGradedBraided.braiding_inv_mem _ _))
    (fun X Y ↦ by
      change 𝟙 _ ≫ (β_ X.toC Y.toC).hom = (β_ X.toC Y.toC).hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-- The braiding of the degree-zero category is that of `C`. -/
@[simp] theorem braiding_hom_val (X Y : DegreeZero R C) :
    val (β_ X Y).hom = (β_ X.toC Y.toC).hom := rfl

/-- The inclusion of the degree-zero category is braided. -/
instance ιBraided : (ι R C).Braided where
  braided X Y := by
    change 𝟙 _ ≫ (β_ X.toC Y.toC).hom = (β_ X.toC Y.toC).hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

end Braided

section Symmetric

variable [MonoidalCategory C] [IsGradedMonoidal R C] [SymmetricCategory C] [IsGradedBraided R C]

/-- The degree-zero category of a graded symmetric monoidal category is symmetric. -/
instance symmetricCategory : SymmetricCategory (DegreeZero R C) :=
  SymmetricCategory.ofFaithful (ι R C)

end Symmetric

end CategoryTheory.GradedCategory.DegreeZero
