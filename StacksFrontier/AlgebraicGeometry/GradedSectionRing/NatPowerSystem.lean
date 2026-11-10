module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.PowerSystemComparison
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Basic

/-!
# The iterated tensor powers as a power system

Let `C` be a monoidal category and `L` an object of `C`. The iterated tensor powers
`Stacks.TensorPowers.natTensorPow L n`, with `natTensorPow L 0 = 𝟙_ C` and
`natTensorPow L (n + 1) = natTensorPow L n ⊗ L`, form a `Stacks.Monoidal.PowerSystem` whose
zeroth-power identification and successor comparisons are identities. Its multiplication
isomorphisms are `Stacks.GradedSections.powAddIso`, and its product of global sections is
`Stacks.GradedSections.mul`. For an invertible sheaf of modules `L`, the comparison of this power
system with the integer tensor powers of `L` is multiplicative.

## Main definitions

* `Stacks.GradedSections.natPowerSystem`: the iterated tensor powers of `L` as a power system.
* `Stacks.SheafOfModules.Invertible.natTensorPowCompare`: the comparison
  `L ^⊗ n ≅ L^{⊗ n}` of the iterated tensor powers of an invertible sheaf of modules with its
  integer tensor powers, in nonnegative degree.

## Main results

* `Stacks.GradedSections.natPowerSystem_mulIso`: the multiplication isomorphisms of the power
  system of iterated powers are `Stacks.GradedSections.powAddIso`.
* `Stacks.GradedSections.mulMap_eq_powAdd`: multiplication by a section is that section
  whiskered into the first factor of the multiplication morphism.
* `Stacks.GradedSections.mul_eq_sectionMul`: the product of two sections of iterated tensor
  powers is the power-system product of global sections.
* `Stacks.Monoidal.PowerSystem.compare_sectionMul` and
  `Stacks.Monoidal.PowerSystem.compare_sectionOne`: **the comparison of two power systems is a
  map of graded monoids on global sections.**
* `Stacks.SheafOfModules.Invertible.natTensorPowCompare_mul`: **the comparison of the two
  families of tensor powers of an invertible sheaf of modules is multiplicative**, against
  `powAddIso` on one side and `Stacks.SheafOfModules.Invertible.tensorPowerMulIso` on the
  other.
* `Stacks.SheafOfModules.Invertible.mul_comp_natTensorPowCompare` and
  `Stacks.SheafOfModules.Invertible.sectionMul_natTensorPowCompare`: the same statement on
  global sections, the second for the product `Stacks.SheafOfModules.Invertible.sectionMul` of
  sections in `SheafOfModules.sections`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.Monoidal.PowerSystem

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A product of global sections is the second factor followed by the first one whiskered in. -/
theorem sectionTensor_eq_comp_whiskerRight {M N : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N) :
    sectionTensor s t = t ≫ (λ_ N).inv ≫ (s ▷ N) := by
  rw [sectionTensor, tensorHom_def', ← Category.assoc, ← leftUnitor_inv_naturality,
    Category.assoc]

/-- **The comparison of two power systems carries the unit section to the unit section.** -/
theorem compare_sectionOne (S T : PowerSystem C) (β : S.gen ≅ T.gen) :
    S.sectionOne ≫ (compare S T β 0).hom = T.sectionOne := by
  simp [sectionOne, compare_zero]

/-- **The comparison of two power systems is multiplicative on global sections.** -/
theorem compare_sectionMul (S T : PowerSystem C) (β : S.gen ≅ T.gen) {a b : ℕ}
    (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ S.obj b) :
    T.sectionMul (s ≫ (compare S T β a).hom) (t ≫ (compare S T β b).hom)
      = S.sectionMul s t ≫ (compare S T β (a + b)).hom := by
  rw [sectionMul, sectionMul, ← sectionTensor_comp_tensorHom, Category.assoc, compare_mul,
    Category.assoc]

end Stacks.Monoidal.PowerSystem

namespace Stacks.GradedSections

open Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- The iterated tensor powers of `L` as a power system: both the identification of the zeroth
power with the tensor unit and the successor comparison `L ^⊗ n ⊗ L ≅ L ^⊗ (n + 1)` are the
identity. -/
@[implicit_reducible]
def natPowerSystem (L : C) : Stacks.Monoidal.PowerSystem C where
  gen := L
  obj := natTensorPow L
  objZeroIso := Iso.refl _
  succIso _ := Iso.refl _

/-- The generator of `natPowerSystem L` is `L`. -/
@[simp]
theorem natPowerSystem_gen (L : C) : (natPowerSystem L).gen = L := rfl

/-- The `n`-th object of `natPowerSystem L` is `natTensorPow L n`. -/
@[simp]
theorem natPowerSystem_obj (L : C) (n : ℕ) : (natPowerSystem L).obj n = natTensorPow L n := rfl

/-- The zeroth-power identification of `natPowerSystem L` is the identity. -/
@[simp]
theorem natPowerSystem_objZeroIso (L : C) : (natPowerSystem L).objZeroIso = Iso.refl _ := rfl

/-- The successor comparisons of `natPowerSystem L` are the identity. -/
@[simp]
theorem natPowerSystem_succIso (L : C) (n : ℕ) : (natPowerSystem L).succIso n = Iso.refl _ := rfl

/-- **The multiplication isomorphisms of the power system of iterated tensor powers are
`powAddIso`.** -/
theorem natPowerSystem_mulIso (L : C) (n : ℕ) : ∀ m : ℕ,
    (natPowerSystem L).mulIso n m = powAddIso L n m
  | 0 => by
      refine Iso.ext ?_
      change (natTensorPow L n ◁ 𝟙 (𝟙_ C)) ≫ (ρ_ (natTensorPow L n)).hom
        = (powAddIso L n 0).hom
      rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, powAddIso_zero_right]
  | m + 1 => by
      refine Iso.ext ?_
      change (natTensorPow L n ◁ 𝟙 (natTensorPow L m ⊗ L)) ≫
          (α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫
          (((natPowerSystem L).mulIso n m).hom ▷ L) ≫ 𝟙 ((natPowerSystem L).obj (n + m) ⊗ L)
        = (powAddIso L n (m + 1)).hom
      rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id,
        natPowerSystem_mulIso L n m, powAddIso_hom, powAddIso_hom, powAdd_succ]

/-- A global section whiskered into the first factor of a nested tensor product, read through
the left unitor, splits off the last factor. -/
theorem coherence_leftUnitor_inv_whiskerRight {A B D E : C} (s : 𝟙_ C ⟶ A) (f : A ⊗ B ⟶ E) :
    (λ_ (B ⊗ D)).inv ≫ (s ▷ (B ⊗ D)) ≫ (α_ A B D).inv ≫ (f ▷ D)
      = ((λ_ B).inv ≫ (s ▷ B) ≫ f) ▷ D := by
  have hcoh : (λ_ (B ⊗ D)).inv ≫ (α_ (𝟙_ C) B D).inv = (λ_ B).inv ▷ D := by
    monoidal_coherence
  rw [associator_inv_naturality_left_assoc, ← Category.assoc, hcoh]
  simp only [comp_whiskerRight]

/-- **Multiplication by a section is that section whiskered into the first factor of the
multiplication morphism.** `Stacks.GradedSections.mulMap s m` is the left unitor followed by
`s` whiskered by `natTensorPow L m` and the multiplication morphism `powAdd L n m`. -/
theorem mulMap_eq_powAdd {L : C} {n : ℕ} (s : powSections L n) : ∀ m : ℕ,
    mulMap s m = (λ_ (natTensorPow L m)).inv ≫ (s ▷ natTensorPow L m) ≫ powAdd L n m
  | 0 => by
      change s = (λ_ (𝟙_ C)).inv ≫ (s ▷ (𝟙_ C)) ≫ (ρ_ (natTensorPow L n)).hom
      rw [rightUnitor_naturality, ← unitors_equal, Iso.inv_hom_id_assoc]
  | m + 1 => by
      change mulMap s m ▷ L
        = (λ_ (natTensorPow L m ⊗ L)).inv ≫ (s ▷ (natTensorPow L m ⊗ L)) ≫
            (α_ (natTensorPow L n) (natTensorPow L m) L).inv ≫ (powAdd L n m ▷ L)
      rw [coherence_leftUnitor_inv_whiskerRight, mulMap_eq_powAdd s m]

/-- **The product of two sections of iterated tensor powers is the power-system product of
global sections.** -/
theorem mul_eq_sectionMul {L : C} {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    mul s t = (natPowerSystem L).sectionMul s t := by
  rw [Stacks.Monoidal.PowerSystem.sectionMul, natPowerSystem_mulIso, powAddIso_hom, mul_def,
    mulMap_eq_powAdd, Stacks.Monoidal.PowerSystem.sectionTensor_eq_comp_whiskerRight]
  simp only [natPowerSystem_obj, Category.assoc]

/-- The unit section of the power system of iterated tensor powers is the identity of the tensor
unit. -/
@[simp]
theorem natPowerSystem_sectionOne (L : C) :
    (natPowerSystem L).sectionOne = 𝟙 (𝟙_ C) := rfl

end Stacks.GradedSections

namespace Stacks.SheafOfModules.Invertible

open Stacks.TensorPowers Stacks.GradedSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.braidedCategory Stacks.SheafOfModules.symmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]

/-- **The comparison of the iterated tensor powers of an invertible sheaf of modules with its
integer tensor powers, in nonnegative degree.** It is the comparison
`Stacks.Monoidal.PowerSystem.compare` of the two power systems along the identity of `L`. -/
def natTensorPowCompare (n : ℕ) :
    natTensorPow L n ≅ tensorPower O hO L (n : ℤ) :=
  Stacks.Monoidal.PowerSystem.compare (natPowerSystem L) (tensorPowerSystem O hO L)
    (Iso.refl L) n

/-- **The comparison of the two families of tensor powers is multiplicative.** On one side is
`Stacks.GradedSections.powAddIso`, the multiplication of the iterated powers; on the other
`Stacks.SheafOfModules.Invertible.tensorPowerMulIso`, the multiplication of the integer tensor
powers in nonnegative degree. -/
theorem natTensorPowCompare_mul (a b : ℕ) :
    ((natTensorPowCompare O hO L a).hom ⊗ₘ (natTensorPowCompare O hO L b).hom) ≫
        (tensorPowerMulIso O hO L a b).hom
      = (powAddIso L a b).hom ≫ (natTensorPowCompare O hO L (a + b)).hom := by
  rw [← natPowerSystem_mulIso]
  exact Stacks.Monoidal.PowerSystem.compare_mul (natPowerSystem L) (tensorPowerSystem O hO L)
    (Iso.refl L) a b

/-- The comparison carries the unit section of the iterated powers to the unit section of the
integer tensor powers. -/
theorem natTensorPowCompare_sectionOne :
    (natPowerSystem L).sectionOne ≫ (natTensorPowCompare O hO L 0).hom
      = (tensorPowerSystem O hO L).sectionOne :=
  Stacks.Monoidal.PowerSystem.compare_sectionOne (natPowerSystem L) (tensorPowerSystem O hO L)
    (Iso.refl L)

/-- **The comparison of the two families of tensor powers is multiplicative on global sections**,
read as morphisms out of the tensor unit: the product of two sections of iterated powers, pushed
along the comparison, is the product of their images. -/
theorem mul_comp_natTensorPowCompare {a b : ℕ} (s : powSections L a) (t : powSections L b) :
    mul s t ≫ (natTensorPowCompare O hO L (a + b)).hom
      = (tensorPowerSystem O hO L).sectionMul (s ≫ (natTensorPowCompare O hO L a).hom)
          (t ≫ (natTensorPowCompare O hO L b).hom) := by
  rw [mul_eq_sectionMul]
  exact (Stacks.Monoidal.PowerSystem.compare_sectionMul (natPowerSystem L)
    (tensorPowerSystem O hO L) (Iso.refl L) s t).symm

/-- **The comparison of the two families of tensor powers is multiplicative on global
sections**, stated with the product `Stacks.SheafOfModules.Invertible.sectionMul` of sections
in `SheafOfModules.sections`. -/
theorem sectionMul_natTensorPowCompare {a b : ℕ} (s : powSections L a) (t : powSections L b) :
    sectionMul O hO L (homToSection O hO L (s ≫ (natTensorPowCompare O hO L a).hom))
        (homToSection O hO L (t ≫ (natTensorPowCompare O hO L b).hom))
      = homToSection O hO L (mul s t ≫ (natTensorPowCompare O hO L (a + b)).hom) := by
  rw [sectionMul, sectionToHom_homToSection, sectionToHom_homToSection,
    mul_comp_natTensorPowCompare]

end Stacks.SheafOfModules.Invertible

end
