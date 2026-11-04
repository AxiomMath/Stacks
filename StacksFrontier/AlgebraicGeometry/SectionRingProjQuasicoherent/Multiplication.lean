module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Functoriality
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Multiplication by a section of a tensor power, as a morphism of twisted objects

Let `C` be a monoidal category, `L` and `F` objects of `C`, and write `F ⊙ m` for `F` whiskered on
the right by `m` copies of `L` (`Stacks.TwistedSections.twistPow`). A section `a : 𝟙_ C ⟶ L ^⊗ j`
of a tensor power of `L` multiplies twisted objects:

`F ⊙ m ≅ (F ⊙ m) ⊗ 𝟙_ C ⟶ (F ⊙ m) ⊗ L ^⊗ j ≅ F ⊙ (m + j)`.

This file names that morphism, `Stacks.SectionRingProjQuasicoherent.twistMul`, and proves the
three laws the comparison of Stacks Tag 01QJ is built on: it is the action of the graded module
of twisted sections on a twisted *section* (`comp_twistMul`), multiplying by `x` and then by `y`
is multiplying by the product `x y` of the section ring (`twistMul_comp_twistMul`), and it is
natural in `F` (`twistMul_comp_twistPowMap`). The first two are the reason the comparison is
well defined and compatible with a change of denominator; on a scheme, where a section is only
local, they are statements about *morphisms* and so hold on the sections over every open at once.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.twistPowAddIso`: `F ⊙ (m + j) ≅ (F ⊙ m) ⊗ L ^⊗ j`.
* `Stacks.SectionRingProjQuasicoherent.natTensorPowAddIso`: `L ^⊗ (i + j) ≅ L ^⊗ i ⊗ L ^⊗ j`.
* `Stacks.SectionRingProjQuasicoherent.twistMul`: multiplication by `a : 𝟙_ C ⟶ L ^⊗ j`, a
  morphism `F ⊙ m ⟶ F ⊙ (m + j)`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.comp_twistMul`: on a twisted section `t`, multiplication
  by `a` is `a ≫ actMap t j`, the module structure of `Stacks.TwistedSections.twistModule`.
* `Stacks.SectionRingProjQuasicoherent.twistMul_comp_twistMul`: associativity.
* `Stacks.SectionRingProjQuasicoherent.twistMul_comp_twistPowMap`: naturality in `F`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap)
open Stacks.TwistedSections (twistPow twistSections actMap twistPowMap)

universe v u

namespace Stacks.SectionRingProjQuasicoherent

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


/-- **`F ⊙ (m + j) ≅ (F ⊙ m) ⊗ L ^⊗ j`**: the `j` copies of `L` whiskered on one at a time,
collected into one tensor power. -/
def twistPowAddIso (F L : C) (m : ℕ) :
    (j : ℕ) → (twistPow F L (m + j) ≅ twistPow F L m ⊗ natTensorPow L j)
  | 0 => (ρ_ (twistPow F L m)).symm
  | j + 1 => whiskerRightIso (twistPowAddIso F L m j) L ≪≫ α_ _ _ _

/-- For `j = 0`, `twistPowAddIso` is the inverse right unitor of `F ⊙ m`. -/
theorem twistPowAddIso_zero (F L : C) (m : ℕ) :
    twistPowAddIso F L m 0 = (ρ_ (twistPow F L m)).symm := rfl

/-- `twistPowAddIso F L m (j + 1)` is `twistPowAddIso F L m j` whiskered by `L`, followed by the
associator. -/
theorem twistPowAddIso_succ (F L : C) (m j : ℕ) :
    twistPowAddIso F L m (j + 1) = whiskerRightIso (twistPowAddIso F L m j) L ≪≫ α_ _ _ _ :=
  rfl

/-- **`L ^⊗ (i + j) ≅ L ^⊗ i ⊗ L ^⊗ j`**, by the same recursion. -/
def natTensorPowAddIso (L : C) (i : ℕ) :
    (j : ℕ) → (natTensorPow L (i + j) ≅ natTensorPow L i ⊗ natTensorPow L j)
  | 0 => (ρ_ (natTensorPow L i)).symm
  | j + 1 => whiskerRightIso (natTensorPowAddIso L i j) L ≪≫ α_ _ _ _

/-- For `j = 0`, `natTensorPowAddIso` is the inverse right unitor of `L ^⊗ i`. -/
theorem natTensorPowAddIso_zero (L : C) (i : ℕ) :
    natTensorPowAddIso L i 0 = (ρ_ (natTensorPow L i)).symm := rfl

/-- `natTensorPowAddIso L i (j + 1)` is `natTensorPowAddIso L i j` whiskered by `L`, followed by
the associator. -/
theorem natTensorPowAddIso_succ (L : C) (i j : ℕ) :
    natTensorPowAddIso L i (j + 1) = whiskerRightIso (natTensorPowAddIso L i j) L ≪≫ α_ _ _ _ :=
  rfl

/-- The action of a twisted section by `j` copies of `L` is, after collecting them, right
whiskering by `L ^⊗ j`. -/
theorem actMap_comp_twistPowAddIso {F L : C} {m : ℕ} (t : twistSections F L m) (j : ℕ) :
    actMap t j ≫ (twistPowAddIso F L m j).hom =
      (λ_ (natTensorPow L j)).inv ≫ t ▷ natTensorPow L j := by
  induction j with
  | zero =>
      show t ≫ (ρ_ (twistPow F L m)).inv = (λ_ (𝟙_ C : C)).inv ≫ t ▷ (𝟙_ C : C)
      rw [rightUnitor_inv_naturality, MonoidalCategory.unitors_inv_equal]
  | succ j ih =>
      show actMap t j ▷ L ≫ (twistPowAddIso F L m j).hom ▷ L ≫
          (α_ (twistPow F L m) (natTensorPow L j) L).hom =
        (λ_ (natTensorPow L j ⊗ L)).inv ≫ t ▷ (natTensorPow L j ⊗ L)
      rw [← Category.assoc, ← comp_whiskerRight, ih, comp_whiskerRight, Category.assoc,
        associator_naturality_left t (natTensorPow L j) L, leftUnitor_tensor_inv, Category.assoc]

/-- Multiplication by a section of `L ^⊗ i` on the tensor powers is, after collecting the
copies of `L`, left whiskering. -/
theorem mulMap_comp_natTensorPowAddIso {L : C} {i : ℕ} (x : powSections L i) (j : ℕ) :
    mulMap x j ≫ (natTensorPowAddIso L i j).hom =
      (λ_ (natTensorPow L j)).inv ≫ x ▷ natTensorPow L j := by
  induction j with
  | zero =>
      show x ≫ (ρ_ (natTensorPow L i)).inv = (λ_ (𝟙_ C : C)).inv ≫ x ▷ (𝟙_ C : C)
      rw [rightUnitor_inv_naturality, MonoidalCategory.unitors_inv_equal]
  | succ j ih =>
      show mulMap x j ▷ L ≫ (natTensorPowAddIso L i j).hom ▷ L ≫
          (α_ (natTensorPow L i) (natTensorPow L j) L).hom =
        (λ_ (natTensorPow L j ⊗ L)).inv ≫ x ▷ (natTensorPow L j ⊗ L)
      rw [← Category.assoc, ← comp_whiskerRight, ih, comp_whiskerRight, Category.assoc,
        associator_naturality_left x (natTensorPow L j) L, leftUnitor_tensor_inv, Category.assoc]

/-- **Collecting `i + j` copies of `L` at once, or `i` and then `j`.** -/
theorem twistPowAddIso_add (F L : C) (m i : ℕ) :
    ∀ j : ℕ, (twistPowAddIso F L (m + i) j).hom ≫ (twistPowAddIso F L m i).hom ▷ _ ≫
        (α_ _ _ _).hom =
      eqToHom (congrArg (twistPow F L) (Nat.add_assoc m i j)) ≫
        (twistPowAddIso F L m (i + j)).hom ≫ twistPow F L m ◁ (natTensorPowAddIso L i j).hom
  | 0 => by
      show (ρ_ (twistPow F L (m + i))).inv ≫ (twistPowAddIso F L m i).hom ▷ (𝟙_ C) ≫
          (α_ (twistPow F L m) (natTensorPow L i) (𝟙_ C)).hom =
        𝟙 _ ≫ (twistPowAddIso F L m i).hom ≫ twistPow F L m ◁ (ρ_ (natTensorPow L i)).inv
      rw [← rightUnitor_inv_naturality_assoc]
      monoidal
  | j + 1 => by
      have ih := twistPowAddIso_add F L m i j
      have heq : eqToHom (congrArg (twistPow F L) (Nat.add_assoc m i (j + 1))) =
          eqToHom (congrArg (twistPow F L) (Nat.add_assoc m i j)) ▷ L := by
        rw [eqToHom_whiskerRight]
        rfl
      rw [heq]
      show ((twistPowAddIso F L (m + i) j).hom ▷ L ≫
            (α_ (twistPow F L (m + i)) (natTensorPow L j) L).hom) ≫
          (twistPowAddIso F L m i).hom ▷ (natTensorPow L j ⊗ L) ≫
            (α_ (twistPow F L m) (natTensorPow L i) (natTensorPow L j ⊗ L)).hom =
        eqToHom (congrArg (twistPow F L) (Nat.add_assoc m i j)) ▷ L ≫
          ((twistPowAddIso F L m (i + j)).hom ▷ L ≫
            (α_ (twistPow F L m) (natTensorPow L (i + j)) L).hom) ≫
          twistPow F L m ◁ ((natTensorPowAddIso L i j).hom ▷ L ≫
            (α_ (natTensorPow L i) (natTensorPow L j) L).hom)
      have key : ((twistPowAddIso F L (m + i) j).hom ▷ L ≫
            (α_ (twistPow F L (m + i)) (natTensorPow L j) L).hom) ≫
          (twistPowAddIso F L m i).hom ▷ (natTensorPow L j ⊗ L) ≫
            (α_ (twistPow F L m) (natTensorPow L i) (natTensorPow L j ⊗ L)).hom =
          ((twistPowAddIso F L (m + i) j).hom ≫ (twistPowAddIso F L m i).hom ▷ _ ≫
              (α_ _ _ _).hom) ▷ L ≫
            (α_ (twistPow F L m) (natTensorPow L i ⊗ natTensorPow L j) L).hom ≫
              twistPow F L m ◁ (α_ (natTensorPow L i) (natTensorPow L j) L).hom := by
        monoidal
      rw [key, ih]
      monoidal

/-- **Multiplication by a section `a` of `L ^⊗ j`**, as a morphism `F ⊙ m ⟶ F ⊙ (m + j)`. -/
def twistMul {F L : C} {j : ℕ} (a : powSections L j) (m : ℕ) :
    twistPow F L m ⟶ twistPow F L (m + j) :=
  (ρ_ (twistPow F L m)).inv ≫ twistPow F L m ◁ a ≫ (twistPowAddIso F L m j).inv

/-- **On a twisted section, multiplication by `a` is the module action** `a ≫ actMap t j`. -/
@[reassoc]
theorem comp_twistMul {F L : C} {m j : ℕ} (t : twistSections F L m) (a : powSections L j) :
    t ≫ twistMul a m = a ≫ actMap t j := by
  rw [← cancel_mono (twistPowAddIso F L m j).hom, Category.assoc, Category.assoc,
    actMap_comp_twistPowAddIso, twistMul]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange,
    ← MonoidalCategory.unitors_inv_equal, leftUnitor_inv_naturality_assoc]

/-- **Associativity**: multiplying by `x` and then by `y` is multiplying by the product
`x y = y ≫ mulMap x j` of the section ring, up to the reindexing `m + i + j = m + (i + j)`. -/
theorem twistMul_comp_twistMul {F L : C} {i j : ℕ} (x : powSections L i) (y : powSections L j)
    (m : ℕ) :
    twistMul (F := F) x m ≫ twistMul y (m + i) =
      twistMul (mul x y) m ≫ eqToHom (congrArg (twistPow F L) (Nat.add_assoc m i j).symm) := by
  rw [← cancel_mono (twistPowAddIso F L (m + i) j).hom,
    ← cancel_mono ((twistPowAddIso F L m i).hom ▷ natTensorPow L j),
    ← cancel_mono (α_ _ _ _).hom]
  simp only [Category.assoc]
  conv_rhs => rw [twistPowAddIso_add, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hM : mul x y ≫ (natTensorPowAddIso L i j).hom =
      (λ_ (𝟙_ C)).inv ≫ x ▷ (𝟙_ C) ≫ natTensorPow L i ◁ y := by
    rw [Stacks.GradedSections.mul_def, Category.assoc, mulMap_comp_natTensorPowAddIso,
      leftUnitor_inv_naturality_assoc, whisker_exchange]
  simp only [twistMul, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, hM, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp]
  monoidal

/-- `twistPowAddIso` is natural in the twisted object. -/
theorem twistPowAddIso_naturality {F G L : C} (φ : F ⟶ G) (m : ℕ) :
    ∀ j : ℕ, (twistPowAddIso F L m j).hom ≫ twistPowMap L φ m ▷ natTensorPow L j =
      twistPowMap L φ (m + j) ≫ (twistPowAddIso G L m j).hom
  | 0 => by
      show (ρ_ _).inv ≫ twistPowMap L φ m ▷ (𝟙_ C) = twistPowMap L φ m ≫ (ρ_ _).inv
      rw [rightUnitor_inv_naturality]
  | j + 1 => by
      have ih := twistPowAddIso_naturality (L := L) φ m j
      show ((twistPowAddIso F L m j).hom ▷ L ≫ (α_ _ _ _).hom) ≫
          twistPowMap L φ m ▷ (natTensorPow L j ⊗ L) =
        twistPowMap L φ (m + j) ▷ L ≫ (twistPowAddIso G L m j).hom ▷ L ≫ (α_ _ _ _).hom
      rw [Category.assoc, ← associator_naturality_left, ← comp_whiskerRight_assoc, ih,
        comp_whiskerRight_assoc]

/-- **Multiplication by a section is natural in the twisted object.** -/
theorem twistMul_comp_twistPowMap {F G L : C} (φ : F ⟶ G) {j : ℕ} (a : powSections L j)
    (m : ℕ) :
    twistMul (F := F) a m ≫ twistPowMap L φ (m + j) = twistPowMap L φ m ≫ twistMul a m := by
  simp only [twistMul, Category.assoc]
  rw [← cancel_mono (twistPowAddIso G L m j).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← twistPowAddIso_naturality, Iso.inv_hom_id_assoc, whisker_exchange,
    rightUnitor_inv_naturality_assoc]

/-- Reindexing the source degree commutes with multiplication. -/
@[reassoc]
theorem eqToHom_comp_twistMul {F L : C} {j : ℕ} (a : powSections L j) {m m' : ℕ} (h : m = m') :
    eqToHom (congrArg (twistPow F L) h) ≫ twistMul a m' =
      twistMul a m ≫ eqToHom (congrArg (twistPow F L) (congrArg (· + j) h)) := by
  subst h; simp

section Preadditive

variable [Preadditive C]

/-- **Multiplication only depends on the element of the section ring.** Two sections naming the
same element of `Γ_*(L)` in equal degrees multiply alike, up to the reindexing. -/
theorem twistMul_congr_of {F L : C} {i j : ℕ} (h : i = j) (x : powSections L i)
    (y : powSections L j)
    (hxy : DirectSum.of (powSections L) i x = DirectSum.of (powSections L) j y) (m : ℕ) :
    twistMul (F := F) x m ≫ eqToHom (congrArg (twistPow F L) (congrArg (m + ·) h)) =
      twistMul y m := by
  subst h
  obtain rfl := DirectSum.of_injective (β := powSections L) i hxy
  simp

/-- A twisted section reindexed along an equality of degrees names the same element of the direct
sum. -/
theorem of_twistCongr {F L : C} {m m' : ℕ} (h : m = m') (t : twistSections F L m) :
    DirectSum.of (twistSections F L) m' (Stacks.TwistedSections.twistCongr h t) =
      DirectSum.of (twistSections F L) m t := by
  subst h; rw [Stacks.TwistedSections.twistCongr_rfl]

end Preadditive

section Module

variable [Preadditive C] [BraidedCategory C] {L : C} [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L]

/-- **The module structure of `Γ_*(F, L)` on homogeneous elements, through `twistMul`.** -/
theorem of_smul_of_eq_twistMul {F : C} {j m : ℕ} (x : powSections L j)
    (t : twistSections F L m) :
    DirectSum.of (powSections L) j x • DirectSum.of (twistSections F L) m t =
      DirectSum.of (twistSections F L) (m + j) (t ≫ twistMul x m) := by
  rw [Stacks.TwistedSections.of_smul_of, Stacks.TwistedSections.gsmul_def, of_twistCongr,
    comp_twistMul]

end Module

/-- Reindexing the degree of the multiplying section. -/
theorem twistMul_comp_eqToHom {F L : C} {j j' : ℕ} (h : j = j') (a : powSections L j) (m : ℕ) :
    twistMul (F := F) (a ≫ eqToHom (congrArg (natTensorPow L) h)) m =
      twistMul a m ≫ eqToHom (congrArg (twistPow F L) (congrArg (m + ·) h)) := by
  subst h; simp

end Stacks.SectionRingProjQuasicoherent

end
