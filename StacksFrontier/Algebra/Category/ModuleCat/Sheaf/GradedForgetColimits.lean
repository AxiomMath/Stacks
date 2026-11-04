module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting the differential of a differential graded module commutes with colimits

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras, i.e. a cochain complex `A.complex` of sheaves of modules together with an
`R`-bilinear, restriction-compatible multiplication, a global unit in degree `0`, and the signed
Leibniz rule. A right differential graded `A`-module is a cochain complex with a compatible
right action, and `SheafOfModules.forgetToGradedModule A` sends it to the right graded module
over `A.toGradedAlgebra` obtained by forgetting the differential.

This file proves that this functor commutes with all colimits, by exhibiting it as a **left**
adjoint: its right adjoint sends a graded module `N` to the *cofree* differential graded module
on `N`, which is `Nⁿ ⊕ Nⁿ⁺¹` in degree `n` with differential `(x, y) ↦ (y, 0)`.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra` is a sheaf of differential graded algebras over a
  sheaf of rings, and `SheafOfModules.DifferentialGradedAlgebra.toGradedAlgebra` forgets its
  differential.
* `SheafOfModules.DifferentialGradedModule` is a right differential graded module over such an
  algebra; these form a category.
* `SheafOfModules.forgetToGradedModule` forgets the differential of a right differential graded
  module, landing in the category `SheafOfModules.GradedModule` of right graded modules.
* `SheafOfModules.Cofree.cofree` is the cofree differential graded module on a graded module.
* `SheafOfModules.homSections` is the additive map on sections induced by a morphism of sheaves
  of modules, and `SheafOfModules.biprodFst`, `biprodSnd`, `biprodInl`, `biprodInr` are the four
  coordinate maps of a binary biproduct on sections.
* `SheafOfModules.castHom` transports sections along an equality of degrees.

## Main results

* `SheafOfModules.forgetToGradedModule_preservesColimits`: forgetting the differential commutes
  with all colimits.
* `SheafOfModules.forgetToGradedModule_preservesColimitsOfSize` is the same statement for
  colimits of every size.
* `SheafOfModules.forgetAdjunction` is the adjunction, and `SheafOfModules.Cofree.homEquiv` the
  hom-bijection `Hom(forget M, N) ≃ Hom(M, cofree N)` behind it.
* `SheafOfModules.DifferentialGradedAlgebra.one_closed` says the unit of a differential graded
  algebra is closed.

## References

* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe t a m v u s₁ s₂
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Sheaves of modules have binary products. -/
instance hasBinProd : HasBinaryProducts (SheafOfModules.{m} R) := inferInstance
/-- Sheaves of modules have binary biproducts. -/
instance hasBinBiprod : HasBinaryBiproducts (SheafOfModules.{m} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The additive map on sections over `U` induced by a morphism of sheaves of modules. -/
def homSections {M N : SheafOfModules.{m} R} (f : M ⟶ N) (U : Cᵒᵖ) :
    M.val.obj U →+ N.val.obj U := (f.val.app U).hom.toAddMonoidHom

/-- `homSections f U` is evaluation of the component of `f` at `U`. -/
@[simp] theorem homSections_apply {M N : SheafOfModules.{m} R} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj U) : homSections f U x = f.val.app U x := rfl

/-- The map on sections of a composite is the composite of the maps on sections. -/
@[simp] theorem homSections_comp {M N P : SheafOfModules.{m} R} (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ)
    (x : M.val.obj U) : homSections (f ≫ g) U x = homSections g U (homSections f U x) := rfl

/-- The identity morphism induces the identity on sections. -/
@[simp] theorem homSections_id {M : SheafOfModules.{m} R} (U : Cᵒᵖ) (x : M.val.obj U) :
    homSections (𝟙 M) U x = x := rfl

/-- The zero morphism induces the zero map on sections. -/
@[simp] theorem homSections_zero {M N : SheafOfModules.{m} R} (U : Cᵒᵖ) (x : M.val.obj U) :
    homSections (0 : M ⟶ N) U x = 0 := rfl

/-- The map on sections of a sum of morphisms is the sum of the maps on sections. -/
@[simp] theorem homSections_add {M N : SheafOfModules.{m} R} (f g : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj U) : homSections (f + g) U x = homSections f U x + homSections g U x := rfl

/-- The map on sections is linear over the sections of the sheaf of rings. -/
@[simp] theorem homSections_smul {M N : SheafOfModules.{m} R} (f : M ⟶ N) (U : Cᵒᵖ)
    (r : R.obj.obj U) (x : M.val.obj U) :
    homSections f U (r • x) = r • homSections f U x := (f.val.app U).hom.map_smul r x

/-- The map on sections commutes with restriction. -/
theorem homSections_naturality {M N : SheafOfModules.{m} R} (f : M ⟶ N) {U V : Cᵒᵖ} (g : U ⟶ V)
    (x : M.val.obj U) :
    N.val.map g (homSections f U x) = homSections f V (M.val.map g x) :=
  (PresheafOfModules.naturality_apply f.val g x).symm

/-- Equal morphisms induce equal maps on sections. -/
theorem homSections_congr {M N : SheafOfModules.{m} R} {f g : M ⟶ N} (h : f = g) (U : Cᵒᵖ)
    (x : M.val.obj U) : homSections f U x = homSections g U x := by rw [h]

/-- Morphisms inducing the same maps on all sections are equal. -/
theorem homSections_ext {M N : SheafOfModules.{m} R} {f g : M ⟶ N}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U), homSections f U x = homSections g U x) : f = g := by
  ext U x
  exact h U x

/-- Equal composites induce equal iterated maps on sections. -/
private theorem homSections_comp_congr {X Y Z W : SheafOfModules.{m} R} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') (U : Cᵒᵖ) (z : X.val.obj U) :
    homSections g U (homSections f U z) = homSections g' U (homSections f' U z) :=
  (homSections_comp f g U z).symm.trans
    ((homSections_congr h U z).trans (homSections_comp f' g' U z))

/-- The first projection of a binary biproduct of sheaves of modules, on sections over `U`. -/
noncomputable abbrev biprodFst (M N : SheafOfModules.{m} R) (U : Cᵒᵖ) :=
  homSections (biprod.fst : M ⊞ N ⟶ M) U
/-- The second projection of a binary biproduct of sheaves of modules, on sections over `U`. -/
noncomputable abbrev biprodSnd (M N : SheafOfModules.{m} R) (U : Cᵒᵖ) :=
  homSections (biprod.snd : M ⊞ N ⟶ N) U
/-- The first inclusion into a binary biproduct of sheaves of modules, on sections over `U`. -/
noncomputable abbrev biprodInl (M N : SheafOfModules.{m} R) (U : Cᵒᵖ) :=
  homSections (biprod.inl : M ⟶ M ⊞ N) U
/-- The second inclusion into a binary biproduct of sheaves of modules, on sections over `U`. -/
noncomputable abbrev biprodInr (M N : SheafOfModules.{m} R) (U : Cᵒᵖ) :=
  homSections (biprod.inr : N ⟶ M ⊞ N) U

variable (M N : SheafOfModules.{m} R)

/-- The first coordinate of `inl x` is `x`. -/
@[simp] theorem biprodFst_inl (U : Cᵒᵖ) (x : M.val.obj U) :
    biprodFst M N U (biprodInl M N U x) = x := by
  rw [← homSections_comp]; exact homSections_congr biprod.inl_fst U x
/-- The second coordinate of `inl x` is zero. -/
@[simp] theorem biprodSnd_inl (U : Cᵒᵖ) (x : M.val.obj U) :
    biprodSnd M N U (biprodInl M N U x) = 0 := by
  rw [← homSections_comp, homSections_congr biprod.inl_snd U x]; exact homSections_zero U x
/-- The first coordinate of `inr y` is zero. -/
@[simp] theorem biprodFst_inr (U : Cᵒᵖ) (y : N.val.obj U) :
    biprodFst M N U (biprodInr M N U y) = 0 := by
  rw [← homSections_comp, homSections_congr biprod.inr_fst U y]; exact homSections_zero U y
/-- The second coordinate of `inr y` is `y`. -/
@[simp] theorem biprodSnd_inr (U : Cᵒᵖ) (y : N.val.obj U) :
    biprodSnd M N U (biprodInr M N U y) = y := by
  rw [← homSections_comp]; exact homSections_congr biprod.inr_snd U y

/-- A section of a biproduct is the sum of the inclusions of its two coordinates. -/
theorem biprodSections_total (U : Cᵒᵖ) (ξ : (M ⊞ N).val.obj U) :
    biprodInl M N U (biprodFst M N U ξ) + biprodInr M N U (biprodSnd M N U ξ) = ξ := by
  have h := homSections_congr (biprod.total (X := M) (Y := N)) U ξ
  rw [homSections_add] at h
  simpa [← homSections_comp] using h

/-- Sections of a biproduct are determined by their two coordinates. -/
theorem biprodSections_ext (U : Cᵒᵖ) {ξ η : (M ⊞ N).val.obj U}
    (h₁ : biprodFst M N U ξ = biprodFst M N U η)
    (h₂ : biprodSnd M N U ξ = biprodSnd M N U η) : ξ = η := by
  rw [← biprodSections_total M N U ξ, ← biprodSections_total M N U η, h₁, h₂]

end SheafOfModules

namespace SheafOfModules

/-- Transport a term along an equality of indices. -/
abbrev gradedCast {ι : Type*} (X : ι → Type*) {i j : ι} (h : i = j) : X i → X j := h ▸ id

/-- Transport along an equality of indices preserves zero. -/
theorem gradedCast_zero {ι : Type*} (T : ι → Type*) [∀ i, Zero (T i)] {i j : ι} (h : i = j) :
    gradedCast T h (0 : T i) = 0 := by
  cases h
  rfl

/-- Transport along an equality of indices is additive. -/
theorem gradedCast_add {ι : Type*} (T : ι → Type*) [∀ i, Add (T i)] {i j : ι} (h : i = j)
    (x y : T i) : gradedCast T h (x + y) = gradedCast T h x + gradedCast T h y := by
  cases h
  rfl

/-- Transport along an equality of indices commutes with a scalar action. -/
theorem gradedCast_smul {ι : Type*} (T : ι → Type*) {S : Type*} [∀ i, SMul S (T i)] {i j : ι}
    (h : i = j) (r : S) (x : T i) : gradedCast T h (r • x) = r • gradedCast T h x := by
  cases h
  rfl

/-- A transported term is heterogeneously equal to the term it came from. -/
theorem gradedCast_heq {ι : Type*} (T : ι → Type*) {i j : ι} (h : i = j) (x : T i) :
    gradedCast T h x ≍ x := by
  cases h
  rfl

/-- Transport along two equalities of indices is transport along their composite. -/
theorem gradedCast_trans {ι : Type*} (T : ι → Type*) {i j k : ι} (h : i = j) (h' : j = k)
    (x : T i) : gradedCast T h' (gradedCast T h x) = gradedCast T (h.trans h') x := by
  cases h
  cases h'
  rfl

/-- Transport along an equality of indices does not depend on the proof. -/
theorem gradedCast_proof_irrel {ι : Type*} (T : ι → Type*) {i j : ι} (h h' : i = j) (x : T i) :
    gradedCast T h x = gradedCast T h' x := by
  cases h
  rfl

/-- A dependent function applied to heterogeneously equal arguments gives heterogeneously
equal values. -/
theorem heq_dependent_apply {ι : Type*} {B D : ι → Type*} (f : ∀ i, B i → D i) {i j : ι}
    (h : i = j) {x : B i} {y : B j} (hx : x ≍ y) : f i x ≍ f j y := by
  subst h
  exact heq_of_eq (congrArg (f i) (eq_of_heq hx))

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A sheaf of differential graded algebras over a sheaf of rings on a site. -/
@[stacks 0FRF "sheaves of differential graded algebras"]
structure DifferentialGradedAlgebra (R : Sheaf J RingCat.{t}) where
  /-- The underlying cochain complex of sheaves of modules. -/
  complex : CochainComplex (SheafOfModules.{a} R) ℤ
  /-- Graded multiplication, bilinear over the sheaf of rings and natural on the site. -/
  mul : ∀ n i : ℤ, BilinearMap (complex.X n) (complex.X i) (complex.X (n + i))
  /-- The global multiplicative identity in degree zero. -/
  one : (complex.X 0).sections
  /-- Multiplication is associative. -/
  mul_assoc : ∀ (n i j : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U)
      (y : (complex.X i).val.obj U) (z : (complex.X j).val.obj U),
    HEq ((mul (n + i) j).app U ((mul n i).app U x y) z)
      ((mul n (i + j)).app U x ((mul i j).app U y z))
  /-- The global unit is a left identity. -/
  one_mul : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U),
    HEq ((mul 0 n).app U (one.eval U) x) x
  /-- The global unit is a right identity. -/
  mul_one : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U),
    HEq ((mul n 0).app U x (one.eval U)) x
  /-- The differential satisfies the signed graded Leibniz rule. -/
  leibniz : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U)
      (y : (complex.X i).val.obj U),
    (complex.d (n + i) (n + i + 1)).val.app U ((mul n i).app U x y) =
      gradedCast (fun q ↦ (complex.X q).val.obj U) (add_right_comm n 1 i)
          ((mul (n + 1) i).app U ((complex.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (complex.X q).val.obj U) (add_assoc n i 1).symm
            ((mul n (i + 1)).app U x ((complex.d i (i + 1)).val.app U y))

namespace DifferentialGradedAlgebra

variable (A : DifferentialGradedAlgebra.{t, a} R)

/-- The underlying sheaf of graded algebras. -/
@[implicit_reducible]
def toGradedAlgebra : GradedAlgebra.{t, a} R where
  piece := A.complex.X
  mul := A.mul
  one := A.one
  mul_assoc := A.mul_assoc
  one_mul := A.one_mul
  mul_one := A.mul_one

/-- The degree-`n` piece of the underlying graded algebra is the degree-`n` term of the complex. -/
@[simp] theorem toGradedAlgebra_piece (n : ℤ) : A.toGradedAlgebra.piece n = A.complex.X n := rfl
/-- The multiplication of the underlying graded algebra is that of `A`. -/
@[simp] theorem toGradedAlgebra_mul (n i : ℤ) : A.toGradedAlgebra.mul n i = A.mul n i := rfl
/-- The unit of the underlying graded algebra is that of `A`. -/
@[simp] theorem toGradedAlgebra_one : A.toGradedAlgebra.one = A.one := rfl

/-- The unit of a sheaf of differential graded algebras is closed. -/
theorem one_closed (U : Cᵒᵖ) :
    (A.complex.d 0 1).val.app U (A.one.eval U) = 0 := by
  have hunit : (A.mul 0 0).app U (A.one.eval U) (A.one.eval U) = A.one.eval U :=
    eq_of_heq (A.mul_one 0 U (A.one.eval U))
  have hc1 : ∀ x : (A.complex.X (0 + 1 + 0)).val.obj U,
      gradedCast (fun q ↦ (A.complex.X q).val.obj U) (add_right_comm (0 : ℤ) 1 0) x = x :=
    fun _ => rfl
  have hc2 : ∀ x : (A.complex.X (0 + (0 + 1))).val.obj U,
      gradedCast (fun q ↦ (A.complex.X q).val.obj U) (add_assoc (0 : ℤ) 0 1).symm x = x :=
    fun _ => rfl
  have e1 : (A.mul (0 + 1) 0).app U ((A.complex.d 0 (0 + 1)).val.app U (A.one.eval U))
      (A.one.eval U) = (A.complex.d 0 1).val.app U (A.one.eval U) :=
    eq_of_heq (A.mul_one 1 U ((A.complex.d 0 1).val.app U (A.one.eval U)))
  have e2 : (A.mul 0 (0 + 1)).app U (A.one.eval U)
      ((A.complex.d 0 (0 + 1)).val.app U (A.one.eval U))
      = (A.complex.d 0 1).val.app U (A.one.eval U) :=
    eq_of_heq (A.one_mul 1 U ((A.complex.d 0 1).val.app U (A.one.eval U)))
  have hl := A.leibniz 0 0 U (A.one.eval U) (A.one.eval U)
  rw [hunit, hc1, hc2, e1, e2, Int.negOnePow_zero] at hl
  rw [Units.val_one, one_zsmul] at hl
  simpa using hl.symm

end DifferentialGradedAlgebra
end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A right differential graded module over a sheaf of differential graded algebras. -/
@[stacks 0FRI "right differential graded modules"]
structure DifferentialGradedModule (A : DifferentialGradedAlgebra.{t, a} R) where
  /-- The underlying cochain complex of sheaves of modules. -/
  complex : CochainComplex (SheafOfModules.{m} R) ℤ
  /-- The right action of homogeneous sections of the algebra. -/
  mul : ∀ n i : ℤ, BilinearMap (complex.X n) (A.complex.X i) (complex.X (n + i))
  /-- The right action is associative with multiplication in the algebra. -/
  mul_assoc : ∀ (n i j : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U)
      (y : (A.complex.X i).val.obj U) (z : (A.complex.X j).val.obj U),
    HEq ((mul (n + i) j).app U ((mul n i).app U x y) z)
      ((mul n (i + j)).app U x ((A.mul i j).app U y z))
  /-- The unit of the algebra acts as the identity. -/
  mul_one : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U),
    HEq ((mul n 0).app U x (A.one.eval U)) x
  /-- The differential satisfies the signed right-module Leibniz rule. -/
  leibniz : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U)
      (y : (A.complex.X i).val.obj U),
    (complex.d (n + i) (n + i + 1)).val.app U ((mul n i).app U x y) =
      gradedCast (fun q ↦ (complex.X q).val.obj U) (add_right_comm n 1 i)
          ((mul (n + 1) i).app U ((complex.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (complex.X q).val.obj U) (add_assoc n i 1).symm
            ((mul n (i + 1)).app U x ((A.complex.d i (i + 1)).val.app U y))

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- A morphism of right differential graded modules. -/
@[stacks 0FRI "homomorphisms of differential graded modules"]
structure Hom (M N : DifferentialGradedModule.{t, a, m} A) where
  /-- The underlying morphism of cochain complexes. -/
  toHomologicalComplex : M.complex ⟶ N.complex
  /-- The complex morphism commutes with the right action. -/
  map_mul : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U)
      (y : (A.complex.X i).val.obj U),
    (toHomologicalComplex.f (n + i)).val.app U ((M.mul n i).app U x y) =
      (N.mul n i).app U ((toHomologicalComplex.f n).val.app U x) y

/-- Morphisms of differential graded modules agreeing in every degree are equal. -/
@[ext]
theorem Hom.ext {M N : DifferentialGradedModule.{t, a, m} A} {f g : Hom M N}
    (h : ∀ n, f.toHomologicalComplex.f n = g.toHomologicalComplex.f n) : f = g := by
  cases f with
  | mk f hf => cases g with
    | mk g hg =>
      have hfg : f = g := HomologicalComplex.hom_ext f g h
      subst hfg; rfl

/-- The identity morphism of a differential graded module. -/
def Hom.id (M : DifferentialGradedModule.{t, a, m} A) : Hom M M where
  toHomologicalComplex := 𝟙 M.complex
  map_mul _ _ _ _ _ := rfl

/-- Composition of morphisms of differential graded modules. -/
def Hom.comp {M N P : DifferentialGradedModule.{t, a, m} A} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  toHomologicalComplex := f.toHomologicalComplex ≫ g.toHomologicalComplex
  map_mul n i U x y := by
    change (g.toHomologicalComplex.f (n + i)).val.app U
      ((f.toHomologicalComplex.f (n + i)).val.app U ((M.mul n i).app U x y)) = _
    rw [f.map_mul, g.map_mul]; rfl

/-- The category of right differential graded modules over `A`. -/
instance : Category (DifferentialGradedModule.{t, a, m} A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext fun n => by simp [Hom.comp, Hom.id]
  comp_id f := Hom.ext fun n => by simp [Hom.comp, Hom.id]
  assoc f g h := Hom.ext fun n => by simp [Hom.comp]

/-- The identity morphism is the identity in every degree. -/
@[simp] theorem id_f (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (𝟙 M : M ⟶ M).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- A composite of morphisms is the composite in every degree. -/
@[simp] theorem comp_f {M N P : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) (g : N ⟶ P)
    (n : ℤ) : (f ≫ g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

end DifferentialGradedModule

/-- Forget the differential of a right differential graded module. -/
def forgetToGradedModule (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, m} A ⥤ GradedModule.{t, a, m} A.toGradedAlgebra where
  obj M :=
    { piece := M.complex.X
      smul := fun n i U => (M.mul n i).app U
      smul_smul_left := fun n i U r x y => (M.mul n i).map_smul_left U r x y
      smul_smul_right := fun n i U r x y => (M.mul n i).map_smul_right U r x y
      smul_naturality := fun n i {_ _} f x y => (M.mul n i).naturality f x y
      smul_mul := M.mul_assoc
      smul_one := M.mul_one }
  map f := { app := fun n => f.toHomologicalComplex.f n, map_smul := f.map_mul }
  map_id _ := GradedModule.Hom.ext fun _ => rfl
  map_comp _ _ := GradedModule.Hom.ext fun _ => rfl

/-- The degree-`n` piece of the forgotten module is the degree-`n` term of the complex. -/
@[simp] theorem forgetToGradedModule_obj_piece (A : DifferentialGradedAlgebra.{t, a} R)
    (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    ((forgetToGradedModule A).obj M).piece n = M.complex.X n := rfl

/-- The degree-`n` component of the forgotten morphism is that of the complex morphism. -/
@[simp] theorem forgetToGradedModule_map_app (A : DifferentialGradedAlgebra.{t, a} R)
    {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) (n : ℤ) :
    ((forgetToGradedModule A).map f).app n = f.toHomologicalComplex.f n := rfl

namespace GradedModule
variable {A' : GradedAlgebra.{t, a} R}

/-- Transporting the module argument of the action along an equality of degrees. -/
theorem smul_gradedCast_left (N : GradedModule.{t, a, m} A') {n n' i : ℤ} (h : n = n')
    (U : Cᵒᵖ) (x : (N.piece n).val.obj U) (y : (A'.piece i).val.obj U) :
    N.smul n' i U (gradedCast (fun q ↦ (N.piece q).val.obj U) h x) y
      = gradedCast (fun q ↦ (N.piece q).val.obj U) (by rw [h]) (N.smul n i U x y) := by
  subst h; rfl

/-- Transporting the algebra argument of the action along an equality of degrees. -/
theorem smul_gradedCast_right (N : GradedModule.{t, a, m} A') {n i i' : ℤ} (h : i = i')
    (U : Cᵒᵖ) (x : (N.piece n).val.obj U) (y : (A'.piece i).val.obj U) :
    N.smul n i' U x (gradedCast (fun q ↦ (A'.piece q).val.obj U) h y)
      = gradedCast (fun q ↦ (N.piece q).val.obj U) (by rw [h]) (N.smul n i U x y) := by
  subst h; rfl

end GradedModule
end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transport of sections along an equality of degrees, as an additive map. -/
def castHom (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ) :
    (X i).val.obj U →+ (X j).val.obj U := by subst h; exact AddMonoidHom.id _

/-- `castHom` is `gradedCast` on sections. -/
theorem castHom_apply (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (X i).val.obj U) :
    castHom X h U x = gradedCast (fun q ↦ (X q).val.obj U) h x := by subst h; rfl

/-- Transport along an equality of degrees is linear over the sheaf of rings. -/
theorem castHom_smul (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (r : R.obj.obj U) (x : (X i).val.obj U) :
    castHom X h U (r • x) = r • castHom X h U x := by subst h; rfl

/-- Transport along an equality of degrees commutes with restriction. -/
theorem castHom_naturality (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) {U V : Cᵒᵖ}
    (g : U ⟶ V) (x : (X i).val.obj U) :
    (X j).val.map g (castHom X h U x) = castHom X h V ((X i).val.map g x) := by subst h; rfl

/-- Restriction of sections commutes with integer multiples. -/
theorem map_zsmul_sections (X : SheafOfModules.{m} R) {U V : Cᵒᵖ} (g : U ⟶ V) (k : ℤ)
    (x : X.val.obj U) : X.val.map g (k • x) = k • X.val.map g x :=
  (X.val.map g).hom.toAddMonoidHom.map_zsmul k x

/-- Transport along `rfl` is the identity. -/
theorem castHom_rfl (X : ℤ → SheafOfModules.{m} R) {i : ℤ} (U : Cᵒᵖ)
    (x : (X i).val.obj U) : castHom X (rfl : i = i) U x = x := rfl

/-- A transported section is heterogeneously equal to the section it came from. -/
theorem heq_castHom (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (X i).val.obj U) : HEq (castHom X h U x) x := by subst h; rfl

namespace Cofree

variable {A : DifferentialGradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A.toGradedAlgebra)

/-- The degree-`n` piece of the cofree differential graded module on a graded module. -/
noncomputable abbrev piece (n : ℤ) : SheafOfModules.{m} R := N.piece n ⊞ N.piece (n + 1)

/-- The `Nᵏ` coordinate of a section of the degree-`k` piece of the cofree module. -/
noncomputable abbrev coordFst (k : ℤ) (U : Cᵒᵖ) := biprodFst (N.piece k) (N.piece (k + 1)) U
/-- The `Nᵏ⁺¹` coordinate of a section of the degree-`k` piece of the cofree module. -/
noncomputable abbrev coordSnd (k : ℤ) (U : Cᵒᵖ) := biprodSnd (N.piece k) (N.piece (k + 1)) U
/-- The inclusion of sections of `Nᵏ` into the degree-`k` piece of the cofree module. -/
noncomputable abbrev coordInl (k : ℤ) (U : Cᵒᵖ) := biprodInl (N.piece k) (N.piece (k + 1)) U
/-- The inclusion of sections of `Nᵏ⁺¹` into the degree-`k` piece of the cofree module. -/
noncomputable abbrev coordInr (k : ℤ) (U : Cᵒᵖ) := biprodInr (N.piece k) (N.piece (k + 1)) U

/-- Sections of a piece of the cofree module are determined by their two coordinates. -/
theorem sections_ext {k : ℤ} (U : Cᵒᵖ) {ξ η : (piece N k).val.obj U}
    (h₁ : coordFst N k U ξ = coordFst N k U η) (h₂ : coordSnd N k U ξ = coordSnd N k U η) : ξ = η :=
  biprodSections_ext _ _ U h₁ h₂

/-- Two sections in propositionally equal degrees agree as soon as their coordinates do. -/
theorem heq_of_coords {k k' : ℤ} (h : k = k') (U : Cᵒᵖ)
    (ξ : (piece N k).val.obj U) (ξ' : (piece N k').val.obj U)
    (h₁ : HEq (coordFst N k U ξ) (coordFst N k' U ξ'))
    (h₂ : HEq (coordSnd N k U ξ) (coordSnd N k' U ξ')) :
    HEq ξ ξ' := by
  subst h
  exact heq_of_eq (sections_ext N U (eq_of_heq h₁) (eq_of_heq h₂))

/-- The differential of the cofree module: it sends `(x, y)` in degree `n` to `(y, 0)`. -/
noncomputable def d (n : ℤ) : piece N n ⟶ piece N (n + 1) := biprod.snd ≫ biprod.inl

/-- The differential of the cofree module squares to zero. -/
theorem d_d (n : ℤ) : d N n ≫ d N (n + 1) = 0 := by
  simp only [d, Category.assoc, biprod.inl_snd_assoc, zero_comp, comp_zero]

/-- The first coordinate of `d (x, y)` is `y`. -/
@[simp] theorem coordFst_d (n : ℤ) (U : Cᵒᵖ) (ξ : (piece N n).val.obj U) :
    coordFst N (n + 1) U (homSections (d N n) U ξ) = coordSnd N n U ξ :=
  biprodFst_inl _ _ U _

/-- The second coordinate of `d (x, y)` is zero. -/
@[simp] theorem coordSnd_d (n : ℤ) (U : Cᵒᵖ) (ξ : (piece N n).val.obj U) :
    coordSnd N (n + 1) U (homSections (d N n) U ξ) = 0 :=
  biprodSnd_inl _ _ U _

/-- The underlying cochain complex of the cofree differential graded module. -/
noncomputable def complex : CochainComplex (SheafOfModules.{m} R) ℤ :=
  CochainComplex.of (piece N) (d N) (d_d N)

/-- The differential of the algebra on sections, as an additive map. -/
noncomputable abbrev algD (i : ℤ) (U : Cᵒᵖ) := homSections (A.complex.d i (i + 1)) U

/-- The action of a homogeneous algebra section `a` of degree `i` on the cofree module, as an
additive map in the module variable: `(x, y) * a = (x a, y a + (-1)ⁿ x (d a))` in degree `n`. -/
noncomputable def mulHom (n i : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U) :
    (piece N n).val.obj U →+ (piece N (n + i)).val.obj U :=
  (coordInl N (n + i) U).comp (((N.smul n i U).flip a).comp (coordFst N n U))
    + (coordInr N (n + i) U).comp
        ((castHom N.piece (add_right_comm n 1 i) U).comp
            (((N.smul (n + 1) i U).flip a).comp (coordSnd N n U))
          + (Int.negOnePow n : ℤ) • (castHom N.piece (add_assoc n i 1).symm U).comp
              (((N.smul n (i + 1) U).flip (algD i U a)).comp (coordFst N n U)))

/-- The action on the cofree module in coordinates. -/
theorem mulHom_apply (n i : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
    (ξ : (piece N n).val.obj U) :
    mulHom N n i U a ξ
      = coordInl N (n + i) U (N.smul n i U (coordFst N n U ξ) a)
        + coordInr N (n + i) U
            (castHom N.piece (add_right_comm n 1 i) U (N.smul (n + 1) i U (coordSnd N n U ξ) a)
              + (Int.negOnePow n : ℤ) • castHom N.piece (add_assoc n i 1).symm U
                  (N.smul n (i + 1) U (coordFst N n U ξ) (algD i U a))) := rfl

/-- The first coordinate of `(x, y) * a` is `x a`. -/
@[simp] theorem coordFst_mulHom (n i : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
    (ξ : (piece N n).val.obj U) :
    coordFst N (n + i) U (mulHom N n i U a ξ) = N.smul n i U (coordFst N n U ξ) a := by
  rw [mulHom_apply, map_add, biprodFst_inl, biprodFst_inr, add_zero]

/-- The second coordinate of `(x, y) * a` in degree `n` is `y a + (-1)ⁿ x (d a)`. -/
@[simp] theorem coordSnd_mulHom (n i : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
    (ξ : (piece N n).val.obj U) :
    coordSnd N (n + i) U (mulHom N n i U a ξ) =
      castHom N.piece (add_right_comm n 1 i) U (N.smul (n + 1) i U (coordSnd N n U ξ) a)
        + (Int.negOnePow n : ℤ) • castHom N.piece (add_assoc n i 1).symm U
            (N.smul n (i + 1) U (coordFst N n U ξ) (algD i U a)) := by
  rw [mulHom_apply, map_add, biprodSnd_inl, biprodSnd_inr, zero_add]

/-- Transport along two equalities of degrees is transport along their composite. -/
theorem castHom_castHom (X : ℤ → SheafOfModules.{m} R) {i j k : ℤ} (h : i = j) (h' : j = k)
    (U : Cᵒᵖ) (x : (X i).val.obj U) :
    castHom X h' U (castHom X h U x) = castHom X (h.trans h') U x := by
  subst h; subst h'; rfl

/-- Heterogeneously equal sections transported into a common degree are equal. -/
theorem castHom_eq_castHom {X : ℤ → SheafOfModules.{m} R} {i i' k : ℤ} (h : i = k) (h' : i' = k)
    (U : Cᵒᵖ) {x : (X i).val.obj U} {y : (X i').val.obj U} (hxy : HEq x y) :
    castHom X h U x = castHom X h' U y :=
  eq_of_heq ((heq_castHom X h U x).trans (hxy.trans (heq_castHom X h' U y).symm))

/-- A section is heterogeneously equal to any section equal to its transport. -/
theorem heq_of_castHom_eq {X : ℤ → SheafOfModules.{m} R} {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    {x : (X i).val.obj U} {y : (X j).val.obj U} (hxy : castHom X h U x = y) : HEq x y :=
  (heq_castHom X h U x).symm.trans (heq_of_eq hxy)

/-- Transport along an equality of degrees preserves zero. -/
theorem castHom_zero (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ) :
    castHom X h U 0 = 0 := map_zero _

/-- Transporting the module argument of the action along an equality of degrees. -/
theorem smul_castHom_left {A' : GradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A')
    {n n' i : ℤ} (h : n = n') (U : Cᵒᵖ) (x : (N.piece n).val.obj U)
    (y : (A'.piece i).val.obj U) :
    N.smul n' i U (castHom N.piece h U x) y
      = castHom N.piece (by rw [h]) U (N.smul n i U x y) := by
  subst h; rfl

/-- Transporting the algebra argument of the action along an equality of degrees. -/
theorem smul_castHom_right {A' : GradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A')
    {n i i' : ℤ} (h : i = i') (U : Cᵒᵖ) (x : (N.piece n).val.obj U)
    (y : (A'.piece i).val.obj U) :
    N.smul n i' U x (castHom A'.piece h U y)
      = castHom N.piece (by rw [h]) U (N.smul n i U x y) := by
  subst h; rfl

/-- The first coordinate commutes with transport along an equality of degrees. -/
theorem coordFst_castHom {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (ζ : (piece N k).val.obj U) :
    coordFst N k' U (castHom (piece N) h U ζ) = castHom N.piece h U (coordFst N k U ζ) := by
  subst h; rfl

/-- The second coordinate commutes with transport along an equality of degrees. -/
theorem coordSnd_castHom {k k' : ℤ} (h : k = k') (U : Cᵒᵖ) (ζ : (piece N k).val.obj U) :
    coordSnd N k' U (castHom (piece N) h U ζ)
      = castHom N.piece (by rw [h]) U (coordSnd N k U ζ) := by
  subst h; rfl

/-- The differential of the algebra is square-zero on sections. -/
theorem algD_algD (i : ℤ) (U : Cᵒᵖ) (x : (A.complex.X i).val.obj U) :
    algD (i + 1) U (algD i U x) = 0 := by
  have h := homSections_congr (A.complex.d_comp_d i (i + 1) (i + 1 + 1)) U x
  rw [homSections_comp] at h
  exact h.trans (homSections_zero U x)

/-- Transport in the algebra argument, with the algebra's own degree family. -/
theorem smul_castHom_algebra {i i' : ℤ} (n : ℤ) (h : i = i') (U : Cᵒᵖ)
    (x : (N.piece n).val.obj U) (y : (A.complex.X i).val.obj U) :
    N.smul n i' U x (castHom A.complex.X h U y)
      = castHom N.piece (by rw [h]) U (N.smul n i U x y) := by
  subst h; rfl

/-- The unit of the algebra acts as the identity on the cofree module. -/
theorem mulHom_one (n : ℤ) (U : Cᵒᵖ) (ξ : (piece N n).val.obj U) :
    HEq (mulHom N n 0 U (A.one.eval U) ξ) ξ := by
  refine heq_of_coords N (add_zero n) U _ _ ?_ ?_
  · rw [coordFst_mulHom]
    exact N.smul_one n U (coordFst N n U ξ)
  · rw [coordSnd_mulHom]
    rw [show algD (A := A) 0 U (A.one.eval U) = 0 from A.one_closed U]
    simp only [map_zero, smul_zero, add_zero]
    exact HEq.trans (heq_castHom _ _ _ _) (N.smul_one (n + 1) U (coordSnd N n U ξ))

/-- The action on the cofree module is associative. -/
theorem mulHom_assoc (n i j : ℤ) (U : Cᵒᵖ) (ξ : (piece N n).val.obj U)
    (a : (A.complex.X i).val.obj U) (b : (A.complex.X j).val.obj U) :
    HEq (mulHom N (n + i) j U b (mulHom N n i U a ξ))
        (mulHom N n (i + j) U ((A.mul i j).app U a b) ξ) := by
  refine heq_of_coords N (add_assoc n i j) U _ _ ?_ ?_
  · rw [coordFst_mulHom, coordFst_mulHom, coordFst_mulHom]
    exact N.smul_mul n i j U (coordFst N n U ξ) a b
  · rw [coordSnd_mulHom, coordSnd_mulHom, coordFst_mulHom, coordSnd_mulHom]
    simp only [algD, homSections_apply]
    rw [A.leibniz i j U a b]
    simp only [← castHom_apply, map_add, map_zsmul, AddMonoidHom.add_apply,
      AddMonoidHom.coe_smul, Pi.smul_apply, smul_castHom_left, smul_castHom_algebra,
      castHom_castHom]
    refine heq_of_castHom_eq (by omega : n + i + j + 1 = n + (i + j) + 1) U ?_
    simp only [map_add, map_zsmul, castHom_castHom, smul_add, smul_smul, add_assoc]
    refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_)
    · exact castHom_eq_castHom _ _ U (N.smul_mul (n + 1) i j U _ a b)
    · exact congrArg _ (castHom_eq_castHom _ _ U (N.smul_mul n (i + 1) j U _ _ b))
    · rw [Int.negOnePow_add, Units.val_mul]
      exact congrArg _ (castHom_eq_castHom _ _ U (N.smul_mul n i (j + 1) U _ a _))

/-- The first coordinate is linear over the sheaf of rings. -/
@[simp] theorem coordFst_smul (k : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (ζ : (piece N k).val.obj U) :
    coordFst N k U (r • ζ) = r • coordFst N k U ζ := homSections_smul _ _ _ _

/-- The second coordinate is linear over the sheaf of rings. -/
@[simp] theorem coordSnd_smul (k : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (ζ : (piece N k).val.obj U) :
    coordSnd N k U (r • ζ) = r • coordSnd N k U ζ := homSections_smul _ _ _ _

/-- The first coordinate commutes with restriction. -/
theorem coordFst_map (k : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V) (ζ : (piece N k).val.obj U) :
    coordFst N k V ((piece N k).val.map g ζ) = (N.piece k).val.map g (coordFst N k U ζ) :=
  (homSections_naturality _ g ζ).symm

/-- The second coordinate commutes with restriction. -/
theorem coordSnd_map (k : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V) (ζ : (piece N k).val.obj U) :
    coordSnd N k V ((piece N k).val.map g ζ) = (N.piece (k + 1)).val.map g (coordSnd N k U ζ) :=
  (homSections_naturality _ g ζ).symm

/-- The action on the cofree module is additive in the algebra variable. -/
theorem mulHom_add_algebra (n i : ℤ) (U : Cᵒᵖ) (a a' : (A.complex.X i).val.obj U)
    (ξ : (piece N n).val.obj U) :
    mulHom N n i U (a + a') ξ = mulHom N n i U a ξ + mulHom N n i U a' ξ := by
  refine sections_ext N U ?_ ?_
  · simp only [map_add, coordFst_mulHom]
  · simp only [map_add, coordSnd_mulHom, smul_add]
    abel

/-- The action on the cofree module is linear over the sheaf of rings in the module variable. -/
theorem mulHom_smul_module (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (a : (A.complex.X i).val.obj U) (ξ : (piece N n).val.obj U) :
    mulHom N n i U a (r • ξ) = r • mulHom N n i U a ξ := by
  refine sections_ext N U ?_ ?_
  · simp only [coordFst_mulHom, coordFst_smul, N.smul_smul_left]
  · simp only [coordSnd_mulHom, coordFst_smul, coordSnd_smul, N.smul_smul_left, castHom_smul,
      smul_add]
    rw [smul_comm]

/-- The action on the cofree module is linear over the sheaf of rings in the algebra variable. -/
theorem mulHom_smul_algebra (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (a : (A.complex.X i).val.obj U) (ξ : (piece N n).val.obj U) :
    mulHom N n i U (r • a) ξ = r • mulHom N n i U a ξ := by
  refine sections_ext N U ?_ ?_
  · simp only [coordFst_mulHom, coordFst_smul, N.smul_smul_right]
  · simp only [coordSnd_mulHom,  homSections_smul, N.smul_smul_right, castHom_smul,
      smul_add]
    rw [smul_comm]

/-- The action on the cofree module commutes with restriction. -/
theorem mulHom_naturality (n i : ℤ) {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : (A.complex.X i).val.obj U) (ξ : (piece N n).val.obj U) :
    (piece N (n + i)).val.map g (mulHom N n i U a ξ)
      = mulHom N n i V ((A.complex.X i).val.map g a) ((piece N n).val.map g ξ) := by
  have e1 := coordFst_mulHom N n i V ((A.complex.X i).val.map g a) ((piece N n).val.map g ξ)
  have e2 := coordSnd_mulHom N n i V ((A.complex.X i).val.map g a) ((piece N n).val.map g ξ)
  refine sections_ext N V ?_ ?_
  · rw [e1, coordFst_map, coordFst_mulHom, coordFst_map, N.smul_naturality]
    simp only [DifferentialGradedAlgebra.toGradedAlgebra_piece]
  · rw [e2, coordSnd_map, coordSnd_mulHom, map_add, map_zsmul_sections, castHom_naturality,
      castHom_naturality, N.smul_naturality, N.smul_naturality, coordFst_map, coordSnd_map,
      homSections_naturality]
    simp only [DifferentialGradedAlgebra.toGradedAlgebra_piece]
    rw [homSections_naturality (A.complex.d i (i + 1)) g a]
    rfl

/-- The differential of the cofree module satisfies the signed module Leibniz rule. -/
theorem mulHom_leibniz (n i : ℤ) (U : Cᵒᵖ) (ξ : (piece N n).val.obj U)
    (a : (A.complex.X i).val.obj U) :
    homSections (d N (n + i)) U (mulHom N n i U a ξ)
      = castHom (piece N) (add_right_comm n 1 i) U
          (mulHom N (n + 1) i U a (homSections (d N n) U ξ))
        + (Int.negOnePow n : ℤ) • castHom (piece N) (add_assoc n i 1).symm U
            (mulHom N n (i + 1) U (algD i U a) ξ) := by
  refine sections_ext N U ?_ ?_
  · simp only [map_add, AddMonoidHom.map_zsmul, coordFst_castHom, coordFst_d, coordFst_mulHom,
      coordSnd_mulHom]
  · simp only [map_add, AddMonoidHom.map_zsmul, coordSnd_castHom, coordFst_d, coordSnd_d,
      coordSnd_mulHom, algD_algD]
    simp only [map_zero, AddMonoidHom.zero_apply,  smul_zero, add_zero, zero_add,
      castHom_castHom]
    rw [Int.negOnePow_succ, Units.val_neg, neg_smul]
    exact (neg_add_cancel _).symm

/-- The first coordinate of `biprod.lift α β` on sections is `α`. -/
theorem coordFst_lift {Z : SheafOfModules.{m} R} (k : ℤ) (α : Z ⟶ N.piece k)
    (β : Z ⟶ N.piece (k + 1)) (U : Cᵒᵖ) (z : Z.val.obj U) :
    coordFst N k U (homSections (biprod.lift α β) U z) = homSections α U z := by
  rw [← homSections_comp]; exact homSections_congr (biprod.lift_fst α β) U z

/-- The second coordinate of `biprod.lift α β` on sections is `β`. -/
theorem coordSnd_lift {Z : SheafOfModules.{m} R} (k : ℤ) (α : Z ⟶ N.piece k)
    (β : Z ⟶ N.piece (k + 1)) (U : Cᵒᵖ) (z : Z.val.obj U) :
    coordSnd N k U (homSections (biprod.lift α β) U z) = homSections β U z := by
  rw [← homSections_comp]; exact homSections_congr (biprod.lift_snd α β) U z

/-- The cofree differential graded module on a graded module: degreewise `Nⁿ ⊕ Nⁿ⁺¹`, with
differential `(x, y) ↦ (y, 0)` and action `(x, y) * a = (x a, y a + (-1)ⁿ x (d a))`. -/
noncomputable def cofree : DifferentialGradedModule.{t, a, m} A where
  complex := complex N
  mul n i :=
    { app := fun U =>
        AddMonoidHom.mk'
          (fun ξ => AddMonoidHom.mk' (fun x => mulHom N n i U x ξ)
            (fun x y => mulHom_add_algebra N n i U x y ξ))
          (fun ξ η => AddMonoidHom.ext fun x => map_add (mulHom N n i U x) ξ η)
      map_smul_left := fun U r ξ x => mulHom_smul_module N n i U r x ξ
      map_smul_right := fun U r ξ x => mulHom_smul_algebra N n i U r x ξ
      naturality := fun {_ _} f ξ x => mulHom_naturality N n i f x ξ }
  mul_assoc n i j U x y z := mulHom_assoc N n i j U x y z
  mul_one n U x := mulHom_one N n U x
  leibniz n i U x y := by
    rw [show (complex N).d (n + i) (n + i + 1) = d N (n + i) from
        CochainComplex.of_d _ _ (n + i),
      show (complex N).d n (n + 1) = d N n from CochainComplex.of_d _ _ n,
      ← castHom_apply, ← castHom_apply]
    exact mulHom_leibniz N n i U x y

variable {M : DifferentialGradedModule.{t, a, m} A}

/-- The degree-`n` component of the differential graded morphism `M ⟶ cofree N` attached to a
graded morphism out of `M` with its differential forgotten. -/
noncomputable def liftHom (φ : (forgetToGradedModule A).obj M ⟶ N) (n : ℤ) :
    M.complex.X n ⟶ piece N n :=
  biprod.lift (φ.app n) (M.complex.d n (n + 1) ≫ φ.app (n + 1))

/-- The underlying complex morphism of the lift. -/
noncomputable def liftComplexHom (φ : (forgetToGradedModule A).obj M ⟶ N) :
    M.complex ⟶ (cofree N).complex where
  f := liftHom N φ
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [show (cofree N).complex.d i (i + 1) = d N i from CochainComplex.of_d _ _ i]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext z
    change homSections (liftHom N φ i ≫ d N i) U z
      = homSections (M.complex.d i (i + 1) ≫ liftHom N φ (i + 1)) U z
    rw [homSections_comp, homSections_comp]
    have a1 := coordSnd_lift N i (φ.app i) (M.complex.d i (i + 1) ≫ φ.app (i + 1)) U z
    have b1 := coordFst_lift N (i + 1) (φ.app (i + 1))
      (M.complex.d (i + 1) (i + 1 + 1) ≫ φ.app (i + 1 + 1)) U
      (homSections (M.complex.d i (i + 1)) U z)
    have b2 := coordSnd_lift N (i + 1) (φ.app (i + 1))
      (M.complex.d (i + 1) (i + 1 + 1) ≫ φ.app (i + 1 + 1)) U
      (homSections (M.complex.d i (i + 1)) U z)
    have hz : homSections (M.complex.d (i + 1) (i + 1 + 1)) U
        (homSections (M.complex.d i (i + 1)) U z) = 0 :=
      (homSections_comp _ _ U z).symm.trans
        ((homSections_congr (M.complex.d_comp_d i (i + 1) (i + 1 + 1)) U z).trans
          (homSections_zero U z))
    refine sections_ext N U ?_ ?_
    · calc coordFst N (i + 1) U (homSections (d N i) U (homSections (liftHom N φ i) U z))
          = coordSnd N i U (homSections (liftHom N φ i) U z) := coordFst_d N i U _
        _ = homSections (M.complex.d i (i + 1) ≫ φ.app (i + 1)) U z := a1
        _ = homSections (φ.app (i + 1)) U (homSections (M.complex.d i (i + 1)) U z) :=
              homSections_comp _ _ U z
        _ = coordFst N (i + 1) U
              (homSections (liftHom N φ (i + 1)) U
                (homSections (M.complex.d i (i + 1)) U z)) := b1.symm
    · calc coordSnd N (i + 1) U (homSections (d N i) U (homSections (liftHom N φ i) U z))
          = 0 := coordSnd_d N i U _
        _ = homSections (φ.app (i + 1 + 1)) U 0 := (map_zero _).symm
        _ = homSections (φ.app (i + 1 + 1)) U
              (homSections (M.complex.d (i + 1) (i + 1 + 1)) U
                (homSections (M.complex.d i (i + 1)) U z)) :=
              congrArg (homSections (φ.app (i + 1 + 1)) U) hz.symm
        _ = homSections (M.complex.d (i + 1) (i + 1 + 1) ≫ φ.app (i + 1 + 1)) U
              (homSections (M.complex.d i (i + 1)) U z) := (homSections_comp _ _ U _).symm
        _ = coordSnd N (i + 1) U
              (homSections (liftHom N φ (i + 1)) U
                (homSections (M.complex.d i (i + 1)) U z)) := b2.symm

/-- A graded morphism commutes with transport along an equality of degrees. -/
theorem hom_castHom (φ : (forgetToGradedModule A).obj M ⟶ N) {k k' : ℤ} (h : k = k')
    (U : Cᵒᵖ) (w : (M.complex.X k).val.obj U) :
    homSections (φ.app k') U (castHom M.complex.X h U w)
      = castHom N.piece h U (homSections (φ.app k) U w) := by
  subst h; rfl

/-- The morphism of differential graded modules attached to a graded morphism. -/
noncomputable def liftDgHom (φ : (forgetToGradedModule A).obj M ⟶ N) : M ⟶ cofree N where
  toHomologicalComplex := liftComplexHom N φ
  map_mul n i U x y := by
    have hx1 := coordFst_lift N n (φ.app n) (M.complex.d n (n + 1) ≫ φ.app (n + 1)) U x
    have hx2 := coordSnd_lift N n (φ.app n) (M.complex.d n (n + 1) ≫ φ.app (n + 1)) U x
    have hL1 := coordFst_lift N (n + i) (φ.app (n + i))
      (M.complex.d (n + i) (n + i + 1) ≫ φ.app (n + i + 1)) U ((M.mul n i).app U x y)
    have hL2 := coordSnd_lift N (n + i) (φ.app (n + i))
      (M.complex.d (n + i) (n + i + 1) ≫ φ.app (n + i + 1)) U ((M.mul n i).app U x y)
    have hleib : homSections (M.complex.d (n + i) (n + i + 1)) U ((M.mul n i).app U x y)
        = castHom M.complex.X (add_right_comm n 1 i) U
            ((M.mul (n + 1) i).app U (homSections (M.complex.d n (n + 1)) U x) y)
          + (Int.negOnePow n : ℤ) • castHom M.complex.X (add_assoc n i 1).symm U
              ((M.mul n (i + 1)).app U x (homSections (A.complex.d i (i + 1)) U y)) := by
      rw [castHom_apply, castHom_apply]; exact M.leibniz n i U x y
    refine sections_ext N U ?_ ?_
    · calc coordFst N (n + i) U (homSections (liftHom N φ (n + i)) U ((M.mul n i).app U x y))
          = homSections (φ.app (n + i)) U ((M.mul n i).app U x y) := hL1
        _ = N.smul n i U (homSections (φ.app n) U x) y := φ.map_smul n i U x y
        _ = N.smul n i U (coordFst N n U (homSections (liftHom N φ n) U x)) y :=
              congrArg (fun t => N.smul n i U t y) hx1.symm
        _ = coordFst N (n + i) U (mulHom N n i U y (homSections (liftHom N φ n) U x)) :=
              (coordFst_mulHom N n i U y _).symm
    · calc coordSnd N (n + i) U (homSections (liftHom N φ (n + i)) U ((M.mul n i).app U x y))
          = homSections (M.complex.d (n + i) (n + i + 1) ≫ φ.app (n + i + 1)) U
              ((M.mul n i).app U x y) := hL2
        _ = homSections (φ.app (n + i + 1)) U
              (homSections (M.complex.d (n + i) (n + i + 1)) U ((M.mul n i).app U x y)) :=
              homSections_comp _ _ U _
        _ = castHom N.piece (add_right_comm n 1 i) U
                (N.smul (n + 1) i U (homSections (φ.app (n + 1)) U
                  (homSections (M.complex.d n (n + 1)) U x)) y)
              + (Int.negOnePow n : ℤ) • castHom N.piece (add_assoc n i 1).symm U
                  (N.smul n (i + 1) U (homSections (φ.app n) U x)
                    (homSections (A.complex.d i (i + 1)) U y)) :=
              (congrArg (homSections (φ.app (n + i + 1)) U) hleib).trans
                (((homSections (φ.app (n + i + 1)) U).map_add _ _).trans
                  (congrArg₂ (· + ·)
                    ((hom_castHom N φ (add_right_comm n 1 i) U _).trans
                      (congrArg (castHom N.piece (add_right_comm n 1 i) U)
                        (φ.map_smul (n + 1) i U _ y)))
                    (((homSections (φ.app (n + i + 1)) U).map_zsmul _ _).trans
                      (congrArg (fun t => (Int.negOnePow n : ℤ) • t)
                        ((hom_castHom N φ (add_assoc n i 1).symm U _).trans
                          (congrArg (castHom N.piece (add_assoc n i 1).symm U)
                            (φ.map_smul n (i + 1) U x _)))))))
        _ = coordSnd N (n + i) U (mulHom N n i U y (homSections (liftHom N φ n) U x)) :=
              (congrArg₂ (· + ·)
                (congrArg
                  (fun t => castHom N.piece (add_right_comm n 1 i) U (N.smul (n + 1) i U t y))
                  (hx2.trans (homSections_comp _ _ U x)).symm)
                (congrArg
                  (fun t => (Int.negOnePow n : ℤ) • castHom N.piece (add_assoc n i 1).symm U
                    (N.smul n (i + 1) U t (homSections (A.complex.d i (i + 1)) U y)))
                  hx1.symm)).trans
                (coordSnd_mulHom N n i U y _).symm

/-- The graded morphism attached to a morphism of differential graded modules, by taking the
first coordinate. -/
noncomputable def lowerHom (ψ : M ⟶ cofree N) : (forgetToGradedModule A).obj M ⟶ N where
  app n := ψ.toHomologicalComplex.f n ≫ biprod.fst
  map_smul n i U x y :=
    (homSections_comp _ _ U _).trans
      ((congrArg (coordFst N (n + i) U) (ψ.map_mul n i U x y)).trans
        ((coordFst_mulHom N n i U y _).trans
          (congrArg (fun t => N.smul n i U t y) (homSections_comp _ _ U x).symm)))

/-- Taking the first coordinate is inverse to the lift. -/
theorem lowerHom_liftDgHom (φ : (forgetToGradedModule A).obj M ⟶ N) :
    lowerHom N (liftDgHom N φ) = φ :=
  GradedModule.Hom.ext fun _ => biprod.lift_fst _ _

/-- The lift is inverse to taking the first coordinate. -/
theorem liftDgHom_lowerHom (ψ : M ⟶ cofree N) : liftDgHom N (lowerHom N ψ) = ψ := by
  refine DifferentialGradedModule.Hom.ext fun n => ?_
  refine homSections_ext fun U z => ?_
  show homSections (liftHom N (lowerHom N ψ) n) U z = homSections (ψ.toHomologicalComplex.f n) U z
  have hcomm : homSections (d N n) U (homSections (ψ.toHomologicalComplex.f n) U z)
      = homSections (ψ.toHomologicalComplex.f (n + 1)) U
          (homSections (M.complex.d n (n + 1)) U z) := by
    have h := ψ.toHomologicalComplex.comm n (n + 1)
    rw [show (cofree N).complex.d n (n + 1) = d N n from CochainComplex.of_d _ _ n] at h
    exact homSections_comp_congr h U z
  refine sections_ext N U ?_ ?_
  · exact (coordFst_lift N n _ _ U z).trans (homSections_comp _ _ U z)
  · exact (coordSnd_lift N n _ _ U z).trans
      ((homSections_comp _ _ U z).trans
        ((homSections_comp _ _ U _).trans
          ((congrArg (coordFst N (n + 1) U) hcomm).symm.trans (coordFst_d N n U _))))

/-- The hom-bijection exhibiting the cofree module as right adjoint to forgetting the
differential. -/
noncomputable def homEquiv (M : DifferentialGradedModule.{t, a, m} A)
    (N : GradedModule.{t, a, m} A.toGradedAlgebra) :
    ((forgetToGradedModule A).obj M ⟶ N) ≃ (M ⟶ cofree N) where
  toFun := liftDgHom N
  invFun := lowerHom N
  left_inv := lowerHom_liftDgHom N
  right_inv := liftDgHom_lowerHom N

end Cofree

namespace Cofree

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The hom-bijection is natural in the differential graded module. -/
theorem homEquiv_naturality (M' M : DifferentialGradedModule.{t, a, m} A)
    (N : GradedModule.{t, a, m} A.toGradedAlgebra) (f : M' ⟶ M)
    (g : (forgetToGradedModule A).obj M ⟶ N) :
    homEquiv M' N ((forgetToGradedModule A).map f ≫ g) = f ≫ homEquiv M N g := by
  refine DifferentialGradedModule.Hom.ext fun n => ?_
  refine homSections_ext fun U z => ?_
  show homSections (liftHom N ((forgetToGradedModule A).map f ≫ g) n) U z
    = homSections (f.toHomologicalComplex.f n ≫ liftHom N g n) U z
  have hcomm : homSections (M.complex.d n (n + 1)) U
        (homSections (f.toHomologicalComplex.f n) U z)
      = homSections (f.toHomologicalComplex.f (n + 1)) U
          (homSections (M'.complex.d n (n + 1)) U z) :=
    homSections_comp_congr (f.toHomologicalComplex.comm n (n + 1)) U z
  refine sections_ext N U ?_ ?_
  · calc coordFst N n U (homSections (liftHom N ((forgetToGradedModule A).map f ≫ g) n) U z)
        = homSections (((forgetToGradedModule A).map f ≫ g).app n) U z := coordFst_lift N n _ _ U z
      _ = homSections (g.app n) U (homSections (f.toHomologicalComplex.f n) U z) :=
            homSections_comp _ _ U z
      _ = coordFst N n U (homSections (liftHom N g n) U
            (homSections (f.toHomologicalComplex.f n) U z)) :=
            (coordFst_lift N n _ _ U _).symm
      _ = coordFst N n U (homSections (f.toHomologicalComplex.f n ≫ liftHom N g n) U z) :=
            congrArg (coordFst N n U) (homSections_comp _ _ U z).symm
  · calc coordSnd N n U (homSections (liftHom N ((forgetToGradedModule A).map f ≫ g) n) U z)
        = homSections (M'.complex.d n (n + 1) ≫
            ((forgetToGradedModule A).map f ≫ g).app (n + 1)) U z := coordSnd_lift N n _ _ U z
      _ = homSections (((forgetToGradedModule A).map f ≫ g).app (n + 1)) U
            (homSections (M'.complex.d n (n + 1)) U z) := homSections_comp _ _ U z
      _ = homSections (g.app (n + 1)) U (homSections (f.toHomologicalComplex.f (n + 1)) U
            (homSections (M'.complex.d n (n + 1)) U z)) := homSections_comp _ _ U _
      _ = homSections (g.app (n + 1)) U (homSections (M.complex.d n (n + 1)) U
            (homSections (f.toHomologicalComplex.f n) U z)) :=
            congrArg (homSections (g.app (n + 1)) U) hcomm.symm
      _ = homSections (M.complex.d n (n + 1) ≫ g.app (n + 1)) U
            (homSections (f.toHomologicalComplex.f n) U z) := (homSections_comp _ _ U _).symm
      _ = coordSnd N n U (homSections (liftHom N g n) U
            (homSections (f.toHomologicalComplex.f n) U z)) :=
            (coordSnd_lift N n _ _ U _).symm
      _ = coordSnd N n U (homSections (f.toHomologicalComplex.f n ≫ liftHom N g n) U z) :=
            congrArg (coordSnd N n U) (homSections_comp _ _ U z).symm

end Cofree

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The cofree construction is right adjoint to forgetting the differential of a right
differential graded module. -/
noncomputable def forgetAdjunction (A : DifferentialGradedAlgebra.{t, a} R) :
    forgetToGradedModule.{t, a, m} A ⊣
      Adjunction.rightAdjointOfEquiv
        (F := forgetToGradedModule.{t, a, m} A) (G_obj := Cofree.cofree)
        Cofree.homEquiv Cofree.homEquiv_naturality :=
  Adjunction.adjunctionOfEquivRight Cofree.homEquiv Cofree.homEquiv_naturality

/-- Forgetting the differential commutes with colimits of every size. -/
instance forgetToGradedModule_preservesColimitsOfSize
    (A : DifferentialGradedAlgebra.{t, a} R) :
    PreservesColimitsOfSize.{s₁, s₂} (forgetToGradedModule.{t, a, m} A) :=
  (forgetAdjunction A).leftAdjoint_preservesColimits

/-- For a sheaf of differential graded algebras, the functor from right differential graded
modules to right graded modules that forgets the differential commutes with all colimits. -/
instance forgetToGradedModule_preservesColimits
    (A : DifferentialGradedAlgebra.{t, a} R) :
    PreservesColimits (forgetToGradedModule.{t, a, m} A) :=
  forgetToGradedModule_preservesColimitsOfSize A

end SheafOfModules
