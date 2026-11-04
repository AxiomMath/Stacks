module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# The differential graded category of cochain complexes

For a preadditive category `B`, the cochain complexes in `B` are the objects of a differential
graded category over `ℤ`: a homogeneous morphism of degree `n` from `A` to `C` is an arbitrary
family of maps `A.X i ⟶ C.X (i + n)`, its differential is the usual graded commutator with the
differentials of the two complexes, and composition is componentwise composition. The closed
degree-`n` morphisms are, equivalently, the maps of complexes `A ⟶ C[n]`.

## Main definitions

* `CochainComplex.dgCategory`: the differential graded category of integer-indexed cochain
  complexes in a preadditive category.
* `CochainComplex.dgCategoryLinear`: the same category read over a commutative ring `R`, for
  cochain complexes in an `R`-linear preadditive category.

## Main results

* `CochainComplex.dgCategory_d_v`, `CochainComplex.dgCategory_comp_v` and
  `CochainComplex.dgCategory_id_v`: the differential, the composition and the identity,
  computed on components.
* `CochainComplex.dgCategory_hom_ext`: two homogeneous morphisms with the same components are
  equal.
* `CochainComplex.HomComplex.Cocycle.equivHomShift`: a closed homogeneous morphism of degree `n`
  from `A` to `C` is a map of complexes `A ⟶ C⟦n⟧`.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

open CochainComplex.HomComplex

variable (B : Type u) [Category.{v} B] [Preadditive B]

/-- The differential graded category of cochain complexes in a preadditive category `B`. Its
degree-`n` morphisms `A ⟶ C` are the families `A.X i ⟶ C.X (i + n)`, the differential is
`(d f) i = f i ≫ d - (-1)^n • (d ≫ f (i + 1))`, and composition and identities are the
componentwise ones. -/
@[stacks 09L9 "differential_graded_category_of_complexes",
  implicit_reducible,
  sga "2 V 1.1" "Hom^•(F,G) complex", sga "4 XVII 1.1.10" "(ii)"]
public def dgCategory : DGCategory ℤ where
  Obj := CochainComplex B ℤ
  Hom A B n := Cochain A B n
  addCommGroup A B n := inferInstance
  module A B n := inferInstance
  d {A B n} f := δ n (n + 1) f
  d_add {A B n} f g := δ_add n (n + 1) f g
  d_smul {A B n} r f := δ_smul n (n + 1) r f
  d_d {A B n} f := δ_δ n (n + 1) (n + 1 + 1) f
  comp {A B C m n k} h g f := f.comp g (by omega)
  comp_add_left {A B C m n k} h g₁ g₂ f := by
    simpa only using Cochain.comp_add f g₁ g₂ (by omega : n + m = k)
  comp_add_right {A B C m n k} h g f₁ f₂ := by
    simpa only using Cochain.add_comp f₁ f₂ g (by omega : n + m = k)
  comp_smul_left {A B C m n k} h r g f := by
    simpa only using Cochain.comp_smul f r g (by omega : n + m = k)
  comp_smul_right {A B C m n k} h r g f := by
    simpa only using Cochain.smul_comp r f g (by omega : n + m = k)
  leibniz {A B C m n k} h g f := by
    have hd := δ_comp f g (by omega : n + m = k) (n + 1) (m + 1) (k + 1)
      (by omega) (by omega) (by omega)
    rw [Units.smul_def] at hd
    change _ = _ + (m.negOnePow : ℤ) • _ at hd
    have hs : (m.negOnePow : ℤ) = (-1 : ℤ) ^ m.natAbs := Int.coe_negOnePow ℤ m
    rw [hs] at hd
    simpa only using hd
  assoc {A B C D l m n p q r} h₁ h₂ h₃ h₄ e g f := by
    simpa only using
      (Cochain.comp_assoc f g e (by omega : n + m = p) (by omega : m + l = q)
        (by omega : n + m + l = r))
  id A := Cochain.ofHom (𝟙 A)
  id_comp {A B n} f := by
    simpa only using Cochain.comp_id f
  comp_id {A B n} f := by
    simpa only using Cochain.id_comp f
  d_id A := δ_ofHom (p := (1 : ℤ)) (𝟙 A)

/-- The objects of the differential graded category are cochain complexes. -/
@[simp] public theorem dgCategory_obj : (dgCategory B).Obj = CochainComplex B ℤ := rfl

/-- Homogeneous morphisms in the differential graded category are Mathlib cochains. -/
@[simp] public theorem dgCategory_hom_eq (A C : CochainComplex B ℤ) (n : ℤ) :
    (dgCategory B).Hom A C n = Cochain A C n := rfl

/-- Two homogeneous morphisms are equal when all their components are equal. -/
@[ext] public theorem dgCategory_hom_ext {A C : CochainComplex B ℤ} {n : ℤ}
    (f g : (dgCategory B).Hom A C n)
    (h : ∀ (p q : ℤ) (hpq : p + n = q), f.v p q hpq = g.v p q hpq) : f = g :=
  Cochain.ext f g h

/-- The differential has the usual graded-commutator formula on components. -/
public theorem dgCategory_d_v {A C : CochainComplex B ℤ} {n : ℤ}
    (f : (dgCategory B).Hom A C n) (p q : ℤ) (hpq : p + (n + 1) = q) (q₁ q₂ : ℤ)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) :
    ((dgCategory B).d f).v p q hpq =
      f.v p q₁ (by omega) ≫ C.d q₁ q + (n + 1).negOnePow • A.d p q₂ ≫ f.v q₂ q (by omega) :=
  δ_v n (n + 1) rfl f p q hpq q₁ q₂ hq₁ hq₂

/-- Composition in the differential graded category is componentwise composition. -/
public theorem dgCategory_comp_v {A C D : CochainComplex B ℤ} {m n k : ℤ} (h : m + n = k)
    (g : (dgCategory B).Hom C D m) (f : (dgCategory B).Hom A C n) (p₁ p₂ p₃ : ℤ)
    (h₁ : p₁ + n = p₂) (h₂ : p₂ + m = p₃) :
    ((dgCategory B).comp h g f).v p₁ p₃ (by omega) = f.v p₁ p₂ h₁ ≫ g.v p₂ p₃ h₂ :=
  Cochain.comp_v f g (by omega) p₁ p₂ p₃ h₁ h₂

/-- The identity in the differential graded category is componentwise the identity. -/
@[simp] public theorem dgCategory_id_v (A : CochainComplex B ℤ) (p : ℤ) :
    ((dgCategory B).id A).v p p (add_zero p) = 𝟙 (A.X p) := Cochain.ofHom_v (𝟙 A) p

section Linear

variable (R : Type*) [CommRing R] [Linear R B]

/-- The differential graded category over `R` of cochain complexes in an `R`-linear preadditive
category `B`. The objects, the homogeneous morphisms, the differential, the composition and the
identities are those of `CochainComplex.dgCategory B`, and the homogeneous morphisms carry their
`R`-module structure. -/
@[implicit_reducible, sga "4 XVII 1.1.10"]
public def dgCategoryLinear : DGCategory R where
  Obj := CochainComplex B ℤ
  Hom A B n := Cochain A B n
  addCommGroup A B n := inferInstance
  module A B n := inferInstance
  d {A B n} f := δ n (n + 1) f
  d_add {A B n} f g := δ_add n (n + 1) f g
  d_smul {A B n} r f := δ_smul n (n + 1) r f
  d_d {A B n} f := δ_δ n (n + 1) (n + 1 + 1) f
  comp {A B C m n k} h g f := f.comp g (by omega)
  comp_add_left {A B C m n k} h g₁ g₂ f := by
    simpa only using Cochain.comp_add f g₁ g₂ (by omega : n + m = k)
  comp_add_right {A B C m n k} h g f₁ f₂ := by
    simpa only using Cochain.add_comp f₁ f₂ g (by omega : n + m = k)
  comp_smul_left {A B C m n k} h r g f := by
    simpa only using Cochain.comp_smul f r g (by omega : n + m = k)
  comp_smul_right {A B C m n k} h r g f := by
    simpa only using Cochain.smul_comp r f g (by omega : n + m = k)
  leibniz {A B C m n k} h g f := by
    have hd := δ_comp f g (by omega : n + m = k) (n + 1) (m + 1) (k + 1)
      (by omega) (by omega) (by omega)
    rw [Units.smul_def] at hd
    change _ = _ + (m.negOnePow : ℤ) • _ at hd
    have hs : (m.negOnePow : ℤ) = (-1 : ℤ) ^ m.natAbs := Int.coe_negOnePow ℤ m
    rw [hs] at hd
    have hz : ∀ z : Cochain A C (k + 1),
        ((-1 : ℤ) ^ m.natAbs) • z = ((-1 : R) ^ m.natAbs) • z := by
      intro z
      rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ m.natAbs) z]
      push_cast
      rfl
    rw [hz] at hd
    simpa only using hd
  assoc {A B C D l m n p q r} h₁ h₂ h₃ h₄ e g f := by
    simpa only using
      (Cochain.comp_assoc f g e (by omega : n + m = p) (by omega : m + l = q)
        (by omega : n + m + l = r))
  id A := Cochain.ofHom (𝟙 A)
  id_comp {A B n} f := by
    simpa only using Cochain.comp_id f
  comp_id {A B n} f := by
    simpa only using Cochain.id_comp f
  d_id A := δ_ofHom (p := (1 : ℤ)) (𝟙 A)

/-- The objects of the `R`-linear differential graded category are the objects of the
`ℤ`-linear one. -/
@[simp] public theorem dgCategoryLinear_obj :
    (dgCategoryLinear B R).Obj = (dgCategory B).Obj := rfl

/-- The homogeneous morphisms of the `R`-linear differential graded category are those of the
`ℤ`-linear one. -/
@[simp] public theorem dgCategoryLinear_hom_eq (A C : CochainComplex B ℤ) (n : ℤ) :
    (dgCategoryLinear B R).Hom A C n = (dgCategory B).Hom A C n := rfl

/-- The differential of the `R`-linear differential graded category is that of the `ℤ`-linear
one. -/
public theorem dgCategoryLinear_d {A C : CochainComplex B ℤ} {n : ℤ}
    (f : (dgCategoryLinear B R).Hom A C n) :
    (dgCategoryLinear B R).d f = (dgCategory B).d f := rfl

/-- Composition in the `R`-linear differential graded category is that of the `ℤ`-linear one. -/
public theorem dgCategoryLinear_comp {A C D : CochainComplex B ℤ} {m n k : ℤ} (h : m + n = k)
    (g : (dgCategoryLinear B R).Hom C D m) (f : (dgCategoryLinear B R).Hom A C n) :
    (dgCategoryLinear B R).comp h g f = (dgCategory B).comp h g f := rfl

/-- The identities of the `R`-linear differential graded category are those of the `ℤ`-linear
one. -/
public theorem dgCategoryLinear_id (A : CochainComplex B ℤ) :
    (dgCategoryLinear B R).id A = (dgCategory B).id A := rfl

/-- Two homogeneous morphisms of the `R`-linear differential graded category are equal when all
their components are equal. -/
@[ext] public theorem dgCategoryLinear_hom_ext {A C : CochainComplex B ℤ} {n : ℤ}
    (f g : (dgCategoryLinear B R).Hom A C n)
    (h : ∀ (p q : ℤ) (hpq : p + n = q), f.v p q hpq = g.v p q hpq) : f = g :=
  Cochain.ext f g h

/-- The differential of the `R`-linear differential graded category has the usual graded-commutator
formula on components. -/
public theorem dgCategoryLinear_d_v {A C : CochainComplex B ℤ} {n : ℤ}
    (f : (dgCategoryLinear B R).Hom A C n) (p q : ℤ) (hpq : p + (n + 1) = q) (q₁ q₂ : ℤ)
    (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q₂) :
    ((dgCategoryLinear B R).d f).v p q hpq =
      f.v p q₁ (by omega) ≫ C.d q₁ q + (n + 1).negOnePow • A.d p q₂ ≫ f.v q₂ q (by omega) :=
  dgCategory_d_v (B := B) f p q hpq q₁ q₂ hq₁ hq₂

/-- Composition in the `R`-linear differential graded category is componentwise composition. -/
public theorem dgCategoryLinear_comp_v {A C D : CochainComplex B ℤ} {m n k : ℤ} (h : m + n = k)
    (g : (dgCategoryLinear B R).Hom C D m) (f : (dgCategoryLinear B R).Hom A C n) (p₁ p₂ p₃ : ℤ)
    (h₁ : p₁ + n = p₂) (h₂ : p₂ + m = p₃) :
    ((dgCategoryLinear B R).comp h g f).v p₁ p₃ (by omega) = f.v p₁ p₂ h₁ ≫ g.v p₂ p₃ h₂ :=
  dgCategory_comp_v (B := B) h g f p₁ p₂ p₃ h₁ h₂

/-- The identity of the `R`-linear differential graded category is componentwise the identity. -/
@[simp] public theorem dgCategoryLinear_id_v (A : CochainComplex B ℤ) (p : ℤ) :
    ((dgCategoryLinear B R).id A).v p p (add_zero p) = 𝟙 (A.X p) :=
  dgCategory_id_v (B := B) A p

end Linear

end CochainComplex

add_to_stacks 09L9 "closed_shift" CochainComplex.HomComplex.Cocycle.equivHomShift
add_to_stacks 09L9 "closed_shift" CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply
add_to_stacks 09L9 "closed_shift" CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe
add_to_stacks 09L9 "closed_shift" CochainComplex.HomComplex.Cocycle.rightShift_coe
