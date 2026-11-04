module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Left differential graded modules over a sheaf of differential graded algebras

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A left differential graded `A`-module is a cochain complex of sheaves of
`R`-modules together with a unital, associative left action of the homogeneous local sections
of `A` obeying the signed Leibniz rule, the sign being determined by the degree of the algebra
section. Morphisms are action-compatible morphisms of the underlying complexes.

## Main definitions

* `SheafOfModules.LeftDifferentialGradedModule` is a left differential graded module over a
  sheaf of differential graded algebras.
* `SheafOfModules.LeftDifferentialGradedModule.Hom` is a morphism of such modules, and
  `SheafOfModules.LeftDifferentialGradedModule.instCategory` the category they form.

## Implementation notes

The right-handed half of Tag 0FRI — `SheafOfModules.DifferentialGradedModule`, its `Hom` and
the category they form — is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean` and is not restated
here. This file adds the left-handed half, which the source defines "in the same way, with the
algebra acting on the left".

The action is a `SheafOfModules.BilinearMap`, i.e. it is presented on local sections as a
biadditive map linear over the sheaf of rings in each variable and compatible with
restriction; this is forced by the target `complex.X (n + m)` varying with the degrees, and the
algebra and module pieces are allowed to live in independent universes. Associativity and the
unit law are stated with `HEq`, and the Leibniz rule uses `SheafOfModules.gradedCast`, because
the degrees indexing their two sides are propositionally but not definitionally equal.

The square-zero differential is supplied by the underlying `CochainComplex`, and morphisms
carry the complex morphism directly, so the category and its limits and colimits can be stated
without conversion.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module
pieces are independent, matching `GradedForgetColimits`; a ringed site `X` is the case
`R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A left differential graded module over a sheaf of differential graded algebras. The sign in
the Leibniz rule is determined by the degree of the algebra section. -/
@[stacks 0FRI "left differential graded modules"]
structure LeftDifferentialGradedModule (A : DifferentialGradedAlgebra.{t, a} R) where
  /-- The underlying cochain complex of sheaves of modules. -/
  complex : CochainComplex (SheafOfModules.{m} R) ℤ
  /-- The left action of homogeneous sections of the algebra. -/
  mul : ∀ n m : ℤ, BilinearMap (A.complex.X n) (complex.X m) (complex.X (n + m))
  /-- The left action is associative with multiplication in the algebra. -/
  mul_assoc : ∀ (n m k : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (b : (A.complex.X m).val.obj U) (x : (complex.X k).val.obj U),
    HEq ((mul (n + m) k).app U ((A.mul n m).app U a b) x)
      ((mul n (m + k)).app U a ((mul m k).app U b x))
  /-- The unit of the algebra acts as the identity. -/
  one_mul : ∀ (n : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U),
    HEq ((mul 0 n).app U (A.one.eval U) x) x
  /-- The differential satisfies the signed left-module Leibniz rule. -/
  leibniz : ∀ (n m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (x : (complex.X m).val.obj U),
    (complex.d (n + m) (n + m + 1)).val.app U ((mul n m).app U a x) =
      gradedCast (fun q ↦ (complex.X q).val.obj U) (add_right_comm n 1 m)
          ((mul (n + 1) m).app U ((A.complex.d n (n + 1)).val.app U a) x) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (complex.X q).val.obj U) (add_assoc n m 1).symm
            ((mul n (m + 1)).app U a ((complex.d m (m + 1)).val.app U x))

namespace LeftDifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- A morphism of left differential graded modules. -/
@[stacks 0FRI "homomorphisms of left differential graded modules"]
structure Hom (M N : LeftDifferentialGradedModule.{t, a, m} A) where
  /-- The underlying morphism of cochain complexes. -/
  toHomologicalComplex : M.complex ⟶ N.complex
  /-- The complex morphism commutes with the left action. -/
  map_mul : ∀ (n m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (x : (M.complex.X m).val.obj U),
    (toHomologicalComplex.f (n + m)).val.app U ((M.mul n m).app U a x) =
      (N.mul n m).app U a ((toHomologicalComplex.f m).val.app U x)

/-- Morphisms of left differential graded modules are determined degreewise. -/
@[ext]
theorem Hom.ext {M N : LeftDifferentialGradedModule.{t, a, m} A} {f g : Hom M N}
    (h : ∀ n, f.toHomologicalComplex.f n = g.toHomologicalComplex.f n) : f = g := by
  cases f
  cases g
  congr 1
  exact HomologicalComplex.hom_ext _ _ h

/-- The identity morphism of a left differential graded module. -/
def Hom.id (M : LeftDifferentialGradedModule.{t, a, m} A) : Hom M M where
  toHomologicalComplex := 𝟙 M.complex
  map_mul _ _ _ _ _ := rfl

/-- Composition of morphisms of left differential graded modules. -/
def Hom.comp {M N P : LeftDifferentialGradedModule.{t, a, m} A} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  toHomologicalComplex := f.toHomologicalComplex ≫ g.toHomologicalComplex
  map_mul n m U a x := by
    change (g.toHomologicalComplex.f (n + m)).val.app U
      ((f.toHomologicalComplex.f (n + m)).val.app U ((M.mul n m).app U a x)) = _
    rw [f.map_mul, g.map_mul]
    rfl

/-- In each degree, the identity morphism is the identity. -/
@[simp]
theorem Hom.id_f (M : LeftDifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (Hom.id M).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- In each degree, a composite morphism is the composite of the components. -/
@[simp]
theorem Hom.comp_f {M N P : LeftDifferentialGradedModule.{t, a, m} A} (f : Hom M N)
    (g : Hom N P) (n : ℤ) : (f.comp g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

/-- Left differential graded modules over a fixed sheaf of differential graded algebras form a
category. -/
instance instCategory : Category (LeftDifferentialGradedModule.{t, a, m} A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp

/-- In each degree, the categorical identity morphism is the identity. -/
@[simp]
theorem id_f (M : LeftDifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (𝟙 M : M ⟶ M).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- In each degree, a categorical composite is the composite of the components. -/
@[simp]
theorem comp_f {M N P : LeftDifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) (g : N ⟶ P)
    (n : ℤ) : (f ≫ g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

end LeftDifferentialGradedModule

end SheafOfModules
