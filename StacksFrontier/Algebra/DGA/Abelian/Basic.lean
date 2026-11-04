module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.Algebra.DirectSum.GradedSubmodule
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Differential graded algebras and modules

Fix a commutative ring `R`. A differential graded algebra `(A, d)` over `R` is a `ℤ`-graded
associative unital `R`-algebra `A = ⊕_n A^n` with an `R`-linear differential `d` of degree `+1`
such that `d ∘ d = 0` and `d (a b) = d(a) b + (-1)^n a d(b)` for `a ∈ A^n`. A right differential
graded module over `(A, d)` is a right `A`-module `M = ⊕_n M^n` with `M^n A^m ⊆ M^{n+m}` and an
`R`-linear differential `d` of degree `+1` such that `d ∘ d = 0` and
`d (m a) = d(m) a + (-1)^n m d(a)` for `m ∈ M^n`. Its homomorphisms are the right `A`-module
maps compatible with the gradings and the differentials. This file defines these objects, the
category `Mod_(A, d)` of right differential graded `A`-modules, and its preadditive structure.

A right `A`-module is a module over `A.Aᵐᵒᵖ`, the right action of `a` being `MulOpposite.op a •`,
and the sign `(-1)^n` for `n : ℤ` is `Int.negOnePow n`.

## Main definitions

* `DifferentialGradedAlgebra`: a differential graded algebra over `R`.
* `DifferentialGradedModule`: a right differential graded module over a differential graded
  algebra.
* `DifferentialGradedModule.Hom`: a homomorphism of right differential graded modules, a
  morphism of the category `Mod_(A, d)`.

## References

* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V)
* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
-/

open CategoryTheory CategoryTheory.Limits

universe u v w w' w'' t

variable (R : Type u) [CommRing R]

/-- A differential graded algebra over a commutative ring `R`: an `R`-algebra `A` with a
`ℤ`-grading `A = ⊕_n A^n` making it a graded algebra, and an `R`-linear differential `d` of degree
`+1` with `d ∘ d = 0` satisfying the Leibniz rule on homogeneous elements. -/
@[sga "6 VII 2.1"]
structure DifferentialGradedAlgebra where
  /-- The underlying type of the algebra, independent of the base-ring universe. -/
  A : Type v
  [ring : Ring A]
  [isAlg : Algebra R A]
  /-- The `ℤ`-grading `A = ⊕_n A^n` by `R`-submodules. -/
  grading : ℤ → Submodule R A
  /-- The grading makes `A` a graded algebra: `A = ⊕_n A^n`, `A^n · A^m ⊆ A^{n+m}` and
  `1 ∈ A^0`. -/
  [gradedAlg : GradedAlgebra grading]
  /-- The differential, an `R`-linear endomorphism. -/
  d : A →ₗ[R] A
  /-- Square-zero: `d ∘ d = 0`. -/
  d_comp_d : d ∘ₗ d = 0
  /-- The differential has degree `+1`. -/
  d_mem : ∀ (n : ℤ) (a : A), a ∈ grading n → d a ∈ grading (n + 1)
  /-- Leibniz rule: for `a ∈ A^n` and `b ∈ A^m`,
  `d (a * b) = d a * b + (-1)^n • (a * d b)`. -/
  leibniz : ∀ (n m : ℤ) (a b : A), a ∈ grading n → b ∈ grading m →
    d (a * b) = d a * b + (n.negOnePow : ℤ) • (a * d b)

attribute [instance] DifferentialGradedAlgebra.ring DifferentialGradedAlgebra.isAlg
  DifferentialGradedAlgebra.gradedAlg

variable {R}

/-- A right differential graded module over a differential graded algebra `(A, d)`: an `R`-module
`M` with an `R`-bilinear right `A`-action, a `ℤ`-grading `M = ⊕_n M^n` by `R`-submodules with
`M^n A^m ⊆ M^{n+m}`, and an `R`-linear differential `d` of degree `+1` with `d ∘ d = 0` satisfying
the Leibniz rule on homogeneous elements. -/
structure DifferentialGradedModule (A : DifferentialGradedAlgebra.{u, v} R) where
  /-- The underlying type of the module, independent of the base ring and algebra. -/
  M : Type w
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  /-- The right `A`-action, as a module over `A.Aᵐᵒᵖ`: the right action of `a : A.A` on `x : M` is
  `MulOpposite.op a • x`. -/
  [rmodule : Module (MulOpposite A.A) M]
  /-- The `R`-module structure is compatible with the right `A`-action: `r • x` is the right action
  of `algebraMap R A r` on `x`. -/
  [isScalarTower : IsScalarTower R (MulOpposite A.A) M]
  /-- The `ℤ`-grading `M = ⊕_n M^n` by `R`-submodules. -/
  grading : ℤ → Submodule R M
  /-- The grading is a direct sum decomposition `M = ⊕_n M^n`. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- Graded module: `M^n · A^m ⊆ M^{n+m}`. -/
  smul_mem : ∀ (n m : ℤ) (x : M) (a : A.A), x ∈ grading n → a ∈ A.grading m →
    (MulOpposite.op a) • x ∈ grading (n + m)
  /-- The differential, an `R`-linear endomorphism. -/
  d : M →ₗ[R] M
  /-- Square-zero: `d ∘ d = 0`. -/
  d_comp_d : d ∘ₗ d = 0
  /-- The differential has degree `+1`. -/
  d_mem : ∀ (n : ℤ) (x : M), x ∈ grading n → d x ∈ grading (n + 1)
  /-- Leibniz rule: for `x ∈ M^n` and `a ∈ A^m`,
  `d (x a) = (d x) a + (-1)^n • (x (d a))`. -/
  leibniz : ∀ (n m : ℤ) (x : M) (a : A.A), x ∈ grading n → a ∈ A.grading m →
    d ((MulOpposite.op a) • x) = (MulOpposite.op a) • (d x)
      + (n.negOnePow : ℤ) • ((MulOpposite.op (A.d a)) • x)

attribute [instance] DifferentialGradedModule.addCommGroup DifferentialGradedModule.module
  DifferentialGradedModule.rmodule DifferentialGradedModule.isScalarTower
  DifferentialGradedModule.decomposition

variable {A : DifferentialGradedAlgebra.{u, v} R}

/-- A homomorphism of right differential graded `A`-modules: an `R`-linear map respecting the right
`A`-action, the grading and the differential. -/
@[ext]
structure DifferentialGradedModule.Hom (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) where
  /-- The underlying `R`-linear map. -/
  toFun : M.M →ₗ[R] N.M
  /-- Compatibility with the right `A`-action: `f (x a) = (f x) a`. -/
  map_smul : ∀ (x : M.M) (a : A.A), toFun ((MulOpposite.op a) • x) = (MulOpposite.op a) • (toFun x)
  /-- Compatibility with the gradings: `f(M^n) ⊆ N^n`. -/
  map_grading : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → toFun x ∈ N.grading n
  /-- Compatibility with the differentials: `f ∘ d_M = d_N ∘ f`. -/
  map_d : toFun ∘ₗ M.d = N.d ∘ₗ toFun

namespace DifferentialGradedModule

/-- Membership in a graded piece `M^i` transported along an equality of degrees `i = j`. -/
theorem mem_grading_congr {M : DifferentialGradedModule.{u, v, w} A} {i j : ℤ} (hij : i = j)
    {z : M.M} (hz : z ∈ M.grading i) : z ∈ M.grading j :=
  hij ▸ hz

/-- The identity homomorphism. -/
def Hom.id (M : DifferentialGradedModule.{u, v, w} A) : Hom M M where
  toFun := LinearMap.id
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := by simp

/-- Composition of homomorphisms of differential graded modules. -/
def Hom.comp {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} {P : DifferentialGradedModule.{u, v, w''} A}
    (g : Hom N P) (f : Hom M N) : Hom M P where
  toFun := g.toFun ∘ₗ f.toFun
  map_smul := by intro x a; simp [f.map_smul, g.map_smul]
  map_grading n x hx := g.map_grading n _ (f.map_grading n x hx)
  map_d := by
    rw [LinearMap.comp_assoc, f.map_d, ← LinearMap.comp_assoc, g.map_d, LinearMap.comp_assoc]

/-- The category `Mod_(A, d)` of (right) differential graded `A`-modules. -/
instance : Category (DifferentialGradedModule.{u, v, w} A) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp g f
  id_comp := by intro M N f; ext x; simp [Hom.comp, Hom.id]
  comp_id := by intro M N f; ext x; simp [Hom.comp, Hom.id]
  assoc := by intro M N P Q f g h; ext x; simp [Hom.comp]

/-- The underlying map of a composite is the composite of the underlying maps. -/
@[simp] lemma Hom.comp_toFun_apply {M N P : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) (g : N ⟶ P) (x : M.M) : (f ≫ g).toFun x = g.toFun (f.toFun x) := rfl

end DifferentialGradedModule

namespace DifferentialGradedModule

/-- The zero homomorphism. -/
def Hom.zero (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) : Hom M N where
  toFun := 0
  map_smul := by intro x a; simp
  map_grading := by intro n x hx; simp
  map_d := by ext x; simp

/-- Addition of homomorphisms. -/
def Hom.add {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f g : Hom M N) : Hom M N where
  toFun := f.toFun + g.toFun
  map_smul := by
    intro x a
    simp only [LinearMap.add_apply, f.map_smul, g.map_smul, smul_add]
  map_grading n x hx := (N.grading n).add_mem (f.map_grading n x hx) (g.map_grading n x hx)
  map_d := by rw [LinearMap.add_comp, LinearMap.comp_add, f.map_d, g.map_d]

/-- Negation of a homomorphism. -/
def Hom.neg {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f : Hom M N) : Hom M N where
  toFun := -f.toFun
  map_smul := by
    intro x a
    simp only [LinearMap.neg_apply, f.map_smul, smul_neg]
  map_grading n x hx := (N.grading n).neg_mem (f.map_grading n x hx)
  map_d := by rw [LinearMap.neg_comp, LinearMap.comp_neg, f.map_d]

/-- The underlying map of the zero homomorphism is zero. -/
@[simp] lemma Hom.zero_toFun (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) :
    (Hom.zero M N).toFun = 0 := rfl

/-- The underlying map of a sum of homomorphisms is the sum of the underlying maps. -/
@[simp] lemma Hom.add_toFun {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f g : Hom M N) :
    (Hom.add f g).toFun = f.toFun + g.toFun := rfl

/-- The underlying map of the negation of a homomorphism is the negation of the underlying map. -/
@[simp] lemma Hom.neg_toFun {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f : Hom M N) :
    (Hom.neg f).toFun = -f.toFun := rfl

/-- The zero homomorphism. -/
instance instZero (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) : Zero (Hom M N) := ⟨Hom.zero M N⟩
/-- Addition of homomorphisms. -/
instance instAdd (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) : Add (Hom M N) := ⟨Hom.add⟩
/-- Negation of homomorphisms. -/
instance instNeg (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) : Neg (Hom M N) := ⟨Hom.neg⟩
/-- Subtraction of homomorphisms. -/
instance instSub (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) : Sub (Hom M N) :=
  ⟨fun f g ↦ Hom.add f (Hom.neg g)⟩

/-- The underlying map of `0` is zero. -/
@[simp] lemma Hom.hom_zero_toFun (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) :
    (0 : Hom M N).toFun = 0 := rfl

/-- The underlying map of `f + g` is the sum of the underlying maps. -/
@[simp] lemma Hom.hom_add_toFun {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f g : Hom M N) :
    (f + g).toFun = f.toFun + g.toFun := rfl

/-- The underlying map of `-f` is the negation of the underlying map. -/
@[simp] lemma Hom.hom_neg_toFun {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f : Hom M N) :
    (-f).toFun = -f.toFun := rfl

/-- The underlying map of `f - g` is the difference of the underlying maps. -/
@[simp] lemma Hom.hom_sub_toFun {M : DifferentialGradedModule.{u, v, w} A}
    {N : DifferentialGradedModule.{u, v, w'} A} (f g : Hom M N) :
    (f - g).toFun = f.toFun - g.toFun :=
  (sub_eq_add_neg _ _).symm

/-- The additive commutative group structure on hom-sets, transported from the
underlying linear maps via the injective `toFun`. -/
instance instAddCommGroup
    (M : DifferentialGradedModule.{u, v, w} A)
    (N : DifferentialGradedModule.{u, v, w'} A) : AddCommGroup (Hom M N) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  sub := (· - ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by intro f g h; ext x; simp [add_assoc]
  zero_add := by intro f; ext x; simp
  add_zero := by intro f; ext x; simp
  add_comm := by intro f g; ext x; simp [add_comm]
  neg_add_cancel := by intro f; ext x; simp
  sub_eq_add_neg := by intro f g; ext x; simp [sub_eq_add_neg]

/-- The category `Mod_(A, d)` is preadditive. -/
instance instPreadditive : Preadditive (DifferentialGradedModule.{u, v, w} A) where
  homGroup M N := instAddCommGroup M N
  add_comp _ _ _ _ _ h := Hom.ext (LinearMap.comp_add _ _ h.toFun)
  comp_add _ _ _ f _ _ := Hom.ext (LinearMap.add_comp f.toFun _ _)

end DifferentialGradedModule
