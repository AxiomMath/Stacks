module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Differential graded bimodules over sheaves of differential graded algebras

Let `R` be a sheaf of rings on a site and let `A` and `B` be sheaves of differential graded
`R`-algebras. A differential graded `(A, B)`-bimodule is a cochain complex of sheaves of
`R`-modules carrying a unital left `A`-action and a unital right `B`-action which commute with
one another, both obeying the signed Leibniz rule for the differential of the complex. A
homomorphism is a morphism of the underlying complexes respecting both actions.

## Main definitions

* `SheafOfModules.DifferentialGradedBimodule` is a differential graded bimodule between two
  sheaves of differential graded algebras.
* `SheafOfModules.DifferentialGradedBimodule.Hom` is a homomorphism of differential graded
  bimodules, and `SheafOfModules.DifferentialGradedBimodule.instCategory` the category they
  form.

## Implementation notes

The two actions are `SheafOfModules.BilinearMap`s, i.e. they are presented on local sections as
biadditive maps linear over the sheaf of rings in each variable and compatible with
restriction; this is the presentation used by `SheafOfModules.GradedAlgebra` and
`SheafOfModules.DifferentialGradedModule`. The associativity, commutation and unit laws are
stated with `HEq` because the degrees indexing their two sides are propositionally but not
definitionally equal, and the two Leibniz rules use `SheafOfModules.gradedCast` for the same
reason.

The square-zero differential is supplied by the underlying `CochainComplex`, so clients can use
the action and differential laws directly without unfolding a forgetful construction.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the bimodule
pieces are independent, matching the sheaves of differential graded algebras of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedForgetColimits.lean` that this file is
built on; a ringed site `X` is the case `R := X.ringSheaf`.

The source does not assert that differential graded bimodules form a category. The identity,
composition and `Category` instance below are the evident ones and are recorded untagged.

## References

* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A differential graded bimodule between two sheaves of differential graded algebras: a
cochain complex of sheaves of modules with commuting unital left and right actions, each
obeying the signed Leibniz rule. -/
@[stacks 0FRQ "differential graded bimodules"]
structure DifferentialGradedBimodule (A B : DifferentialGradedAlgebra.{t, a} R) where
  /-- The underlying cochain complex of sheaves of modules. -/
  complex : CochainComplex (SheafOfModules.{m} R) ℤ
  /-- Right multiplication by homogeneous sections of `B`. -/
  rightMul (n m : ℤ) : BilinearMap (complex.X n) (B.complex.X m) (complex.X (n + m))
  /-- Left multiplication by homogeneous sections of `A`. -/
  leftMul (n m : ℤ) : BilinearMap (A.complex.X n) (complex.X m) (complex.X (n + m))
  /-- The left action is associative. -/
  left_assoc (i j n : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
      (a' : (A.complex.X j).val.obj U) (x : (complex.X n).val.obj U) :
    HEq ((leftMul i (j + n)).app U a ((leftMul j n).app U a' x))
      ((leftMul (i + j) n).app U ((A.mul i j).app U a a') x)
  /-- The right action is associative. -/
  right_assoc (n i j : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U)
      (b : (B.complex.X i).val.obj U) (b' : (B.complex.X j).val.obj U) :
    HEq ((rightMul (n + i) j).app U ((rightMul n i).app U x b) b')
      ((rightMul n (i + j)).app U x ((B.mul i j).app U b b'))
  /-- Left and right multiplication commute. -/
  left_right_assoc (i n j : ℤ) (U : Cᵒᵖ) (a : (A.complex.X i).val.obj U)
      (x : (complex.X n).val.obj U) (b : (B.complex.X j).val.obj U) :
    HEq ((rightMul (i + n) j).app U ((leftMul i n).app U a x) b)
      ((leftMul i (n + j)).app U a ((rightMul n j).app U x b))
  /-- The unit of `A` acts as the identity. -/
  one_left (n : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U) :
    HEq ((leftMul 0 n).app U (A.one.eval U) x) x
  /-- The unit of `B` acts as the identity. -/
  one_right (n : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U) :
    HEq ((rightMul n 0).app U x (B.one.eval U)) x
  /-- The left action obeys the signed Leibniz rule. -/
  leibniz_left (n m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (x : (complex.X m).val.obj U) :
    (complex.d (n + m) (n + m + 1)).val.app U ((leftMul n m).app U a x) =
      gradedCast (fun q ↦ (complex.X q).val.obj U) (add_right_comm n 1 m)
          ((leftMul (n + 1) m).app U ((A.complex.d n (n + 1)).val.app U a) x) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (complex.X q).val.obj U) (add_assoc n m 1).symm
            ((leftMul n (m + 1)).app U a ((complex.d m (m + 1)).val.app U x))
  /-- The right action obeys the signed Leibniz rule. -/
  leibniz_right (n m : ℤ) (U : Cᵒᵖ) (x : (complex.X n).val.obj U)
      (b : (B.complex.X m).val.obj U) :
    (complex.d (n + m) (n + m + 1)).val.app U ((rightMul n m).app U x b) =
      gradedCast (fun q ↦ (complex.X q).val.obj U) (add_right_comm n 1 m)
          ((rightMul (n + 1) m).app U ((complex.d n (n + 1)).val.app U x) b) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (complex.X q).val.obj U) (add_assoc n m 1).symm
            ((rightMul n (m + 1)).app U x ((B.complex.d m (m + 1)).val.app U b))

namespace DifferentialGradedBimodule

variable {A B : DifferentialGradedAlgebra.{t, a} R}

/-- A homomorphism of differential graded bimodules: a morphism of the underlying complexes
compatible with both actions. -/
@[stacks 0FRQ "homomorphisms of differential graded bimodules"]
structure Hom (M N : DifferentialGradedBimodule.{t, a, m} A B) where
  /-- The underlying morphism of cochain complexes. -/
  toHomologicalComplex : M.complex ⟶ N.complex
  /-- Compatibility with the right action. -/
  map_rightMul (n m : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U)
      (b : (B.complex.X m).val.obj U) :
    (toHomologicalComplex.f (n + m)).val.app U ((M.rightMul n m).app U x b) =
      (N.rightMul n m).app U ((toHomologicalComplex.f n).val.app U x) b
  /-- Compatibility with the left action. -/
  map_leftMul (n m : ℤ) (U : Cᵒᵖ) (a : (A.complex.X n).val.obj U)
      (x : (M.complex.X m).val.obj U) :
    (toHomologicalComplex.f (n + m)).val.app U ((M.leftMul n m).app U a x) =
      (N.leftMul n m).app U a ((toHomologicalComplex.f m).val.app U x)

/-- Homomorphisms of differential graded bimodules are determined degreewise. -/
@[ext]
theorem Hom.ext {M N : DifferentialGradedBimodule.{t, a, m} A B} {f g : Hom M N}
    (h : ∀ n, f.toHomologicalComplex.f n = g.toHomologicalComplex.f n) : f = g := by
  cases f
  cases g
  congr 1
  exact HomologicalComplex.hom_ext _ _ h

/-- The identity homomorphism of a differential graded bimodule. -/
def Hom.id (M : DifferentialGradedBimodule.{t, a, m} A B) : Hom M M where
  toHomologicalComplex := 𝟙 M.complex
  map_rightMul _ _ _ _ _ := rfl
  map_leftMul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of differential graded bimodules. -/
def Hom.comp {M N P : DifferentialGradedBimodule.{t, a, m} A B} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  toHomologicalComplex := f.toHomologicalComplex ≫ g.toHomologicalComplex
  map_rightMul n m U x b := by
    change (g.toHomologicalComplex.f (n + m)).val.app U
      ((f.toHomologicalComplex.f (n + m)).val.app U ((M.rightMul n m).app U x b)) = _
    rw [f.map_rightMul, g.map_rightMul]
    rfl
  map_leftMul n m U a x := by
    change (g.toHomologicalComplex.f (n + m)).val.app U
      ((f.toHomologicalComplex.f (n + m)).val.app U ((M.leftMul n m).app U a x)) = _
    rw [f.map_leftMul, g.map_leftMul]
    rfl

/-- The identity homomorphism `Hom.id M` is the identity in each degree. -/
@[simp]
theorem Hom.id_f (M : DifferentialGradedBimodule.{t, a, m} A B) (n : ℤ) :
    (Hom.id M).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- In each degree, `f.comp g` is the composite of the components of `f` and `g`. -/
@[simp]
theorem Hom.comp_f {M N P : DifferentialGradedBimodule.{t, a, m} A B} (f : Hom M N)
    (g : Hom N P) (n : ℤ) : (f.comp g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

/-- Differential graded bimodules over a fixed pair of sheaves of differential graded algebras
form a category. -/
instance instCategory : Category (DifferentialGradedBimodule.{t, a, m} A B) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp

/-- The identity morphism `𝟙 M` is the identity in each degree. -/
@[simp]
theorem id_f (M : DifferentialGradedBimodule.{t, a, m} A B) (n : ℤ) :
    (𝟙 M : M ⟶ M).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- In each degree, `f ≫ g` is the composite of the components of `f` and `g`. -/
@[simp]
theorem comp_f {M N P : DifferentialGradedBimodule.{t, a, m} A B} (f : M ⟶ N) (g : N ⟶ P)
    (n : ℤ) : (f ≫ g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

end DifferentialGradedBimodule

end SheafOfModules
