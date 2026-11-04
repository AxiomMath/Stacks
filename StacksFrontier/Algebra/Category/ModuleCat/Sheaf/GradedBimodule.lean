module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Graded bimodules over sheaves of graded algebras

Let `R` be a sheaf of rings on a site and let `A` and `B` be sheaves of `ℤ`-graded
`R`-algebras. A graded `(A, B)`-bimodule is an integer-indexed family of sheaves of
`R`-modules carrying a unital left `A`-action and a unital right `B`-action which commute with
one another. Its homomorphisms are the degreewise morphisms of sheaves of modules compatible
with both actions.

## Main definitions

* `SheafOfModules.GradedBimodule` is a graded bimodule between two sheaves of graded algebras.
* `SheafOfModules.GradedBimodule.Hom` is a homomorphism of graded bimodules, and
  `SheafOfModules.GradedBimodule.instCategory` the category they form.

## Implementation notes

The two actions are `SheafOfModules.BilinearMap`s, i.e. they are presented on local sections
as biadditive maps that are linear over the sheaf of rings in each variable and compatible with
restriction. This is forced by the target `piece (n + m)` varying with the degrees, and is the
same presentation that `SheafOfModules.GradedAlgebra` and `SheafOfModules.GradedModule` use.
For the same reason the associativity, commutation and unit laws are stated with `HEq`: the
degrees indexing their two sides, such as `(i + j) + n` and `i + (j + n)`, are propositionally
but not definitionally equal.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the bimodule
pieces are independent, as for `SheafOfModules.GradedAlgebra` and
`SheafOfModules.GradedModule`; a ringed site `X` is the case `R := X.ringSheaf`.
Commutativity of `R` is not needed.

The source does not assert that graded bimodules form a category. The identity, composition and
`Category` instance below are the evident ones.

## References

* [Stacks Project, Tag 0FR5](https://stacks.math.columbia.edu/tag/0FR5)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A graded `(A, B)`-bimodule is a family of sheaves of modules indexed by `ℤ` carrying
commuting unital left `A`- and right `B`-actions. -/
@[stacks 0FR5 "graded bimodules"]
structure GradedBimodule (A B : GradedAlgebra.{t, a} R) where
  /-- The sheaf of modules in each degree. -/
  piece : ℤ → SheafOfModules.{m} R
  /-- Multiplication by a homogeneous section of `B` on the right. -/
  rightMul (n m : ℤ) : BilinearMap (piece n) (B.piece m) (piece (n + m))
  /-- Multiplication by a homogeneous section of `A` on the left. -/
  leftMul (n m : ℤ) : BilinearMap (A.piece n) (piece m) (piece (n + m))
  /-- The left action is associative. -/
  left_assoc (i j n : ℤ) (U : Cᵒᵖ) (a : (A.piece i).val.obj U) (a' : (A.piece j).val.obj U)
      (x : (piece n).val.obj U) :
    HEq ((leftMul i (j + n)).app U a ((leftMul j n).app U a' x))
      ((leftMul (i + j) n).app U ((A.mul i j).app U a a') x)
  /-- The right action is associative. -/
  right_assoc (n i j : ℤ) (U : Cᵒᵖ) (x : (piece n).val.obj U) (b : (B.piece i).val.obj U)
      (b' : (B.piece j).val.obj U) :
    HEq ((rightMul (n + i) j).app U ((rightMul n i).app U x b) b')
      ((rightMul n (i + j)).app U x ((B.mul i j).app U b b'))
  /-- The left and right actions commute. -/
  left_right_assoc (i n j : ℤ) (U : Cᵒᵖ) (a : (A.piece i).val.obj U)
      (x : (piece n).val.obj U) (b : (B.piece j).val.obj U) :
    HEq ((rightMul (i + n) j).app U ((leftMul i n).app U a x) b)
      ((leftMul i (n + j)).app U a ((rightMul n j).app U x b))
  /-- The unit of `A` acts as the identity. -/
  one_left (n : ℤ) (U : Cᵒᵖ) (x : (piece n).val.obj U) :
    HEq ((leftMul 0 n).app U (A.one.eval U) x) x
  /-- The unit of `B` acts as the identity. -/
  one_right (n : ℤ) (U : Cᵒᵖ) (x : (piece n).val.obj U) :
    HEq ((rightMul n 0).app U x (B.one.eval U)) x

namespace GradedBimodule

variable {A B : GradedAlgebra.{t, a} R}

/-- A homomorphism of graded `(A, B)`-bimodules is a degreewise morphism of sheaves of modules
which respects both actions. -/
@[stacks 0FR5 "homomorphisms of graded bimodules"]
structure Hom (M N : GradedBimodule.{t, a, m} A B) where
  /-- The morphism of sheaves of modules in each degree. -/
  app (n : ℤ) : M.piece n ⟶ N.piece n
  /-- Compatibility with the right action. -/
  map_rightMul (n m : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U) (b : (B.piece m).val.obj U) :
    (app (n + m)).val.app U ((M.rightMul n m).app U x b) =
      (N.rightMul n m).app U ((app n).val.app U x) b
  /-- Compatibility with the left action. -/
  map_leftMul (n m : ℤ) (U : Cᵒᵖ) (a : (A.piece n).val.obj U) (x : (M.piece m).val.obj U) :
    (app (n + m)).val.app U ((M.leftMul n m).app U a x) =
      (N.leftMul n m).app U a ((app m).val.app U x)

/-- Homomorphisms of graded bimodules are determined by their homogeneous components. -/
@[ext]
theorem Hom.ext {M N : GradedBimodule.{t, a, m} A B} {f g : Hom M N}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  funext n
  exact h n

/-- The identity homomorphism of a graded bimodule. -/
def Hom.id (M : GradedBimodule.{t, a, m} A B) : Hom M M where
  app _ := 𝟙 _
  map_rightMul _ _ _ _ _ := rfl
  map_leftMul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of graded bimodules. -/
def Hom.comp {M N P : GradedBimodule.{t, a, m} A B} (f : Hom M N) (g : Hom N P) : Hom M P where
  app n := f.app n ≫ g.app n
  map_rightMul n m U x b := by
    change (g.app (n + m)).val.app U
      ((f.app (n + m)).val.app U ((M.rightMul n m).app U x b)) = _
    rw [f.map_rightMul, g.map_rightMul]
    rfl
  map_leftMul n m U a x := by
    change (g.app (n + m)).val.app U
      ((f.app (n + m)).val.app U ((M.leftMul n m).app U a x)) = _
    rw [f.map_leftMul, g.map_leftMul]
    rfl

/-- The degree `n` component of the identity homomorphism is the identity. -/
@[simp]
theorem Hom.id_app (M : GradedBimodule.{t, a, m} A B) (n : ℤ) : (Hom.id M).app n = 𝟙 _ := rfl

/-- The degree `n` component of a composite is the composite of the degree `n` components. -/
@[simp]
theorem Hom.comp_app {M N P : GradedBimodule.{t, a, m} A B} (f : Hom M N) (g : Hom N P)
    (n : ℤ) : (f.comp g).app n = f.app n ≫ g.app n := rfl

/-- Graded bimodules over a fixed pair of sheaves of graded algebras form a category. -/
instance instCategory : Category (GradedBimodule.{t, a, m} A B) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp

/-- The degree `n` component of the identity morphism is the identity. -/
@[simp]
theorem id_app (M : GradedBimodule.{t, a, m} A B) (n : ℤ) : (𝟙 M : M ⟶ M).app n = 𝟙 _ := rfl

/-- The degree `n` component of a composite morphism is the composite of the degree `n`
components. -/
@[simp]
theorem comp_app {M N P : GradedBimodule.{t, a, m} A B} (f : M ⟶ N) (g : N ⟶ P) (n : ℤ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

end GradedBimodule

end SheafOfModules
