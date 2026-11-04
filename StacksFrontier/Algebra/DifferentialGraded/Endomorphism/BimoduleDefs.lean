module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Bimodule

/-!
# Differential graded bimodules

Let `A` and `B` be differential graded algebras over a commutative ring `R`. A differential graded
`(A, B)`-bimodule is a right differential graded `B`-module together with a compatible left
differential graded `A`-action on the complex underlying it, in the sense of Tag 0FQI. A
homomorphism of bimodules is a homomorphism of the underlying right `B`-modules that also respects
the left action on homogeneous elements.

## Main definitions

* `DifferentialGraded.Bimodule`: a differential graded `(A, B)`-bimodule.
* `DifferentialGraded.Bimodule.Hom`: a homomorphism of differential graded bimodules, and the
  resulting category.

## Implementation notes

The compatible left action is recorded as a `DifferentialGradedModule.BimoduleStructure` on the
fixed right module, i.e. a left action on its underlying complex whose homogeneous multiplications
are right `B`-linear. Compatibility of a homomorphism with the left action is stated on
homogeneous elements, where the action is a cochain component; this is the form in which it is
used, and by additivity it determines the behaviour on all of the module.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGraded

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
  (B : DifferentialGradedAlgebra R)

/-- A differential graded `(A, B)`-bimodule, presented as a right differential graded `B`-module
with a compatible left differential graded `A`-action. -/
@[stacks_fixed 0FQH "(3): a differential graded `(A, B)`-bimodule, presented as in Tag 0FQI by a \
right differential graded `B`-module together with a left differential graded `A`-action on its \
underlying complex whose homogeneous multiplications are right `B`-linear; the grading, the \
differential and the two Leibniz rules are those of the right module and of the left action. Its \
underlying graded bimodule, part (2), is `DifferentialGraded.Bimodule.toGradedBimodule`"]
structure Bimodule where
  /-- The underlying right differential graded `B`-module. -/
  rightModule : DifferentialGradedModule B
  /-- The compatible left differential graded `A`-action on its underlying complex. -/
  leftAction : DifferentialGradedModule.BimoduleStructure A B rightModule

namespace Bimodule

/-- A homomorphism of differential graded bimodules: a homomorphism of right `B`-modules which
also commutes with the left `A`-action on homogeneous elements. -/
@[ext]
structure Hom (M N : Bimodule A B) where
  /-- The underlying homomorphism of right differential graded `B`-modules. -/
  rightHom : DifferentialGradedModule.Hom M.rightModule N.rightModule
  /-- Compatibility with the left action, on homogeneous elements. -/
  map_left (n p : ℤ) (a : A.grading n) (x : M.rightModule.grading p) :
    rightHom.toFun
        ((show M.rightModule.grading (p + n) from
          (M.leftAction.1.action n a).v p (p + n) (by omega) x) : M.rightModule.M) =
      ((show N.rightModule.grading (p + n) from
        (N.leftAction.1.action n a).v p (p + n) (by omega) (rightHom.gradedMap p x)) :
          N.rightModule.M)

/-- The identity homomorphism of a differential graded bimodule. -/
def Hom.id (M : Bimodule A B) : Hom A B M M where
  rightHom := DifferentialGradedModule.Hom.id M.rightModule
  map_left _ _ _ _ := rfl

/-- Composition of homomorphisms of differential graded bimodules. -/
def Hom.comp {M N P : Bimodule A B} (f : Hom A B M N) (g : Hom A B N P) : Hom A B M P where
  rightHom := DifferentialGradedModule.Hom.comp g.rightHom f.rightHom
  map_left := by
    intro n p a x
    change g.rightHom.toFun (f.rightHom.toFun _) = _
    rw [f.map_left n p a x, g.map_left n p a (f.rightHom.gradedMap p x)]
    rfl

/-- The category of differential graded `(A, B)`-bimodules. -/
instance : Category (Bimodule A B) where
  Hom := Hom A B
  id := Hom.id A B
  comp f g := Hom.comp A B f g
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

end Bimodule

end DifferentialGraded
