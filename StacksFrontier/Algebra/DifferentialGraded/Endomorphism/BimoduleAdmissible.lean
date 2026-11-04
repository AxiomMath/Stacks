module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible

/-!
# Admissible short exact sequences of differential graded bimodules

Let `A` and `B` be differential graded algebras over a commutative ring `R`. A homomorphism of
*graded* differential graded `(A, B)`-bimodules is a degree-preserving right `B`-linear map which
commutes with the homogeneous left `A`-multiplications; unlike a homomorphism of differential
graded bimodules it is not required to commute with the differentials. A short exact sequence of
differential graded bimodules is *admissible* when it is split as a sequence of graded bimodules.
This is the bimodule counterpart of
`StacksFrontier/Algebra/DifferentialGraded/Module/Admissible.lean`, which treats right differential
graded modules over a single algebra.

## Main definitions

* `DifferentialGraded.Bimodule.GradedHom`: a homomorphism of graded bimodules.
* `DifferentialGraded.Bimodule.Hom.toGradedHom`: forget compatibility with the differentials.
* `DifferentialGraded.Bimodule.IsAdmissibleShortExact`: a short exact sequence of differential
  graded bimodules split in graded bimodules.

## Implementation notes

`GradedHom` is modelled on `DifferentialGraded.Bimodule.Hom`, replacing the underlying
homomorphism of right differential graded `B`-modules by a homomorphism of graded right
`B`-modules and keeping the compatibility with the left action unchanged. As there,
compatibility with the left action is stated on homogeneous elements, where the action is a
cochain component; by additivity this determines the behaviour on the whole bimodule.

Both graded splittings are recorded in `IsAdmissibleShortExact`, as in the single-algebra case:
for a short exact sequence either splitting determines the other, so requiring both does not
strengthen the condition, and consumers need each of them explicitly.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences of differential graded modules
* [Stacks Project, Tag 0FQL](https://stacks.math.columbia.edu/tag/0FQL), where admissibility of a
  sequence of differential graded bimodules is asserted
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGraded

universe u

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
  (B : DifferentialGradedAlgebra R)

namespace Bimodule

/-- A homomorphism of graded differential graded `(A, B)`-bimodules: a homomorphism of the
underlying graded right `B`-modules which also commutes with the left `A`-action on homogeneous
elements. It is not required to commute with the differentials. -/
@[ext]
structure GradedHom (M N : Bimodule A B) where
  /-- The underlying homomorphism of graded right `B`-modules. -/
  rightHom : DifferentialGradedModule.GradedHom M.rightModule N.rightModule
  /-- Compatibility with the left action, on homogeneous elements. -/
  map_left (n p : ℤ) (a : A.grading n) (x : M.rightModule.grading p) :
    rightHom.toFun
        ((show M.rightModule.grading (p + n) from
          (M.leftAction.1.action n a).v p (p + n) (by omega) x) : M.rightModule.M) =
      ((show N.rightModule.grading (p + n) from
        (N.leftAction.1.action n a).v p (p + n) (by omega)
          ⟨rightHom.toFun x, rightHom.map_grading p x x.property⟩) : N.rightModule.M)

/-- Forget compatibility with the differentials. -/
def Hom.toGradedHom {M N : Bimodule A B} (f : Hom A B M N) : GradedHom A B M N where
  rightHom := f.rightHom.toGradedHom
  map_left := f.map_left

/-- A short exact sequence of differential graded `(A, B)`-bimodules which is split as a sequence
of graded `(A, B)`-bimodules. -/
structure IsAdmissibleShortExact {K L M : Bimodule A B}
    (f : Hom A B K L) (g : Hom A B L M) : Prop where
  /-- The first map is injective. -/
  injective : Function.Injective f.rightHom.toFun
  /-- The second map is surjective. -/
  surjective : Function.Surjective g.rightHom.toFun
  /-- The sequence is exact in the middle. -/
  exact : LinearMap.range f.rightHom.toFun = LinearMap.ker g.rightHom.toFun
  /-- The first map has a graded bimodule retraction. -/
  splitMono : ∃ π : GradedHom A B L K,
    ∀ x : K.rightModule.M, π.rightHom.toFun (f.rightHom.toFun x) = x
  /-- The second map has a graded bimodule section. -/
  splitEpi : ∃ s : GradedHom A B M L,
    ∀ x : M.rightModule.M, g.rightHom.toFun (s.rightHom.toFun x) = x

end Bimodule

end DifferentialGraded

end
