module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleDefs
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# Restricting the left action of a differential graded bimodule

Let `R` be a commutative ring, let `A'`, `A` and `B` be differential graded `R`-algebras and let
`φ : A' → A` be a homomorphism of differential graded algebras. A differential graded
`(A, B)`-bimodule becomes a differential graded `(A', B)`-bimodule by letting `A'` act through
`φ`: the underlying right `B`-module is unchanged, and the left action in degree `n` is the left
action of `A` precomposed with `φ` on the degree-`n` pieces.

This is the mirror of `DifferentialGraded.Bimodule.restrictRight`, which restricts the right
action along a homomorphism of differential graded algebras into the right algebra.

## Main definitions

* `DifferentialGradedAlgebra.Hom.gradingMap`: a homomorphism of differential graded algebras, read
  on the degree-`n` pieces of the gradings.
* `DifferentialGradedAlgebra.LeftAction.restrictAlong`: a left differential graded action on a
  cochain complex, restricted along a homomorphism of differential graded algebras.
* `DifferentialGradedModule.BimoduleStructure.restrictLeft` and
  `DifferentialGraded.Bimodule.restrictLeft`: the restricted bimodule structure, and the
  restricted bimodule.

## Implementation notes

A left differential graded action is `DifferentialGradedAlgebra.LeftAction`, which records the
action of the degree-`n` part by degree-`n` cochains of the underlying complex; restricting it
along `φ` therefore only precomposes with `φ` on gradings, and the three laws follow from `φ`
preserving the unit, products and the differential. The right `B`-linearity of every homogeneous
multiplication, which is what upgrades an action to a bimodule structure, is then inherited
unchanged: the restricted action in degree `n` at `a` is literally the original action at `φ a`.

## References

* [Stacks Project, Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
* [Stacks Project, Tag 061X](https://stacks.math.columbia.edu/tag/061X)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A' A : DifferentialGradedAlgebra.{u, u} R}

/-- A homomorphism of differential graded algebras, read on the degree-`n` pieces of the two
gradings. -/
def Hom.gradingMap (φ : A'.Hom A) (n : ℤ) : A'.grading n →ₗ[R] A.grading n where
  toFun a := ⟨φ.toAlgebraHom a, φ.map_grading n a a.property⟩
  map_add' _ _ := Subtype.ext (_root_.map_add φ.toAlgebraHom _ _)
  map_smul' r _ := Subtype.ext (_root_.map_smul φ.toAlgebraHom r _)

/-- The underlying element of `φ.gradingMap n a` is the image of `a` under `φ`. -/
@[simp] theorem Hom.gradingMap_coe (φ : A'.Hom A) (n : ℤ) (a : A'.grading n) :
    ((φ.gradingMap n a : A.grading n) : A.A) = φ.toAlgebraHom a := rfl

/-- A left differential graded action of `A` on a cochain complex, restricted along a
homomorphism `φ : A' → A` of differential graded algebras: the degree-`n` part of `A'` acts
through `φ`. -/
def LeftAction.restrictAlong (φ : A'.Hom A) {M : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : A.LeftAction M) : A'.LeftAction M where
  action n := (L.action n).comp (φ.gradingMap n)
  map_one := by
    have h : φ.gradingMap 0 ⟨1, SetLike.one_mem_graded A'.grading⟩ =
        ⟨1, SetLike.one_mem_graded A.grading⟩ :=
      Subtype.ext (_root_.map_one φ.toAlgebraHom)
    change L.action 0 (φ.gradingMap 0 _) = _
    rw [h]
    exact L.map_one
  map_mul n m a b := by
    have h : φ.gradingMap (n + m)
          ⟨(a : A'.A) * (b : A'.A), SetLike.mul_mem_graded a.property b.property⟩ =
        ⟨((φ.gradingMap n a : A.grading n) : A.A) * ((φ.gradingMap m b : A.grading m) : A.A),
          SetLike.mul_mem_graded (φ.gradingMap n a).property (φ.gradingMap m b).property⟩ :=
      Subtype.ext (_root_.map_mul φ.toAlgebraHom _ _)
    change L.action (n + m) (φ.gradingMap (n + m) _) = _
    rw [h]
    exact L.map_mul n m (φ.gradingMap n a) (φ.gradingMap m b)
  map_d n a := by
    have h : φ.gradingMap (n + 1) ⟨A'.d a, A'.d_mem n a a.property⟩ =
        ⟨A.d ((φ.gradingMap n a : A.grading n) : A.A),
          A.d_mem n _ (φ.gradingMap n a).property⟩ :=
      Subtype.ext (φ.map_d _)
    change L.action (n + 1) (φ.gradingMap (n + 1) _) = _
    rw [h]
    exact L.map_d n (φ.gradingMap n a)

/-- The restricted action in degree `n` at `a` is the original action at `φ a`. -/
@[simp] theorem LeftAction.restrictAlong_action (φ : A'.Hom A)
    {M : CochainComplex (ModuleCat.{u} R) ℤ} (L : A.LeftAction M) (n : ℤ) (a : A'.grading n) :
    (LeftAction.restrictAlong φ L).action n a = L.action n (φ.gradingMap n a) := rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A' A B : DifferentialGradedAlgebra.{u, u} R}

/-- A compatible left differential graded `A`-action on a right differential graded `B`-module,
restricted along a homomorphism `φ : A' → A`: the homogeneous multiplications are the original
ones, so they are still right `B`-linear. -/
def BimoduleStructure.restrictLeft (φ : A'.Hom A) {M : DifferentialGradedModule.{u, u, u} B}
    (L : BimoduleStructure A B M) : BimoduleStructure A' B M :=
  ⟨DifferentialGradedAlgebra.LeftAction.restrictAlong φ L.1,
    fun n a => L.2 n (φ.gradingMap n a)⟩

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A' A B : DifferentialGradedAlgebra.{u, u} R}

/-- A differential graded `(A, B)`-bimodule, restricted on the left along a homomorphism
`φ : A' → A` of differential graded algebras: the same right `B`-module, with `A'` acting on the
left through `φ`. -/
def Bimodule.restrictLeft (φ : A'.Hom A) (N : Bimodule A B) : Bimodule A' B where
  rightModule := N.rightModule
  leftAction := BimoduleStructure.restrictLeft φ N.leftAction

/-- The restricted bimodule has the same underlying right `B`-module as the original one. -/
@[simp] theorem Bimodule.restrictLeft_rightModule (φ : A'.Hom A) (N : Bimodule A B) :
    (Bimodule.restrictLeft φ N).rightModule = N.rightModule := rfl

/-- The left action of the restricted bimodule in degree `n` at `a` is the original left action
at `φ a`. -/
theorem Bimodule.restrictLeft_action (φ : A'.Hom A) (N : Bimodule A B) (n : ℤ)
    (a : A'.grading n) :
    (Bimodule.restrictLeft φ N).leftAction.1.action n a =
      N.leftAction.1.action n (φ.gradingMap n a) := rfl

end DifferentialGraded

end
