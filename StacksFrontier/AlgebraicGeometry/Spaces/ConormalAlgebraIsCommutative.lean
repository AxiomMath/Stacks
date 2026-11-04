module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackIsCommutative
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra

/-!
# The conormal algebra is commutative in every pair of degrees

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. The conormal algebra `𝒞_{Z/X,*}` of Stacks 09RN is commutative in *every* pair of
integer degrees, that is `SheafOfModules.GradedAlgebra.IsCommutative`:

`HEq ((𝒞.mul i j).app U a b) ((𝒞.mul j i).app U b a)`

heterogeneous because the two sides are sections of the pieces of degrees `i + j` and `j + i`,
which are propositionally but not definitionally equal.

## Main results

* `SheafOfModules.heq_reesMul_comm` and `SheafOfModules.isCommutative_reesGradedAlgebra`: the
  graded algebra of the powers of a sheaf of ideals is commutative in every pair of degrees.
* `AlgebraicGeometry.Space.isCommutative_kernelIdealGradedAlgebra`: the same for the powers of
  the kernel ideal sheaf of a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.isCommutative_conormalAlgebra`: **the conormal algebra is commutative
  in every pair of degrees.**

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory Opposite

/-! ### The powers of a sheaf of ideals -/

namespace SheafOfModules

universe t v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (I : (unit R).Submodule)
  (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a)

/-- **The multiplication of the graded algebra of the powers of a sheaf of ideals is commutative
in every pair of degrees.** -/
theorem heq_reesMul_comm (i j : ℤ) (X : Cᵒᵖ) (x : (reesPiece I i).val.obj X)
    (y : (reesPiece I j).val.obj X) :
    HEq ((reesMul I hcomm i j).app X x y) ((reesMul I hcomm j i).app X y x) :=
  reesPiece_heq I (add_comm i j) _ _ (by
    rw [reesVal_reesMul_app, reesVal_reesMul_app, hcomm X])

/-- **The graded algebra of the powers of a sheaf of ideals is commutative in every pair of
degrees.** -/
theorem isCommutative_reesGradedAlgebra : (reesGradedAlgebra I hcomm).IsCommutative :=
  ⟨heq_reesMul_comm I hcomm⟩

end SheafOfModules

/-! ### The conormal algebra -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The graded algebra of the powers of the kernel ideal sheaf is commutative in every pair of
degrees.** -/
theorem isCommutative_kernelIdealGradedAlgebra (f : X ⟶ Y) :
    (kernelIdealGradedAlgebra B S hS f).IsCommutative :=
  SheafOfModules.isCommutative_reesGradedAlgebra (kernelIdealSheaf B S hS f)
    (structureRingSheaf_mul_comm B S hS Y)

/-- **The conormal algebra is commutative in every pair of degrees.** -/
theorem isCommutative_conormalAlgebra (i : Z ⟶ X) :
    (conormalAlgebra B S hS i).IsCommutative :=
  Stacks.Sheaves.GradedAlgebraPullback.isCommutative_toposPullbackGradedAlgebra
    (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposModulesHom B S hS i) (kernelIdealGradedAlgebra B S hS i)
    (hB := isCommutative_kernelIdealGradedAlgebra B S hS i)

end AlgebraicGeometry.Space

end
