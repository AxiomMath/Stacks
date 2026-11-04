module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory

/-!
# Differential graded bimodule structures and endomorphisms

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `M` be a right
differential graded `B`-module. A left differential graded action of `A` on the complex underlying
`M` makes `M` a differential graded `(A, B)`-bimodule exactly when every homogeneous left
multiplication is right `B`-linear. Such actions correspond to homomorphisms of differential graded
algebras from `A` into the right `B`-linear endomorphisms of `M`.

## Main definitions

* `DifferentialGradedModule.IsRightLinearCochain`: a homogeneous cochain of the underlying complex
  is induced by a homogeneous morphism of right `B`-modules.
* `DifferentialGradedModule.BimoduleStructure`: a compatible left action on a fixed right module.
* `DifferentialGradedModule.RightLinearEndomorphismHom`: a homomorphism of differential graded
  algebras all of whose homogeneous images are right `B`-linear.

## Main results

* `DifferentialGradedModule.bimoduleStructureEquivRightLinearEndomorphismHom`: the
  correspondence, together with its canonical formula on homogeneous elements.

## Implementation notes

The right-linear endomorphism differential graded algebra is represented here by its inclusion in
the endomorphism algebra of the underlying complex: a homomorphism into that subalgebra is a
homomorphism into the full endomorphism algebra each of whose homogeneous images is right
`B`-linear, and right `B`-linearity is expressed through the homogeneous morphisms of the
differential graded category of right `B`-modules. A left action on the underlying complex is the
equivalent action-on-pieces presentation of a left differential graded module.

## References

* [Stacks Project, Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]
variable (A : DifferentialGradedAlgebra R) (B : DifferentialGradedAlgebra R)
variable (M : DifferentialGradedModule B)

/-- A homogeneous cochain of the complex underlying `M` is right `B`-linear if it is induced by a
homogeneous morphism of right `B`-modules. -/
def IsRightLinearCochain {n : ℤ} (f : Cochain M.toCochainComplex M.toCochainComplex n) : Prop :=
  ∃ g : HomogeneousMap B M M n,
    ∀ (p : ℤ) (x : M.grading p),
      ((show M.grading (p + n) from f.v p (p + n) rfl x) : M.M) = g.1 x

/-- A differential graded `(A, B)`-bimodule structure compatible with the fixed right differential
graded `B`-module `M`: a left differential graded action of `A` on the underlying complex all of
whose homogeneous multiplications are right `B`-linear. -/
def BimoduleStructure : Type u :=
  { L : A.LeftAction M.toCochainComplex //
    ∀ (n : ℤ) (a : A.grading n), IsRightLinearCochain B M (L.action n a) }

/-- A homomorphism of differential graded algebras from `A` into the right `B`-linear
endomorphisms of `M`, represented by its inclusion into all endomorphisms of the underlying
complex. -/
def RightLinearEndomorphismHom : Type u :=
  { φ : A.Hom (endomorphismDGA M.toCochainComplex).algebra //
    ∀ (n : ℤ) (a : A.grading n),
      IsRightLinearCochain B M
        ((endomorphismDGA M.toCochainComplex).cochainEquiv n
          ⟨φ.toAlgebraHom a, φ.map_grading n a a.property⟩) }

/-- Compatible left differential graded actions on a fixed right differential graded `B`-module
correspond bijectively to homomorphisms into its right `B`-linear endomorphism differential graded
algebra. The specified equation makes the correspondence canonical on every homogeneous element. -/
@[stacks 0FQI]
noncomputable def bimoduleStructureEquivRightLinearEndomorphismHom :
    { e : BimoduleStructure A B M ≃ RightLinearEndomorphismHom A B M //
      ∀ (L : BimoduleStructure A B M) (n : ℤ) (a : A.grading n),
        (endomorphismDGA M.toCochainComplex).cochainEquiv n
          ⟨(e L).1.toAlgebraHom a, (e L).1.map_grading n a a.property⟩ = L.1.action n a } := by
  let base := (DifferentialGradedAlgebra.leftActionEquivHom A M.toCochainComplex).1
  let base_spec := (DifferentialGradedAlgebra.leftActionEquivHom A M.toCochainComplex).2
  refine ⟨
    { toFun := fun L => ⟨base L.1, ?_⟩
      invFun := fun φ => ⟨base.symm φ.1, ?_⟩
      left_inv := fun L => Subtype.ext (base.left_inv L.1)
      right_inv := fun φ => Subtype.ext (base.right_inv φ.1) }, ?_⟩
  · exact fun n a => (base_spec L.1 n a).symm ▸ L.2 n a
  · intro n a
    have h := base_spec (base.symm φ.1) n a
    rw [base.apply_symm_apply φ.1] at h
    exact h ▸ φ.2 n a
  · exact fun L => base_spec L.1

end DifferentialGradedModule
