module

public import StacksFrontier.Algebra.DifferentialGraded.Basic

@[expose] public section

/-!
# Graded-projective differential graded modules

Let `A` be a differential graded algebra over a commutative ring `R` and let
`Mod_(A,d)` be the category of right differential graded `A`-modules
(`Stacks.DifferentialGraded.DGModule`).  A homomorphism in `Mod_(A,d)` is an *admissible
epimorphism* when it is surjective and splits as a homomorphism of the underlying
graded `A`-modules.  This file records the resulting recognition principle: a
surjection onto a target that is projective *as a graded module* is automatically
admissible, because graded projectivity supplies the splitting for free.

Projectivity here is a condition on the underlying graded module only, so it is
stated against `IsGradedLawful`, which isolates the two graded laws of a
differential graded module and imposes nothing on its differential.  This is
strictly weaker than `DGModule.IsLawful`, and deliberately so: the splitting that
witnesses admissibility is a graded homomorphism, and no compatibility between the
auxiliary differentials of the source modules and either their gradings or their
module structures is needed to produce it.

## Main definitions

* `Stacks.DifferentialGraded.DGModule.IsGradedLawful`: the laws of the graded module underlying a
  differential graded module, with no condition on its differential.
* `Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule`: projectivity as a graded module,
  expressed by the splitting of every surjective graded homomorphism onto the module.
  The source modules range over an independently chosen carrier universe.

## Main results

* `Stacks.DifferentialGraded.DGModule.isAdmissibleEpi_of_surjective_of_isProjectiveAsGradedModule`:
  a surjective differential graded homomorphism whose target is projective as a
  graded module is an admissible epimorphism.

## References

* [The Stacks Project, Tag 09K0](https://stacks.math.columbia.edu/tag/09K0)
-/

namespace Stacks.DifferentialGraded.DGModule

universe u v w w'

variable {R : Type u} [CommRing R] {A : Stacks.DifferentialGraded.DGAlgebra.{u, v} R}

/-- The laws of the graded module underlying a differential graded module, with no
conditions imposed on its differential. -/
structure IsGradedLawful (M : Stacks.DifferentialGraded.DGModule.{u, w, v} A) : Prop where
  isInternal : DirectSum.IsInternal M.grading
  grading_smul : ∀ (n m : ℤ) (x : M.carrier) (a : A.carrier),
      x ∈ M.grading n → a ∈ A.grading m →
        (MulOpposite.op a) • x ∈ M.grading (n + m)

/-- A differential graded module is projective as a graded module if every surjective
graded homomorphism from a lawful graded module onto it admits a graded section. The source
modules range over an independently chosen carrier universe. -/
def IsProjectiveAsGradedModule
    (P : DGModule.{u, w, v} A) : Prop :=
  P.IsGradedLawful ∧
    ∀ (M : DGModule.{u, w', v} A), M.IsGradedLawful →
      ∀ f : DGModule.GradedHom M P, Function.Surjective f.toFun →
        ∃ s : DGModule.GradedHom P M, ∀ y, f.toFun (s.toFun y) = y

/-- A surjective homomorphism of lawful differential graded modules whose target is
projective as a graded module is an admissible epimorphism.

The lawfulness of `A` and of `P` is part of the setting of the statement but is not
needed to produce the splitting. -/
@[stacks 09K0]
theorem isAdmissibleEpi_of_surjective_of_isProjectiveAsGradedModule
    (_hA : A.IsLawful) {M : DGModule.{u, w', v} A} {P : DGModule.{u, w, v} A}
    (hM : M.IsLawful) (_hP : P.IsLawful) (f : DGModule.Hom M P)
    (hf : Function.Surjective f.toFun)
    (hPProjective : IsProjectiveAsGradedModule.{u, v, w, w'} P) :
    DGModule.IsAdmissibleEpi f := by
  refine ⟨hf, ?_⟩
  exact hPProjective.2 M ⟨hM.isInternal, hM.grading_smul⟩ f.toGradedHom hf

end Stacks.DifferentialGraded.DGModule
