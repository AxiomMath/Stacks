module

public import Mathlib.RingTheory.Finiteness.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Finite differential graded modules

A right differential graded module over a differential graded algebra `(A, d)` is *finite* when
its underlying right `A`-module is finitely generated. Finiteness in this sense ignores the
grading and the differential. [Stacks, Tag 09R1] gives this definition and also asserts that a
finite differential graded module lying in the category `𝒟` of [Stacks, Tag 09R0] (morphisms out
of it in `K(A, d)` already compute those in `D(A, d)`) is a compact object of `D(A, d)`; that
assertion is registered under the same tag as
`DifferentialGradedModule.isCompactObject_q_of_isFinite`
(`StacksFrontier/Algebra/DifferentialGraded/Module/CompactFiniteProjective.lean`), where graded
projectivity is not needed. Finiteness alone does not make a module compact.

## Main definitions

* `DifferentialGradedModule.IsFinite`: the underlying right module is finitely generated.

## Implementation notes

The right action is encoded as a left action of the opposite algebra, so finiteness is
`Module.Finite` over that opposite ring; stating it as an abbreviation lets clients use
Mathlib's finite-module API without an unfolding lemma.

## References

* [Stacks Project, Tag 09R1](https://stacks.math.columbia.edu/tag/09R1)
-/

universe u

namespace DifferentialGradedModule

/-- A differential graded module that is finitely generated as a right module over its
differential graded algebra. -/
@[stacks 09R1 "definition of a finite differential graded module"]
public abbrev IsFinite {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : Prop := Module.Finite (MulOpposite A.A) M.M

end DifferentialGradedModule
