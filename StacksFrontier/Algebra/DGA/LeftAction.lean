module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Left differential graded actions on a complex

A left action of a differential graded algebra `A` on a cochain complex `M` is
the data, for each degree `n`, of an `R`-linear map from the degree-`n` part of
`A` to the degree-`n` cochains of `M` into itself, multiplicative for the grading
and compatible with both differentials.

## Main definitions

* `DifferentialGradedAlgebra.LeftDGAction` is a left differential graded action on
  a fixed cochain complex.

## Implementation notes

The action is recorded as maps into `CochainComplex.HomComplex.Cochain M M n`
rather than as a scalar multiplication on a graded module. A cochain of degree
`n` is exactly a family of maps raising degree by `n` with no compatibility with
the differentials, so this presentation keeps the action's three laws separate:
unitality and multiplicativity are equations of cochains, and compatibility with
the differential of `A` is the statement that the action of `A.d a` is the cochain
differential `δ` applied to the action of `a`. Composition carries no Koszul sign;
the sign convention lives in `δ`.

Multiplicativity is stated in the order `(action m b).comp (action n a)`, which is
the composite acting first by `a` and then by `b`, matching the product `a * b`
under the identification of a left action with a homomorphism into endomorphisms.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace DifferentialGradedAlgebra

universe u v w

variable {R : Type u} [CommRing R]

/-- A left differential graded action on a fixed complex, expressed on
homogeneous elements. -/
structure LeftDGAction (A : DifferentialGradedAlgebra.{u, v} R)
    (M : CochainComplex (ModuleCat.{max u w} R) ℤ) where
  /-- The action of the degree-`n` part of `A` by degree-`n` cochains. -/
  action (n : ℤ) : A.grading n →ₗ[R] Cochain M M n
  /-- The unit of `A` acts as the identity. -/
  map_one : action 0 ⟨1, SetLike.one_mem_graded A.grading⟩ = Cochain.ofHom (𝟙 M)
  /-- A product acts as the composite of the actions. -/
  map_mul (n m : ℤ) (a : A.grading n) (b : A.grading m) :
    action (n + m) ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (action m b).comp (action n a) (by omega)
  /-- The differential of `A` acts by the cochain differential. -/
  map_d (n : ℤ) (a : A.grading n) :
    action (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ =
      δ n (n + 1) (action n a)

end DifferentialGradedAlgebra

end
