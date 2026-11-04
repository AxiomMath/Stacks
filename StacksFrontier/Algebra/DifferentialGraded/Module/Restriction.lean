module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Restriction of scalars for differential graded modules

A homomorphism `φ : A → B` of differential graded algebras over a commutative ring `R` — an
`R`-algebra map preserving the grading and commuting with the differentials — makes every right
differential graded `B`-module into a right differential graded `A`-module, without changing its
underlying module, its grading or its differential.

## Main definitions

* `DifferentialGradedAlgebra.Hom`: a homomorphism of differential graded algebras.
* `DifferentialGradedModule.restrictScalars`: restriction of a differential graded module along
  such a homomorphism.

## Implementation notes

The restriction keeps the underlying module and differential and composes the right action with
the opposite of the algebra homomorphism; the compatibility of the `R`-module structure with the
new action is inherited from the old one because `φ` is an `R`-algebra map. The definition is
implicitly reducible so clients can compute its underlying module, grading and differential.

This module is also where the two definitions of Section 22.3 are registered: the differential
graded algebra itself (Tag 061V), which `DifferentialGradedAlgebra` is, and its homomorphisms
(Tag 061X), defined here.

## References

* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V)
* [Stacks Project, Tag 061X](https://stacks.math.columbia.edu/tag/061X)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public section

universe u

/-- A homomorphism of differential graded algebras over `R`: an `R`-algebra map that preserves
the grading and commutes with the differentials. -/
structure DifferentialGradedAlgebra.Hom {R : Type u} [CommRing R]
    (A B : DifferentialGradedAlgebra R) where
  /-- The underlying `R`-algebra homomorphism. -/
  toAlgebraHom : A.A →ₐ[R] B.A
  /-- Compatibility with the gradings. -/
  map_grading : ∀ n a, a ∈ A.grading n → toAlgebraHom a ∈ B.grading n
  /-- Compatibility with the differentials. -/
  map_d : ∀ a, toAlgebraHom (A.d a) = B.d (toAlgebraHom a)

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- Restrict a right differential graded `B`-module to `A` along a homomorphism of differential
graded algebras. -/
@[stacks 0BYX "restriction_notation", implicit_reducible, ega "II 2.8.6" "more general"]
def restrictScalars (φ : A.Hom B) (N : DifferentialGradedModule B) :
    DifferentialGradedModule A := by
  letI : Module (MulOpposite A.A) N.M :=
    Module.compHom N.M (RingHom.op φ.toAlgebraHom.toRingHom)
  haveI : IsScalarTower R (MulOpposite A.A) N.M := by
    constructor
    intro r a x
    change (MulOpposite.op (φ.toAlgebraHom (MulOpposite.unop (r • a)))) • x =
      r • ((MulOpposite.op (φ.toAlgebraHom (MulOpposite.unop a))) • x)
    simpa [Algebra.smul_def, mul_smul] using
      (smul_assoc r (MulOpposite.op (φ.toAlgebraHom (MulOpposite.unop a))) x)
  exact
    { M := N.M
      grading := N.grading
      d := N.d
      d_comp_d := N.d_comp_d
      d_mem := N.d_mem
      smul_mem := fun n m x a hx ha =>
        N.smul_mem n m x (φ.toAlgebraHom a) hx (φ.map_grading m a ha)
      leibniz := by
        intro n m x a hx ha
        change N.d ((MulOpposite.op (φ.toAlgebraHom a)) • x) =
          (MulOpposite.op (φ.toAlgebraHom a)) • N.d x +
            (n.negOnePow : ℤ) • ((MulOpposite.op (φ.toAlgebraHom (A.d a))) • x)
        rw [φ.map_d a]
        exact N.leibniz n m x (φ.toAlgebraHom a) hx (φ.map_grading m a ha) }

end DifferentialGradedModule

add_to_stacks 061V "differential graded algebras" DifferentialGradedAlgebra
add_to_stacks 061X "homomorphisms of differential graded algebras" DifferentialGradedAlgebra.Hom
