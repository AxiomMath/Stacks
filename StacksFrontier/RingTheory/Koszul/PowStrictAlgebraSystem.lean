module

public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrict
public import StacksFrontier.RingTheory.Koszul.PowAlgebraSystem

/-!
# The Koszul algebras as a strict inverse system

`Koszul.powAlgebraSystem` presents the graded opposites of the Koszul algebras
`K_b, K_{b+1}, K_{b+2}, …` as a `DifferentialGraded.AlgebraSystem`, whose compatibility between
the transition homomorphisms is recorded through the restriction functors they induce on derived
categories. The transition homomorphisms of the Koszul algebras in fact compose *on the nose*,
by `Koszul.oppPowTransition_comp`, so the system is strict in the sense of
`DifferentialGraded.StrictAlgebraSystem`, and the identification of a two-step restriction of
scalars with a one-step one is the one restriction along a composite already provides rather than
extra data.

This is what makes the module-level and bimodule-level constructions that need strictness
available for the Koszul system: a `DifferentialGraded.StrictModuleSystem` over it is a family of
differential graded modules with transition homomorphisms composing on the nose, and
`DifferentialGraded.Bimodule.DerivedTensorTower.ofSemilinear` turns such data, together with
semilinear transition homomorphisms of the bimodules, into a tower of derived tensor products.

## Main definitions

* `Koszul.powStrictAlgebraSystem`: the graded opposites of `K_{b+n}` and their transition
  homomorphisms, as a strict inverse system of differential graded algebras.

## Main results

* `Koszul.powStrictAlgebraSystem_toAlgebraSystem`: the inverse system underlying it is
  `Koszul.powAlgebraSystem`, so the two presentations agree.

## References

* [Stacks Project, Tag 0GZ3](https://stacks.math.columbia.edu/tag/0GZ3)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded.Bimodule

universe u

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The Koszul algebras as a strict inverse system of differential graded algebras**, reindexed
from a base `b ≥ 1`: the `n`-th entry is the graded opposite of `K_{b+n}` and the transitions are
the transition homomorphisms of the Koszul algebras, which compose on the nose by
`Koszul.oppPowTransition_comp`. -/
def powStrictAlgebraSystem (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) : StrictAlgebraSystem R where
  alg n := oppAlgebra (powAlgebra f (b + n))
  trans h := oppPowTransition f (hb.trans (Nat.le_add_right b _)) (Nat.add_le_add_left h b)
  trans_comp h h' :=
    oppPowTransition_comp f (hb.trans (Nat.le_add_right b _)) (Nat.add_le_add_left h b)
      (Nat.add_le_add_left h' b)

/-- The `n`-th algebra of the strict system is the graded opposite of `K_{b+n}`. -/
@[simp] theorem powStrictAlgebraSystem_alg (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    (powStrictAlgebraSystem f hb).alg n = oppAlgebra (powAlgebra f (b + n)) := rfl

/-- The transitions of the strict system are the transition homomorphisms of the Koszul
algebras. -/
theorem powStrictAlgebraSystem_trans (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) {n m : ℕ} (h : n ≤ m) :
    (powStrictAlgebraSystem f hb).trans h =
      oppPowTransition f (hb.trans (Nat.le_add_right b n)) (Nat.add_le_add_left h b) := rfl

/-- **The inverse system underlying the strict one is `Koszul.powAlgebraSystem`.** The
identification of a two-step restriction of scalars with a one-step one that
`Koszul.powAlgebraSystem` records is exactly the one a strict system provides. -/
theorem powStrictAlgebraSystem_toAlgebraSystem (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) :
    (powStrictAlgebraSystem f hb).toAlgebraSystem = powAlgebraSystem f hb := rfl

end Koszul

end
