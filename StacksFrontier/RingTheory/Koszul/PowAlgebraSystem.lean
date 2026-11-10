module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractDerived
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionComposite
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemProIsomorphism
public import StacksFrontier.RingTheory.Koszul.PowAlgebraMultiplication

/-!
# The Koszul algebras as an inverse system of differential graded algebras

Let `f₁, …, f_r` be elements of a commutative ring `R` and let `K_m` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ m`. For `1 ≤ n ≤ m` the transition homomorphism
`τ_{m,n} : K_m → K_n` scales `ξᵢ` by `fᵢ ^ (m - n)`, and these compose. Reindexing from a base
`b ≥ 1`, the graded opposites of `K_{b}, K_{b+1}, K_{b+2}, …` and these transitions form an
inverse system of differential graded algebras in the sense of
`DifferentialGraded.AlgebraSystem`, whose left differential graded modules are the objects of the
derived categories `D(K_{b+n}^{opp}, d)`.

The identification of a two-step restriction of scalars with a one-step one, which that structure
asks for, is `DifferentialGradedModule.derivedRestrictionComp` applied to the composition of the
transition homomorphisms.

## Main results

* `DifferentialGradedAlgebra.oppHom_comp`: the graded opposite of a composite of homomorphisms of
  differential graded algebras is the composite of the graded opposites.
* `Koszul.oppPowTransition_comp`: the transition homomorphisms compose on the graded opposites.
* `Koszul.powAlgebraSystem`: the inverse system.

## Implementation notes

Following the convention of the chapter a left differential graded module is recorded as a right
module over the graded opposite algebra, which is why the system is built from
`DifferentialGraded.Bimodule.oppAlgebra (Koszul.powAlgebra f (b + n))` rather than from the
Koszul algebras themselves; this is the convention of
`DifferentialGraded.AlgebraSystem`. Two homomorphisms of differential graded algebras with equal
underlying algebra homomorphisms are equal, which is how the composition of transitions is
transported from the underlying algebra homomorphisms, where
`Koszul.powTransition_comp` states it.

## References

* [Stacks Project, Tag 0GZ3](https://stacks.math.columbia.edu/tag/0GZ3)
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded.Bimodule

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- Two homomorphisms of differential graded algebras with the same underlying algebra
homomorphism are equal. -/
theorem hom_eq_of_toAlgebraHom_eq {A B : DifferentialGradedAlgebra.{u, u} R} {φ ψ : A.Hom B}
    (h : φ.toAlgebraHom = ψ.toAlgebraHom) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- The graded opposite of a composite of homomorphisms of differential graded algebras is the
composite of the graded opposites. -/
theorem oppHom_comp {A B C : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) (ψ : B.Hom C) :
    (oppHom ψ).comp (oppHom φ) = oppHom (ψ.comp φ) := by
  refine hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun a => ?_)
  change (oppHom ψ).toAlgebraHom ((oppHom φ).toAlgebraHom a) = _
  rw [oppHom_apply, oppHom_apply, oppHom_apply, LinearEquiv.apply_symm_apply]
  rfl

end DifferentialGradedAlgebra

namespace Koszul

open DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The transition homomorphisms of the Koszul algebras compose on the graded opposites:
`K_m → K_n` followed by `K_n → K_p` is `K_m → K_p`. -/
theorem oppPowTransition_comp (f : Fin r → R) {p n m : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n)
    (hnm : n ≤ m) :
    (oppPowTransition f hp hpn).comp (oppPowTransition f (hp.trans hpn) hnm) =
      oppPowTransition f hp (hpn.trans hnm) :=
  (oppHom_comp (powTransition f (hp.trans hpn) hnm) (powTransition f hp hpn)).trans
    (congrArg oppHom
      (hom_eq_of_toAlgebraHom_eq (powTransition_comp f hp hpn hnm)))

/-- **The Koszul algebras as an inverse system of differential graded algebras**, reindexed from
a base `b ≥ 1`: the `n`-th entry is the graded opposite of `K_{b+n}`, so that the left
differential graded `K_{b+n}`-modules are the objects of its derived category, and the transitions
are the transition homomorphisms of the Koszul algebras. -/
def powAlgebraSystem (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) :
    DifferentialGraded.AlgebraSystem R where
  alg n := oppAlgebra (powAlgebra f (b + n))
  trans h := oppPowTransition f (hb.trans (Nat.le_add_right b _)) (Nat.add_le_add_left h b)
  restrComp h h' :=
    derivedRestrictionComp
        (oppPowTransition f (hb.trans (Nat.le_add_right b _)) (Nat.add_le_add_left h' b))
        (oppPowTransition f (hb.trans (Nat.le_add_right b _)) (Nat.add_le_add_left h b)) ≪≫
      eqToIso (congrArg (fun φ => derivedRestriction φ)
        (oppPowTransition_comp f (hb.trans (Nat.le_add_right b _))
          (Nat.add_le_add_left h b) (Nat.add_le_add_left h' b)))

/-- The `n`-th algebra of the system is the graded opposite of `K_{b+n}`. -/
@[simp] theorem powAlgebraSystem_alg (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    (powAlgebraSystem f hb).alg n = oppAlgebra (powAlgebra f (b + n)) := rfl

/-- The transitions of the system are the transition homomorphisms of the Koszul algebras. -/
theorem powAlgebraSystem_trans (f : Fin r → R) {b : ℕ} (hb : 1 ≤ b) {n m : ℕ} (h : n ≤ m) :
    (powAlgebraSystem f hb).trans h =
      oppPowTransition f (hb.trans (Nat.le_add_right b n)) (Nat.add_le_add_left h b) := rfl

end Koszul

end
