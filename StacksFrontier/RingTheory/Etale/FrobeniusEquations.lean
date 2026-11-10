module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Étaleness of algebras defined by Frobenius equations

Let `A` be a commutative ring in which the prime `p` vanishes. An algebra obtained from a
polynomial ring over `A` by imposing equations whose linear parts are the variables and whose
remaining variable terms are `p`-th powers is étale over `A`: the `p`-th powers contribute
nothing to the Jacobian, which is therefore the identity matrix.

## Main results

* `Algebra.frobeniusEquationAlgebra_isEtale`: the algebra defined by the Frobenius equations
  `bᵢ + xᵢ - ∑ⱼ aⱼᵢ xⱼᵖ` is étale over its coefficient ring.

## References

* [Stacks Project, Tag 0GKU](https://stacks.math.columbia.edu/tag/0GKU)
-/

@[expose] public section

namespace Algebra

universe u

/-- The quotient of a polynomial ring over `A` by the Frobenius equations
`bᵢ + xᵢ - ∑ⱼ aⱼᵢ xⱼᵖ`, where `p` vanishes in `A`, is étale over `A`. -/
theorem frobeniusEquationAlgebra_isEtale
    (p n : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] (hp : (p : A) = 0)
    (a : Fin n → Fin n → A) (b : Fin n → A) :
    Algebra.Etale A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range fun i : Fin n =>
        MvPolynomial.C (b i) + MvPolynomial.X i -
          ∑ j : Fin n, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p)) := by
  classical
  let f : Fin n → MvPolynomial (Fin n) A := fun i =>
    MvPolynomial.C (b i) + MvPolynomial.X i -
      ∑ j : Fin n, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p
  let B := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)
  let P : Algebra.PreSubmersivePresentation A B (Fin n) (Fin n) :=
    Algebra.PreSubmersivePresentation.naive (R := A) (v := f) _root_.id
      (fun _ _ h => h)
  have hpM : (p : MvPolynomial (Fin n) A) = 0 := by
    rw [← map_natCast (algebraMap A (MvPolynomial (Fin n) A)), hp, map_zero]
  have hfderiv (i j : Fin n) :
      MvPolynomial.pderiv i (f j) = if j = i then 1 else 0 := by
    simp [f, map_sub, map_add, map_sum, hpM, Pi.single_apply]
  have hbij : Function.Bijective P.aevalDifferential := by
    have hdiff : P.aevalDifferential = LinearMap.id := by
      apply (Pi.basisFun B (Fin n)).ext
      intro j
      ext i
      rw [Pi.basisFun_apply, P.aevalDifferential_single j i]
      change MvPolynomial.aeval P.val (MvPolynomial.pderiv i (f j)) = _
      simp [hfderiv, P, Pi.single_apply, eq_comm]
    rw [hdiff]
    exact Function.bijective_id
  let Q : Algebra.SubmersivePresentation A B (Fin n) (Fin n) :=
    ⟨P, P.isUnit_jacobian_iff_aevalDifferential_bijective.mpr hbij⟩
  exact (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := A) (S := B)).2
    (Q.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension]))

end Algebra
