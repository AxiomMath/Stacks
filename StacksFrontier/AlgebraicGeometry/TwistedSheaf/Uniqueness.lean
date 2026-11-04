module

public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler-characteristic polynomial of Tag 0BEM is unique

[Stacks, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM) produces a rational polynomial
whose values at the integer points are the Euler characteristics of the twists
`ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` of a coherent sheaf on a proper scheme over a field. That
polynomial is **determined** by those values, and this file says so.

The existence half of the tag is still conditional on the two geometric inputs of
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf`. The uniqueness half is not conditional
on anything: a rational polynomial in finitely many variables is determined by its values at
the integer points, since in each variable the integers are an infinite subset of `ℚ`
(`MvPolynomial.eq_of_eval_intCast_eq`). So the whole package Tag 0BEM is usually quoted
through — a canonical polynomial, its values, its degree bound and its characterization by
those values — follows from the bare existence statement, with no further geometry.

## Main results

* `AlgebraicGeometry.eulerPolynomial_twistedSheaf_unique`: **unconditional.** Two rational
  polynomials whose values at the integer points are the Euler characteristics of the twists of
  one coherent sheaf are equal.
* `AlgebraicGeometry.existsUnique_eulerPolynomial_twistedSheaf`: the existence statement of Tag
  0BEM upgraded to `∃!`. Taking `Classical.choose` of this gives the canonical polynomial, and
  its defining property then supplies both the evaluation identity and the degree bound, while
  the uniqueness clause is the characterization.

## Implementation notes

**Why uniqueness is stated for an arbitrary pair rather than against a chosen polynomial.** The
chapter-33 statements define their polynomial as `Classical.choose` of the existence statement, so a
uniqueness lemma phrased against that choice can only be used once the existence statement is
available as a term. Phrased for an arbitrary pair, the lemma is usable now and composes with
any later proof of existence — including the conditional
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf`, which is how
`AlgebraicGeometry.existsUnique_eulerPolynomial_twistedSheaf` is meant to be fed.

**Only the evaluation clause is used for uniqueness.** The degree bound plays no part: the
values at the integer points already pin the polynomial down. That is why the `∃!` statement
takes the existence of a polynomial satisfying *both* clauses and returns uniqueness among
those satisfying both — the disjunction is carried along, not used.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {r : ℕ}
  (L : Fin r → X.Modules)
  [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)]
  (F : X.Modules) (hF : SheafOfModules.IsCoherent F)

/-- **The polynomial of [Stacks, Tag 0BEM] is unique.** Two rational polynomials in `r`
variables whose values at every integer point are the Euler characteristics of the
corresponding twists of `ℱ` are equal, because a rational polynomial is determined by its
values at the integer points. Nothing here is conditional on the geometric inputs of Tag
0BEM. -/
@[ega "III 2.5.3" "(i), uniqueness clause"]
theorem eulerPolynomial_twistedSheaf_unique {P Q : MvPolynomial (Fin r) ℚ}
    (hP : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
      = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
          (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ))
    (hQ : ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) Q
      = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
          (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ)) :
    P = Q :=
  MvPolynomial.eq_of_eval_intCast_eq fun n => (hP n).trans (hQ n).symm

/-- **[Stacks, Tag 0BEM] with its polynomial characterized.** The existence statement of the
tag, upgraded from `∃` to `∃!` by
`AlgebraicGeometry.eulerPolynomial_twistedSheaf_unique`. Feed it
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf`, or any other proof of the existence
statement, and the canonical polynomial together with its characterization follows. -/
theorem existsUnique_eulerPolynomial_twistedSheaf
    (h : ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ)) :
    ∃! P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  h.imp fun _ hP =>
    ⟨hP, fun _ hQ => eulerPolynomial_twistedSheaf_unique k f L F hF hQ.2 hP.2⟩

end AlgebraicGeometry

end
