module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Polynomial.Numerical
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection

/-!
# Integrality of numerical intersection numbers

Let `k` be a field, let `X` be a proper scheme over `k`, let `i : Z ⟶ X` be a closed subscheme
of dimension at most `d` and let `𝓛_1, …, 𝓛_d` be invertible `𝒪_X`-modules.  The intersection
number `(𝓛_1 ⋯ 𝓛_d · Z)` of Stacks 0BEP is the coefficient of `n_1 ⋯ n_d` in the numerical
polynomial

`χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)`,

whose coefficients are a priori only rational.  Stacks 0BEQ says that this coefficient is
nevertheless an integer.

## Main results

* `AlgebraicGeometry.intersectionNumber_isInteger`: **Stacks 0BEQ.**  In the situation of Stacks
  0BEP there is a rational polynomial of total degree at most `d` representing the twisted Euler
  characteristics, and the coefficient of `n_1 ⋯ n_d` in it is an integer.  **No hypothesis.**
* `AlgebraicGeometry.exists_int_coeff_one_of_eval_eq_eulerCharacteristic`: the same integrality
  for *every* such polynomial, with the polynomial and its two properties as hypotheses.  This is
  the form the integrality argument proves.
* `AlgebraicGeometry.exists_int_eval_of_eval_eq_eulerCharacteristic`: such a polynomial is
  numerical, which is the hypothesis the integrality argument needs.

## Implementation notes

**The representing polynomial comes from Stacks 0BEM.**  The source's intersection number *is* a
coefficient of the numerical polynomial of Stacks 0BEM, so a statement about its integrality has
to speak about that polynomial.  Stacks 0BEM is now a theorem of this library with nothing
carried, `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`: the route through
the finite-dimensionality of coherent cohomology, Stacks 02O6, is closed by
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`.  The polynomial is
therefore produced here rather than assumed, and `AlgebraicGeometry.intersectionNumber_isInteger`
carries no hypothesis beyond the data of Stacks 0BEP.  Stacks 0BEM bounds the total degree by
`dim Supp 𝒪_Z`, which is at most `dim Z`, so the degree bound the integrality argument needs is
discharged from the dimension bound of Stacks 0BEP rather than assumed alongside it.

The universally quantified form, in which the polynomial, its representing property and its
degree bound are all hypotheses, is kept as
`AlgebraicGeometry.exists_int_coeff_one_of_eval_eq_eulerCharacteristic`.  It is what the argument
proves and it is the stronger reading — *no* polynomial of total degree at most `d` representing
those Euler characteristics has a non-integral coefficient of `n_1 ⋯ n_d` — matching
`AlgebraicGeometry.intersectionNumber_eq_coeff`, which still carries such a polynomial as a
hypothesis.

**Why there is something to prove.**  `AlgebraicGeometry.intersectionNumber` is `ℤ`-valued by
construction, being defined by the `d`-fold mixed finite difference rather than as a coefficient,
so "the intersection number is an integer" is empty when read off the Lean type.  The content of
the tag is about the source's own object, the coefficient of `n_1 ⋯ n_d` of a representing
polynomial, and that is what is stated here.  The lemma
`AlgebraicGeometry.intersectionNumber_eq_coeff` identifies the integer produced below with
`AlgebraicGeometry.intersectionNumber k f i d hd L`, so the two readings agree.

**The proof is the source's.**  The source proves the tag by expanding a numerical polynomial of
total degree at most `d` in the binomial basis and reading off the coefficient of
`(n_1 choose 1) ⋯ (n_d choose 1) = n_1 ⋯ n_d`.  What that argument needs of the polynomial is
only that it be numerical, and that is supplied by
`AlgebraicGeometry.exists_int_eval_of_eval_eq_eulerCharacteristic`: the values are Euler
characteristics, which are integers.  The polynomial step is then the general statement
`MvPolynomial.exists_int_coeff_one_of_totalDegree_le`, proved in
`StacksFrontier/Algebra/Polynomial/Numerical.lean` next to the finite-difference formula it uses.
Nothing about schemes enters it, which is why it lives there and not here.

**The hypotheses of Stacks 0BEP are kept.**  Properness of `X` over `k`, the closed immersion
`i`, the dimension bound on `Z` and the invertibility of the `𝓛_j` are all carried, because the
tag reads "in the situation of Definition 0BEP".  In the unconditional statement the dimension
bound is no longer inert: it is what turns the `dim Supp 𝒪_Z` bound of Stacks 0BEM into the
degree bound `≤ d` that the polynomial step needs.  The bound is the `≤ d` of
`AlgebraicGeometry.intersectionNumber` rather than the source's equality, which makes the
hypothesis weaker and the statement correspondingly stronger.

## References

* [Stacks Project, Tag 0BEQ](https://stacks.math.columbia.edu/tag/0BEQ)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **A polynomial representing the twisted Euler characteristics is numerical**: it takes an
integer value at every integer point, namely the Euler characteristic
`χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)` itself.

This is the hypothesis that the integrality argument of Stacks 0BEQ needs of the numerical
polynomial of Stacks 0BEM, and it holds for any polynomial representing those Euler
characteristics, with no assumption beyond the representation. -/
public theorem exists_int_eval_of_eval_eq_eulerCharacteristic (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    {d : ℕ} (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback i).obj (L j)) n)
        (isCoherent_twistedSheafUnitPullback k f i L n) : ℤ) : ℚ))
    (n : Fin d → ℤ) :
    ∃ m : ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P = (m : ℚ) :=
  ⟨_, hP n⟩

/-- **Stacks 0BEQ, for a given representing polynomial.** In the situation of Stacks 0BEP — `k` a
field, `X` a scheme proper over `k`, `i : Z ⟶ X` a closed subscheme of dimension at most `d`, and
`𝓛_1, …, 𝓛_d` invertible `𝒪_X`-modules — the coefficient of the squarefree monomial `n_1 ⋯ n_d`
in *any* rational polynomial of total degree at most `d` whose values at the integral tuples are
the Euler characteristics `χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)` is an integer.

This is the form the source's argument proves.  Stacks 0BEM provides such a polynomial, so the
hypotheses `P`, `hP` and `hdeg` can be discharged; that is
`AlgebraicGeometry.intersectionNumber_isInteger`.  The integer produced is
`AlgebraicGeometry.intersectionNumber k f i d hd L`, by
`AlgebraicGeometry.intersectionNumber_eq_coeff`.

The proof is the source's: a polynomial representing the Euler characteristics is numerical
(`AlgebraicGeometry.exists_int_eval_of_eval_eq_eulerCharacteristic`), and the coefficient of
`n_1 ⋯ n_d` of a numerical polynomial of total degree at most `d` in `d` variables is an integer
(`MvPolynomial.exists_int_coeff_one_of_totalDegree_le`). -/
public theorem exists_int_coeff_one_of_eval_eq_eulerCharacteristic (k : Type u) [Field k]
    {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (_hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    (P : MvPolynomial (Fin d) ℚ)
    (hP : ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
        (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
          (fun j => (Scheme.Modules.pullback i).obj (L j)) n)
        (isCoherent_twistedSheafUnitPullback k f i L n) : ℤ) : ℚ))
    (hdeg : P.totalDegree ≤ d) :
    ∃ m : ℤ, P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = (m : ℚ) :=
  MvPolynomial.exists_int_coeff_one_of_totalDegree_le P hdeg
    (exists_int_eval_of_eval_eq_eulerCharacteristic k f i L P hP)

/-- **Stacks 0BEQ.** In the situation of Stacks 0BEP — `k` a field, `X` a scheme proper over `k`,
`i : Z ⟶ X` a closed subscheme of dimension at most `d`, and `𝓛_1, …, 𝓛_d` invertible
`𝒪_X`-modules — the intersection number `(𝓛_1 ⋯ 𝓛_d · Z)` is an integer.

The intersection number is the coefficient of the squarefree monomial `n_1 ⋯ n_d` in the
numerical polynomial `χ(Z, 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_d^{⊗ n_d}|_Z)` of Stacks 0BEM, whose
coefficients are a priori only rational; the assertion is that this one is integral.  The
polynomial is not assumed: Stacks 0BEM, available unconditionally as
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`, produces it, and its total
degree is at most `dim Supp 𝒪_Z ≤ dim Z ≤ d`.  The integer produced is
`AlgebraicGeometry.intersectionNumber k f i d hd L`, by
`AlgebraicGeometry.intersectionNumber_eq_coeff`.

The integrality itself is
`AlgebraicGeometry.exists_int_coeff_one_of_eval_eq_eulerCharacteristic`, which holds for every
polynomial of total degree at most `d` representing those Euler characteristics. -/
@[stacks 0BEQ]
public theorem intersectionNumber_isInteger (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    ∃ P : MvPolynomial (Fin d) ℚ,
      (∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        ((@eulerCharacteristic k _ Z (i ≫ f) inferInstance
          (twistedSheaf (SheafOfModules.unit Z.ringCatSheaf)
            (fun j => (Scheme.Modules.pullback i).obj (L j)) n)
          (isCoherent_twistedSheafUnitPullback k f i L n) : ℤ) : ℚ)) ∧
        P.totalDegree ≤ d ∧
        ∃ m : ℤ, P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = (m : ℚ) := by
  have hunit : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (i ≫ f)
  obtain ⟨P, hdeg, hP⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k (i ≫ f)
    (fun j => (Scheme.Modules.pullback i).obj (L j)) (SheafOfModules.unit Z.ringCatSheaf) hunit
  have hPdeg : P.totalDegree ≤ d := by
    rcases hdeg with h | h
    · rw [h]
      simp
    · exact_mod_cast h.trans ((topologicalKrullDim_subspace_le _ _).trans hd)
  exact ⟨P, hP, hPdeg,
    exists_int_coeff_one_of_eval_eq_eulerCharacteristic k f i d hd L P hP hPdeg⟩

end AlgebraicGeometry

end
