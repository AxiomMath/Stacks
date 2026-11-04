module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section



/-!
# The Hilbert polynomial of a module relative to an ideal

Let `R` be a commutative ring, let `I ⊆ R` be an ideal and let `M` be an `R`-module. The *Hilbert
function* of `M` relative to `I` is

`φ_{I,M} : n ↦ length_R (I ^ n M / I ^ (n + 1) M)`,

and the *Hilbert polynomial* of `M` relative to `I` is the polynomial `P ∈ ℚ[t]` with
`P(n) = φ_{I,M}(n)` for all `n ≫ 0`. At most one polynomial has this property, since two
polynomials agreeing at every large natural number agree at infinitely many rationals and are
therefore equal (`Polynomial.eq_of_infinite_eval_eq`), so the property defines an element of `ℚ[t]`
wherever it is satisfiable. It is satisfiable when `R` is Noetherian local, `M` is finite and `I`
is an ideal of definition of `R` — in particular for `I` the maximal ideal, which is the Hilbert
polynomial of Definition 09CA — because `φ_{I,M}` is then a numerical polynomial
(`Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul`, Tag 00K8).

## Main definitions

* `Ideal.hilbertPolynomial`: the Hilbert polynomial `P ∈ ℚ[t]` of an `R`-module `M` relative to an
  ideal `I ⊆ R`, characterised by `P(n) = length_R (I ^ n M / I ^ (n + 1) M)` for all `n ≫ 0`.

## Implementation notes

The source states Definition 09CA for `I` the maximal ideal of a Noetherian local ring `R` and `M`
a finite `R`-module, writing `φ_M` for `φ_{m,M}`. The construction consumes none of those three
hypotheses, and the surrounding section is uniformly relative to an ideal of definition `I`
(Tag 07DU): Lemma 00K9 is the statement that `deg φ_{I,M}` does not depend on `I`, so it cannot be
phrased with an `m`-only polynomial. The general form is therefore what is defined and tagged here,
and Definition 09CA is `(IsLocalRing.maximalIdeal R).hilbertPolynomial M`. That specialisation is a
composite of two existing names with no properties of its own, so it is not given a third name.

The polynomial is *characterised* rather than constructed, as in the source, which defines it as
"the element `P(t) ∈ ℚ[t]` such that `P(n) = φ_M(n)` for `n ≫ 0`" and records existence afterwards
by Proposition 00K8. So the value is the polynomial with that property, and `0` in the case that no
polynomial has it — a case that is vacuous under the source's hypotheses, so that over a Noetherian
local ring, for a finite module and an ideal of definition, the value is the source's `P`. The
hypotheses making the property satisfiable belong to the statements *about* the Hilbert polynomial
rather than to the definition, whose only argument beyond `M` is the ideal to filter by.

Finiteness of the lengths is part of the characterising property, in the shape
`∃ p : ℕ, Module.length R … = p ∧ P.eval (n : ℚ) = p`, rather than hidden behind `ENat.toNat`; the
source records that finiteness in the discussion preceding `φ_{I,M}`. This shape is also what makes
the property determine `P`: the two witnesses `p` at a given `n` are forced equal by injectivity of
`ℕ → ℕ∞`. The module `I ^ n M` is spelled `I ^ n • (⊤ : Submodule R M)` and the subquotient
`I ^ n M / I ^ (n + 1) M` as `↥(I ^ n • ⊤) ⧸ (I ^ (n + 1) • ⊤).submoduleOf (I ^ n • ⊤)`, the
spellings of Tags 00K8 and 00K9, so that the three statements speak of one `φ_{I,M}`. The index
convention is the source's: `n = 0` gives `φ_{I,M}(0) = length_R (M / IM)`.

Mathlib's `Polynomial.hilbertPoly p d` is a different polynomial: it computes the coefficients of
the power series `p * (1 - X)⁻ᵈ`, the Hilbert–Serre setting of a graded module over a polynomial
ring, and does not specialise to the `I`-adic Hilbert function of a local ring.

Faithfulness. (1) Every hypothesis is used: there are none beyond `CommRing R` and the module
structure, all of which the conclusion mentions; the source's `IsNoetherianRing R` and
`Module.Finite R M` are dropped rather than carried dead, since they are what makes the property
satisfiable and so appear on the lemmas, and they are not vacuously absent — over the
non-Noetherian local ring `k[x₁, x₂, …]` localised at `(x₁, x₂, …)` every `φ_{m,M}(n)` is `⊤` for
`M = R`, so no polynomial has the property and the value is the fallback `0`.
(2) The scalars and base are the source's: the lengths are lengths of `R`-modules, not of modules
over `R / I`, over the residue field, or over the associated graded ring `⨁_d I ^ d / I ^ (d + 1)`,
and the polynomial has rational coefficients evaluated at the rational cast of `n`, as in the
source's `P(t) ∈ ℚ[t]`.
(3) The source names an element and the definition pins it: uniqueness of a polynomial with the
characterising property makes the value that element, not a mere assertion that one exists.
(4) The instantiation is not degenerate: for a discrete valuation ring `R` with `I = m` and `M = R`
one has `φ_{I,M} ≡ 1`, so the Hilbert polynomial is the constant `1`, and for `R = k[[x, y]]` with
`I = m` and `M = R` one has `φ_{I,M}(n) = n + 1`, so it is `t + 1`; the value is neither always the
fallback `0` nor always constant.

## References

* [Stacks Project, Tag 09CA](https://stacks.math.columbia.edu/tag/09CA)

## Tags

Hilbert polynomial, Hilbert function, ideal of definition, Noetherian local ring, length
-/

@[expose] public section

open Filter Polynomial in
/-- **Stacks 09CA.** The *Hilbert polynomial* of an `R`-module `M` relative to an ideal `I ⊆ R`:
the polynomial `P ∈ ℚ[t]` such that `P(n) = φ_{I,M}(n) = length_R (I ^ n M / I ^ (n + 1) M)` for
all `n ≫ 0`. At most one polynomial has this property, so this is a definition of that element;
the value is `0` in the case that none has it. For `R` Noetherian local, `M` finite and `I` an
ideal of definition — in particular for `I = m`, the Hilbert polynomial of `M` over `R` — such a
`P` exists by Proposition 00K8. -/
@[stacks 09CA "Stated relative to an ideal `I ⊆ R`, as the rest of the section is (Tags 00K8, 00K9,
00KA); the Hilbert polynomial of Definition 09CA is the case `I = IsLocalRing.maximalIdeal R`, for
`R` Noetherian local and `M` finite, where Proposition 00K8 makes the characterising property
satisfiable. The property is what the definition consumes, and it determines the polynomial
uniquely; the value is `0` where nothing has it."]
public noncomputable def Ideal.hilbertPolynomial {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] : ℚ[X] :=
  open Classical in
  if h : ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
          (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) = p ∧
        P.eval (n : ℚ) = (p : ℚ) then
    h.choose
  else 0

end
