module

public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Hilbert–Samuel multiplicity

For an ideal `I` of a commutative ring `R` and an `R`-module `M`, the Hilbert–Samuel
multiplicity in degree `d` is `d !` times the coefficient of degree `d` of the rational
polynomial which eventually computes `length_R (M / I ^ n M)`. For a finite module over a
Noetherian local ring and an ideal of definition this coefficient vanishes above the
dimension of the support, so the one-argument multiplicity reads it off in the
Hilbert–Samuel degree of `M`.

## Main definitions

* `Ideal.hilbertSamuelMultiplicity` is the multiplicity `e_I(M, d)` in a specified degree.
* `Ideal.hilbertSamuelMultiplicityOfModule` is `e_I(M)`, the multiplicity in the
  Hilbert–Samuel degree of `M`.

## Implementation notes

The computing polynomial is taken in the variable `n` for `length_R (M / I ^ (n + 1) M)`.
Translating the variable does not change the leading coefficient, so this gives the same
multiplicity as the polynomial computing `length_R (M / I ^ n M)`. As in
`Ideal.hilbertSamuelDegree`, the polynomial is selected from its eventual characterizing
property, with the zero polynomial as a fallback outside the Noetherian finite setting. The
value lies in `ℚ`; for a finite module over a Noetherian local ring and an ideal of definition it
is a nonnegative integer.

The one-argument multiplicity uses `Ideal.hilbertSamuelDegree`; for a finite module over a
Noetherian local ring that degree is the dimension of the support. The value `0` chosen for
degree `-∞` handles the zero module, whose computing polynomial is zero.

## References

* [Stacks Project, Tag 0AZV](https://stacks.math.columbia.edu/tag/0AZV)
-/

@[expose] public section

open Filter Polynomial

/-- The Hilbert–Samuel multiplicity `e_I(M, d)`: `d !` times the coefficient of degree `d`
of the rational polynomial eventually computing `length_R (M / I ^ (n + 1) M)`.

When `R` is Noetherian local, `M` is finite, `I` is an ideal of definition, and `d` is at
least the dimension of the support of `M`, this is zero if the inequality is strict and is
`d !` times the leading coefficient otherwise. -/
@[stacks 0AZV "the multiplicity `e_I(M, d)`", sga "7 X 2.6"]
public noncomputable def Ideal.hilbertSamuelMultiplicity {R : Type*} [CommRing R]
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (d : ℕ) : ℚ :=
  open Classical in
  (d.factorial : ℚ) *
    (if h : ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = p ∧
            P.eval (n : ℚ) = (p : ℚ) then
        h.choose
      else 0).coeff d

/-- The multiplicity `e_I(M)` of `M` for `I`, obtained by taking the coefficient in the
Hilbert–Samuel degree of `M`. For a finite module over a Noetherian local ring that degree is the
dimension of the support (`Module.hilbertSamuelDegree_eq_supportDim`), so this is
`e_I(M, dim(Supp(M)))`. The zero module, of degree `-∞`, is read in degree zero, where its
multiplicity is zero. -/
@[stacks 0AZV "the multiplicity `e_I(M)`", sga "7 X 2.6"]
public noncomputable abbrev Ideal.hilbertSamuelMultiplicityOfModule {R : Type*} [CommRing R]
    [IsLocalRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : ℚ :=
  Ideal.hilbertSamuelMultiplicity I M ((Module.hilbertSamuelDegree R M).unbotD 0)
