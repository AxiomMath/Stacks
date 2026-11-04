module

public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generalized Hilbert–Samuel multiplicity

For a finite module over a Noetherian local ring whose quotient by an ideal has finite,
nonzero length, the generalized multiplicity in degree `d` is `d !` times the coefficient of
degree `d` in the eventual polynomial computing the lengths of `M / I ^ n M`.

## Main definitions

* `Ideal.generalizedHilbertSamuelMultiplicity` is the generalized multiplicity `e_I(M, d)`.

## Implementation notes

The polynomial is selected from its eventual characterizing property, with the zero
polynomial as a fallback outside the Noetherian finite setting. Unlike
`Ideal.hilbertSamuelMultiplicity` of Tag 0AZV, this definition uses exactly the source's
function with exponent `n`, rather than its translate with exponent `n + 1`. Taking `coeff d`
implements the convention that the coefficient is zero when the polynomial has degree less
than `d`.

The definition is made for arbitrary ideals and modules. Under the hypotheses of the source
the required eventual polynomial exists and `d` is at least the dimension of the support.

## References

* [Stacks Project, Tag 0B00](https://stacks.math.columbia.edu/tag/0B00)
-/

@[expose] public section

open Filter Polynomial

/-- The generalized Hilbert–Samuel multiplicity `e_I(M, d)`: `d !` times the coefficient of
degree `d` in the rational polynomial eventually computing `length_R (M / I ^ n M)`.

For a finite module over a Noetherian local ring, when `M / I M` is nonzero of finite length
and `d` is at least the dimension of the support of `M`, this is the generalized multiplicity
of Tag 0B00. -/
@[stacks 0B00 "generalized_multiplicity", sga "7 X 2.6"]
noncomputable def Ideal.generalizedHilbertSamuelMultiplicity {R : Type*} [CommRing R]
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (d : ℕ) : ℚ :=
  open Classical in
  (d.factorial : ℚ) *
    (if h : ∃ P : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
          Module.length R (M ⧸ (I ^ n • (⊤ : Submodule R M))) = p ∧
            P.eval (n : ℚ) = (p : ℚ) then
        h.choose
      else 0).coeff d
