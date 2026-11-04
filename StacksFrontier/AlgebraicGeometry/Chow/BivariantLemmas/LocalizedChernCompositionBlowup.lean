module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBaseChange

/-!
# Making a closed subscheme an effective Cartier divisor by a blowup

Let `j : Y ⟶ X` be a closed immersion with ideal sheaf `ℐ_Y`, and let `b : X' ⟶ X` be the
blowup of `X` in `ℐ_Y`. The base change `Y ×_X X' ⟶ X'` of `j` along `b` is the closed
subscheme of `X'` cut out by the inverse image ideal `ℐ_Y 𝒪_{X'}`, which is the ideal of the
exceptional divisor; by Stacks 02OS it is an effective Cartier divisor.

When `X` is integral and locally Noetherian and `Y ≠ X` (that is, `j` is not an isomorphism,
equivalently `ℐ_Y ≠ 0`), the blowup `b` is moreover proper and birational and `X'` is integral.
This is the reduction step in the proof of Stacks 0FEC: *by Lemma 02UC it even suffices to
prove the result after blowing up `X` in a nonzero ideal ... This reduces us to the case where
`Y` is an effective Cartier divisor on `X`*.

## Main results

* `Stacks.Chow.isEffectiveCartierDivisor_ker_pullbackSnd_blowUpToBase` — for any closed
  immersion `j : Y ⟶ X`, the base change of `j` to the blowup of `X` in `ℐ_Y` is cut out by an
  effective Cartier divisor.
* `Stacks.Chow.exists_isProper_isBirational_isEffectiveCartierDivisor_ker_pullbackSnd` — for
  `X` integral and locally Noetherian and `j` not an isomorphism, some proper birational
  `b : X' ⟶ X` with `X'` integral makes the base change of `j` an effective Cartier divisor.

## Implementation notes

The source blows up `X` in the product `ℐ_Y ℐ_Z` of the ideals of two closed subschemes; only
the Cartier property for `Y` is used afterwards, so we blow up in `ℐ_Y` alone. The case
distinction `Y = X` or `ℐ_Y ≠ 0` is
`AlgebraicGeometry.IsClosedImmersion.isIso_iff_ker_eq_bot`.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsClosedImmersion j]

/-- **Stacks 02OS, for a closed subscheme.** The base change `Y ×_X X' ⟶ X'` of a closed
immersion `j : Y ⟶ X` to the blowup `X'` of `X` in the ideal of `Y` is cut out by an effective
Cartier divisor: its ideal is the inverse image of the ideal of `Y`, the exceptional ideal. -/
theorem isEffectiveCartierDivisor_ker_pullbackSnd_blowUpToBase :
    Stacks.Divisors.IsEffectiveCartierDivisor (pullback.snd j (blowUpToBase j.ker)).ker := by
  rw [ker_pullbackSnd_eq_comap]
  exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal j.ker

/-- **The blowup step of Stacks 0FEC.** Let `X` be an integral, locally Noetherian scheme and
`j : Y ⟶ X` a closed immersion which is not an isomorphism. Then there is a proper birational
morphism `b : X' ⟶ X` from an integral scheme such that the base change `Y ×_X X' ⟶ X'` of `j`
is cut out by an effective Cartier divisor: the blowup of `X` in the ideal of `Y`. -/
theorem exists_isProper_isBirational_isEffectiveCartierDivisor_ker_pullbackSnd
    [IsIntegral X] [IsLocallyNoetherian X] (hj : ¬ IsIso j) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsProper b ∧ IsBirational b ∧ IsIntegral X' ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (pullback.snd j b).ker := by
  have hI : j.ker ≠ ⊥ := fun h ↦ hj (IsClosedImmersion.isIso_iff_ker_eq_bot.mpr h)
  exact ⟨blowUp j.ker, blowUpToBase j.ker, inferInstance, isBirational_blowUpToBase _ hI,
    isIntegral_blowUp _ hI, isEffectiveCartierDivisor_ker_pullbackSnd_blowUpToBase j⟩

end Stacks.Chow
