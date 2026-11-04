module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwistCompare
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# `𝒪_{X'}(E)` is the twist by `-1`

Let `X` be a scheme, let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals and let `b : X' ⟶ X` be
the blowup of `X` in `ℐ`, with exceptional divisor `E`. The sheaf `𝒪_{X'}(E)` of
[Stacks, Tag 01WX] part (1) — the dual `ℐ_E^∨` of the ideal sheaf of `E` — is the twisting sheaf
of the blowup in degree `-1`:

`𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`.

No hypothesis is carried: `X` is an arbitrary scheme and `ℐ` an arbitrary quasi-coherent sheaf of
ideals.

## The route

Two statements of the library, composed:

* part (3) of [Stacks, Tag 02OS], `AlgebraicGeometry.twistOneIsoExceptionalIdealModule`: the
  degree-one twist `𝒪_{X'}(1)` is the ideal sheaf `ℐ_E` of the exceptional divisor;
* the inversion law `Stacks.Blowup.blowUpTwistNegIsoDual` at `n = 1`: `𝒪_{X'}(-1)` is the dual of
  `𝒪_{X'}(1)`.

Dualizing the first and feeding it into the second is the whole proof, because
`Stacks.Divisors.invertibleSheaf' (exceptionalIdeal ℐ)` *is*, by definition, the dual of
`AlgebraicGeometry.exceptionalIdealModule ℐ`: both `Stacks.Divisors.negativeTwist'` and
`AlgebraicGeometry.exceptionalIdealModule` unfold to
`Stacks.ClosedImmersion.idealSheaf (exceptionalIdeal ℐ).subschemeι.toLRSHom.toShHom`.

The inversion law is what was missing until the two twisting sheaves of a blowup were identified
in `StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/BlowupTwistCompare.lean`: before that the
arithmetic of the twists was available only for `Stacks.Blowup.reesTwist`, the twist of the Rees
algebra on the `SheafGradedAlgebra` substrate, while part (3) of [Stacks, Tag 02OS] is stated for
`AlgebraicGeometry.blowUpTwist`.

## Main definitions

* `AlgebraicGeometry.blowUpTwistNegOneIsoExceptionalInvertibleSheaf`: `𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`.
* `AlgebraicGeometry.exceptionalInvertibleSheafIsoBlowUpTwistNegOne`: the same read the other way
  round.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **`𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`.** For the blowup `b : X' ⟶ X` of an arbitrary scheme in an
arbitrary quasi-coherent sheaf of ideals, with exceptional divisor `E`, the twisting sheaf in
degree `-1` is the sheaf `𝒪_{X'}(E) = ℐ_E^∨` of [Stacks, Tag 01WX] part (1).

The degree-one twist is `ℐ_E` by part (3) of [Stacks, Tag 02OS]
(`AlgebraicGeometry.twistOneIsoExceptionalIdealModule`) and the degree `-1` twist is its dual by
`Stacks.Blowup.blowUpTwistNegIsoDual`, the inversion law for `AlgebraicGeometry.blowUpTwist`. -/
def blowUpTwistNegOneIsoExceptionalInvertibleSheaf :
    blowUpTwist I (-1) ≅ Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I) :=
  Stacks.Blowup.blowUpTwistNegIsoDual I 1 ≪≫
    Stacks.SheafOfModules.dualSheafIso _ _ (twistOneIsoExceptionalIdealModule I)

/-- **`𝒪_{X'}(E) ≅ 𝒪_{X'}(-1)`**, the inverse of
`AlgebraicGeometry.blowUpTwistNegOneIsoExceptionalInvertibleSheaf`. -/
def exceptionalInvertibleSheafIsoBlowUpTwistNegOne :
    Stacks.Divisors.invertibleSheaf' (exceptionalIdeal I) ≅ blowUpTwist I (-1) :=
  (blowUpTwistNegOneIsoExceptionalInvertibleSheaf I).symm

end AlgebraicGeometry

end
