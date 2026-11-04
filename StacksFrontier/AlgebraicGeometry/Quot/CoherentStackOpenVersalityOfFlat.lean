module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenVersalityFlatOfIdealMaps
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquareCompatible

/-!
# Openness of versality for `Coh_{X/B}` with `X → B` flat (Stacks 08WA)

In Situation Stacks 08KB assume that `S` is a locally Noetherian scheme, `S = B` and
`f : X → B` is flat. Then `𝒳 = Coh_{X/B}` satisfies openness of versality (Stacks 07XQ).

The proof is the second proof of the source, through Stacks 0CYF: the diagonal of `𝒳` is
representable by algebraic spaces (Stacks 08W6), `𝒳` satisfies (RS*) (Stacks 08LQ) and is limit
preserving (Stacks 08KD), and over a Noetherian affine chart its tangent spaces and obstruction
classes are read in `Ext^i_{X_A}(ℱ, ℱ ⊗ f^*M̃)` (Stacks 08VW, 0CYE), functorially in the module
and along surjections of square-zero thickenings.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.hasOpenVersality_coherentCFG_of_isFlat`.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **Openness of versality for `Coh_{X/B}`** (Stacks 08WA). In Situation Stacks 08KB assume that
`S` is a locally Noetherian scheme, `S = B` (here: the base `Y` is final) and `f : X → B` is flat.
Then `𝒳 = Coh_{X/B}` satisfies openness of versality (Stacks 07XQ).

This is the second proof of the source, through Stacks 0CYF: the diagonal of `𝒳` is representable
by algebraic spaces (Stacks 08W6), `𝒳` satisfies (RS*) (Stacks 08LQ) and is limit preserving
(Stacks 08KD), and over a Noetherian affine chart `x = (Spec A, ℱ)` the tangent space is
`T_x(M) = Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)`, naturally in `M`, and the obstruction class of a
square-zero thickening `A' → A` with kernel `I` lies in `Ext²_{X_A}(ℱ, ℱ ⊗ f^*Ĩ)`, functorially
along surjections of thickenings (Stacks 08VW, 0CYE). -/
@[stacks 08WA]
theorem hasOpenVersality_coherentCFG_of_isFlat
    [_root_.AlgebraicGeometry.IsLocallyNoetherian S] (hY : IsTerminal D.Y)
    (hflat : IsFlat B S hS D.f.hom) :
    HasOpenVersality ((coherentCFG D).val.p ⋙ Over.post B.inclusion) :=
  D.isOpenVersality_coherentCFG_of_isFlat_of_relativeIdealSquareCompatibleOfIdealMaps hY hflat
    (relativeIdealSquareCompatible_of_idealMaps D)

end AlgebraicGeometry.Space.CoherentSituation

end
