module

public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Devissage
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic

/-!
# The dévissage of [Stacks, Tag 02O5] loses nothing

`StacksFrontier/AlgebraicGeometry/ProperCoherentImage/Devissage.lean` reduces the affine-base case
of [Stacks, Tag 02O5] to its *integral-ideal* case: it suffices to prove that every higher direct
image `R ᵖ f_* (i_* I)` is coherent, where `i : Z ⟶ X` is a closed immersion of an integral
scheme and `I ⊆ 𝒪_Z` is a quasi-coherent ideal sheaf. That reduction was recorded there as a
sufficient condition only, with the converse stated to be out of reach.

The converse is proved here, with no hypothesis, so the reduction is an **equivalence**: the
integral-ideal case of [Stacks, Tag 02O5] is not weaker than the affine-base case, and the
affine-base case is not weaker than the whole tag. The only input is that `i_* I` is a coherent
`𝒪_X`-module, which is
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit` — the
closed-immersion case of [Stacks, Tag 01Y6] in degree zero — together with the fact that the
source of a proper morphism to a locally Noetherian scheme is locally Noetherian.

## Main results

Writing `AlgebraicGeometry.ProperCoherentImage` for the namespace of both:

* `higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals`: the two are equivalent, given
  the irreducible dévissage of [Stacks, Tag 01YF] for Noetherian schemes.
* `higherDirectImageIsCoherent_iff_integralIdeals`: the same, composed with the lossless affine
  reduction, so that the first assertion of [Stacks, Tag 02O5] is itself equivalent to its
  integral-ideal case.

## Implementation notes

**What the converse needs, and why it is now available.** The dévissage file's implementation
notes say the converse would need `(Scheme.Modules.pushforward i).obj I.toSheafOfModules` to be
coherent, and name two facts as unavailable: "quasi-coherent of finite type on a locally
Noetherian scheme is coherent" and coherence of a pushforward along a closed immersion. Both are
proved in this library — the first as
`Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType`
([Stacks, Tag 01XZ]), the second as
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit`, which is
stated at exactly the type the integral-ideal case quantifies over. So the note is out of date
and the converse is a two-line consequence.

**Neither integrality nor the ideal nor properness of the closed immersion is used.** The
forward implication holds for an arbitrary closed immersion `i` into the source and an arbitrary
quasi-coherent submodule of `𝒪_Z`: the affine-base case is applied to the single coherent module
`i_* I`. The hypotheses `IsIntegral Z` of the integral-ideal statement are therefore slack in
this direction, which is what makes the resulting equivalence informative — the dévissage may
restrict to integral `Z` and to ideal sheaves at no cost.

**No tag is attached.** Every statement below either is an implication between two `Prop`s
neither of which is proved, or carries the irreducible dévissage of [Stacks, Tag 01YF] as a
hypothesis. [Stacks, Tag 02O5]'s labels name unconditional assertions, so none is earned here.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProperCoherentImage

attribute [local instance] HasDerivedCategory.standard

/-- **The affine-base case of [Stacks, Tag 02O5] is equivalent to its integral-ideal case.**
The forward implication is `higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase` and
the reverse is `higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`, the dévissage of
[Stacks, Tag 01YG].

The irreducible dévissage of [Stacks, Tag 01YF] for Noetherian schemes is carried as a
hypothesis, as it is there; it is used only in the reverse direction. -/
theorem higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y) :
    HigherDirectImageIsCoherentOverAffineBase.{u} ↔
      HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  ⟨higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase,
    higherDirectImageIsCoherentOverAffineBase_of_integralIdeals hirr⟩

/-- **The first assertion of [Stacks, Tag 02O5] is equivalent to its integral-ideal case.**
Composing `higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals` with the lossless
affine reduction `higherDirectImageIsCoherent_iff_overAffineBase`.

So the whole of [Stacks, Tag 02O5]'s first assertion — for every proper morphism to every locally
Noetherian scheme and every coherent module — is exactly as strong as the statement that
`R ᵖ f_* (i_* I)` is coherent for `f` proper over an *affine* locally Noetherian base, `i` a
closed immersion of an *integral* scheme and `I` a quasi-coherent *ideal* sheaf on it. That is
the statement at which the source's own proof applies Chow's lemma. -/
theorem higherDirectImageIsCoherent_iff_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y) :
    HigherDirectImageIsCoherent.{u} ↔ HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  higherDirectImageIsCoherent_iff_overAffineBase.trans
    (higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals hirr)

end AlgebraicGeometry.ProperCoherentImage

end
