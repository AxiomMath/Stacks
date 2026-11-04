module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of higher direct images in non-positive degrees, over `Scheme.{u}`

[Stacks, Tag 02O5] asserts that for a proper morphism `f : X ⟶ S` to a locally Noetherian
scheme and a coherent `𝒪_X`-module `F`, every higher direct image `R ⁱ f_* F` is coherent. That
statement is **not** proved here; see the implementation notes for what is still missing.

What is proved here are the two degenerate degrees, with no hypothesis on `f` or `F` beyond
coherence of `F`, and — the point of this file — at `Scheme.{u}` rather than `Scheme.{0}`:

* `R ⁱ f_* F` is coherent for `i < 0`, because it vanishes;
* `R ⁰ f_* F` is coherent if and only if `f_* F` is.

`StacksFrontier/AlgebraicGeometry/HigherDirectImageCoherent/Basic.lean` already proves both, but
only for `X S : Scheme.{0}`, and says in its implementation notes that the statement for
`Scheme.{u}` "cannot even be elaborated". It can:
`SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean` is declared for
`M : SheafOfModules.{u} R` over `X : Type u`, so `F.IsCoherent` for `F : X.Modules` with
`X : Scheme.{u}` elaborates, and the restriction to `Scheme.{0}` was never needed for the
mathematics. Since the statement of Tag 02O5 states both of its assertions over `Scheme.{u}`, the
universe-general forms are the ones its degenerate degrees reduce to.

## Main results

* `AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_of_neg`: `R ⁱ f_* F` is
  coherent for `i < 0`, over `Scheme.{u}`.
* `AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff`: `R ⁰ f_* F` is
  coherent if and only if `f_* F` is, over `Scheme.{u}`. This reduces the degree-`0` case of
  [Stacks, Tag 02O5]'s first assertion to its second.

## Implementation notes

Both proofs are now transports along the closure package of
`StacksFrontier/AlgebraicGeometry/CoherentAbelian/Basic.lean` rather than hand-built: coherence
of a zero sheaf of modules is `ObjectProperty.prop_of_isZero` against the `ContainsZero` and
`IsClosedUnderIsomorphisms` instances there, and invariance under isomorphism is
`ObjectProperty.prop_of_iso` against the same. Neither needs the bespoke `isCoherent_of_isZero`
and `isCoherent_of_iso` of the `Scheme.{0}` file, which are the `u = 0` cases of these.

What [Stacks, Tag 02O5] still needs, beyond this file, is the positive-degree content, and it is
blocked on two statements that nothing in the library proves:

* Tag 02O4's `higherDirectImage_isCoherent` — the same conclusion for a *locally projective*
  morphism to a locally Noetherian scheme. A proof belongs in a sibling of this directory. It is
  the substance of the source's argument, not a reduction step.
* Tag 01F6's `relativeLeraySpectralSequence` and `relativeLeraySpectralSequencePlus` —
  the relative Leray spectral sequence with its second-page identification and filtered
  abutment, which is what carries coherence along the factorisation of a proper morphism that
  Chow's lemma produces.

Both are stated but not yet proved in the library, so the gap between
this file and Tag 02O5 is those two declarations and the dévissage that joins them.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.CoherentAbelian

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- **Higher direct images are coherent in negative degrees**, for the trivial reason that they
vanish. No hypothesis on the morphism `f` nor on the module `F` is used.

This is the `Scheme.{u}` form of
`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_of_neg`, which
is stated only for `Scheme.{0}`. -/
theorem isCoherent_higherDirectImage_of_neg (p : ℤ) (hp : p < 0) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent :=
  ObjectProperty.prop_of_isZero
    (P := fun M : SheafOfModules.{u} S.ringCatSheaf => M.IsCoherent)
    (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F p hp)

/-- **Coherence of `R ⁰ f_* F` is coherence of `f_* F`.** The pushforward functor on sheaves of
modules over schemes is a right adjoint, hence left exact, so it agrees with its own zeroth
right derived functor; coherence then transports along that isomorphism.

This reduces the degree-`0` case of [Stacks, Tag 02O5]'s assertion about higher direct images to
its assertion about ordinary direct images, leaving the degrees `i > 0` as the genuinely
cohomological content. No hypothesis on `f` is used.

This is the `Scheme.{u}` form of
`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_zero_iff`,
which is stated only for `Scheme.{0}`. -/
theorem isCoherent_higherDirectImage_zero_iff :
    (((Scheme.Modules.pushforward f).rightDerivedPlus 0).obj F).IsCoherent ↔
      ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  ObjectProperty.prop_iff_of_iso
    (P := fun M : SheafOfModules.{u} S.ringCatSheaf => M.IsCoherent)
    (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso f F)

end AlgebraicGeometry.CoherentAbelian

end
