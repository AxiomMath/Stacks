module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType

/-!
# [Stacks, Tag 02O5] for a proper morphism with finite fibres

[Stacks, Tag 02O5] says that for a proper morphism `f : X ⟶ S` of locally Noetherian schemes
and a coherent `𝒪_X`-module `F`, every higher direct image `R ⁱ f_* F` is coherent. The tag is
not proved in this library; what is proved here is the tag, unconditionally and with no
hypothesis owed, for every proper morphism whose fibres are finite.

Three such classes are named, because the three hypotheses are the ones a caller actually has:
`f` affine, `f` locally quasi-finite, and `f` a monomorphism. Each of them makes a proper
morphism **finite** — respectively by [Stacks, Tag 01WM] together with [Stacks, Tag 01WG],
by [Stacks, Tag 02LS], and by [Stacks, Tag 04XV] — and
`Stacks.AlgebraicGeometry.PushforwardCoherent.isCoherent_higherDirectImage_of_isFinite` is
[Stacks, Tag 02O5] for a finite morphism.

## Main results

All four live in the namespace `AlgebraicGeometry.ProperCoherentImage`.

* `isCoherent_higherDirectImage_of_isProper_of_isAffineHom`: [Stacks, Tag 02O5] for a proper
  affine morphism.
* `isCoherent_higherDirectImage_of_isProper_of_locallyQuasiFinite`: [Stacks, Tag 02O5] for a
  proper locally quasi-finite morphism.
* `isCoherent_higherDirectImage_of_isProper_of_mono`: [Stacks, Tag 02O5] for a proper
  monomorphism.
* `isCoherent_pushforward_of_isProper_of_isAffineHom`: the tag's ordinary-direct-image assertion
  in the same case.

## Implementation notes

**Why quasi-coherence is not an extra hypothesis.** The coherence predicate used throughout, the
root `SheafOfModules.IsCoherent`, is [Stacks, Tag 01BV]'s: finite type with finite-type kernels,
with no quasi-coherence built in. The finite case
`Stacks.AlgebraicGeometry.PushforwardCoherent.isCoherent_higherDirectImage_of_isFinite` needs
quasi-coherence of `F` as well, and it is available rather than assumed: `X` is locally
Noetherian, because `f` is proper and hence locally of finite type over the locally Noetherian
`S`, and on a locally Noetherian scheme coherence is equivalent to quasi-coherence together with
finite type, which is [Stacks, Tag 01XZ]
(`Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isQuasicoherent_and_isFiniteType`).
So the statements below assume exactly what the source assumes.

**The degree is an arbitrary integer.** The source quantifies over `i ≥ 0`; the finite case is
proved for every `i : ℤ`, the negative degrees being the vanishing of a right derived functor
below zero, so that is the form kept here. Instantiating at `(i : ℤ)` for `i : ℕ` gives the
source's statement.

**These classes are not a proper subclass of the finite morphisms.** A proper morphism with
finite fibres *is* finite, so each statement below is the finite case of the tag in the
hypotheses the source would state it with, not a genuinely wider class. Nothing here reaches a
proper morphism with a positive-dimensional fibre; for that the library still needs Chow's lemma
and the projective case. The point of naming them is that `AlgebraicGeometry.IsFinite` is not
syntactically any of `IsProper ∧ IsAffineHom`, `IsProper ∧ LocallyQuasiFinite` or
`IsProper ∧ Mono`, so a caller holding one of those cannot otherwise use the finite case.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProperCoherentImage

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}}

/-- A coherent module on the source of a proper morphism to a locally Noetherian scheme is
quasi-coherent: the source is locally Noetherian, and there coherence is quasi-coherence
together with finite type ([Stacks, Tag 01XZ]). -/
theorem isQuasicoherent_of_isCoherent_of_isProper (f : X ⟶ S) [IsLocallyNoetherian S]
    [IsProper f] (F : X.Modules) (hF : F.IsCoherent) : F.IsQuasicoherent :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ((Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isQuasicoherent_and_isFiniteType
    F).mp hF).1

/-- **[Stacks, Tag 02O5] for a finite morphism, stated for a coherent module only.** This is
`Stacks.AlgebraicGeometry.PushforwardCoherent.isCoherent_higherDirectImage_of_isFinite` with its
quasi-coherence hypothesis discharged by `isQuasicoherent_of_isCoherent_of_isProper`, a finite
morphism being proper. It is the common core of the three cases below. -/
theorem isCoherent_higherDirectImage_of_isFinite (f : X ⟶ S) [IsLocallyNoetherian S] [IsFinite f]
    (F : X.Modules) (hF : F.IsCoherent) (i : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).IsCoherent :=
  have : IsProper f := inferInstance
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent_of_isProper f F hF
  Stacks.AlgebraicGeometry.PushforwardCoherent.isCoherent_higherDirectImage_of_isFinite f F hF i

/-- **[Stacks, Tag 02O5] for a proper affine morphism.** A proper affine morphism is finite: it
is universally closed and affine, hence integral by [Stacks, Tag 01WM]
(`AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom`), and it is locally of
finite type, so it is finite by [Stacks, Tag 01WG]
(`AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`). -/
theorem isCoherent_higherDirectImage_of_isProper_of_isAffineHom (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] [IsAffineHom f] (F : X.Modules) (hF : F.IsCoherent)
    (i : ℤ) : (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).IsCoherent :=
  have : IsIntegralHom f := IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  have : IsFinite f := (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨inferInstance, inferInstance⟩
  isCoherent_higherDirectImage_of_isFinite f F hF i

/-- **[Stacks, Tag 02O5] for a proper locally quasi-finite morphism.** Such a morphism is finite
by Zariski's main theorem, [Stacks, Tag 02LS]
(`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`). -/
theorem isCoherent_higherDirectImage_of_isProper_of_locallyQuasiFinite (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] [LocallyQuasiFinite f] (F : X.Modules)
    (hF : F.IsCoherent) (i : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).IsCoherent :=
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  isCoherent_higherDirectImage_of_isFinite f F hF i

/-- **[Stacks, Tag 02O5] for a proper monomorphism.** A proper monomorphism is a closed
immersion by [Stacks, Tag 04XV] (`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`),
and a closed immersion is finite. -/
theorem isCoherent_higherDirectImage_of_isProper_of_mono (f : X ⟶ S) [IsLocallyNoetherian S]
    [IsProper f] [Mono f] (F : X.Modules) (hF : F.IsCoherent) (i : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).IsCoherent :=
  have : IsClosedImmersion f := (IsClosedImmersion.iff_isProper_and_mono f).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsFinite f := inferInstance
  isCoherent_higherDirectImage_of_isFinite f F hF i

/-- **The ordinary-direct-image assertion of [Stacks, Tag 02O5] for a proper affine morphism.**
Coherence of `f_* F` is coherence of the degree-zero higher direct image, transported along
`AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff`. -/
theorem isCoherent_pushforward_of_isProper_of_isAffineHom (f : X ⟶ S) [IsLocallyNoetherian S]
    [IsProper f] [IsAffineHom f] (F : X.Modules) (hF : F.IsCoherent) :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  (CoherentAbelian.isCoherent_higherDirectImage_zero_iff f F).mp
    (isCoherent_higherDirectImage_of_isProper_of_isAffineHom f F hF 0)

end AlgebraicGeometry.ProperCoherentImage

end
