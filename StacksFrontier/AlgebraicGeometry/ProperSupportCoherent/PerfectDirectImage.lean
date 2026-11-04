module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Producing perfect complexes out of a derived direct image

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let `E` be an
object of `D^b_Coh(𝒪_X)` whose cohomology sheaves have support proper over `S`. Then `Rf_*E` is
pseudo-coherent, and it is a perfect object of `D(𝒪_S)` as soon as it is locally of finite Tor
dimension.

## Main results

* `isPseudoCoherent_of_derivedCategoryBBounded_isCoherent`: an object of `D^b_Coh(𝒪_S)` on a
  Noetherian scheme is pseudo-coherent.
* `isPseudoCoherent_derivedPushforward_of_isProperOver_supp`: the pseudo-coherence half of
  [Stacks, Tag 08EV].
* `isPseudoCoherent_derivedPushforward_of_isAffineHom`: the same for an affine `f`, where the
  appeal to [Stacks, Tag 02O5] is discharged.
* `isPerfect_derivedPushforward_of_locallyHasFiniteTorDimension`: `Rf_*E` is perfect once it is
  locally of finite Tor dimension.

## Implementation notes

**Only part of [Stacks, Tag 08EV] is proved here.** By [Stacks, Tag 08CQ] a perfect object of
`D(𝒪_S)` is exactly a pseudo-coherent one of locally finite Tor dimension, and the source's
proof establishes the two halves separately. The pseudo-coherence half is what is proved below:
[Stacks, Tag 08E2] puts `Rf_*E` in `D^b_Coh(𝒪_S)` and [Stacks, Tag 08E8] identifies the
pseudo-coherent objects of `D_QCoh(𝒪_S)` on a Noetherian scheme with `D⁻_Coh(𝒪_S)`, which
contains it. The Tor-dimension half is **not** proved: `Rf_*E` is not asserted anywhere here to
be of locally finite Tor dimension, and the conclusion `Rf_*E` is perfect is reached only from
that statement as an explicit hypothesis, in
`isPerfect_derivedPushforward_of_locallyHasFiniteTorDimension`.

What the missing half needs, and why none of it is available. The source tensors `Rf_*E` with an
arbitrary quasi-coherent `𝒪_S`-module `ℱ`, rewrites
`Rf_*E ⊗^𝐋_{𝒪_S} ℱ = Rf_*(E ⊗^𝐋_{f^{-1}𝒪_S} f^{-1}ℱ)` by [Stacks, Tag 08EU] and
[Stacks, Tag 08DE], bounds the cohomology of the right-hand side using the finite Tor dimension
of `E` over `f^{-1}𝒪_S`, and converts the resulting vanishing on quasi-coherent test modules
into genuine Tor amplitude by [Stacks, Tag 08EA]. Of those three steps:

* [Stacks, Tag 08EA] is in the tree only as its clause `(1) implies (2)`, which is the direction
  that is not needed; the direction the proof uses, `(2) implies (1)`, is not formalized, and
  `StacksFrontier/AlgebraicGeometry/Perfect/TorAmplitudeQuasiCoherentTests.lean` records what it
  lacks — the essential surjectivity of `QCoh(𝒪_S) → QCoh(𝒪_U)` for `U` an open of a
  quasi-separated scheme. The transport of Tor amplitude along an isomorphism of ringed spaces
  that that file also recorded as missing is in fact available, as
  `Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_iff`.
* [Stacks, Tag 08EU] is in the tree only at `K = 𝒪_S[0]`, and even there with the unitors of the
  two derived tensor products and the right-unitor coherence of the [Stacks, Tag 079U]
  comparison as explicit hypotheses; the dévissage to a general `K` in `D_QCoh(𝒪_S)` is absent,
  so the projection formula is unavailable at the `ℱ` the proof needs.

Accordingly the Tor-dimension half is beyond what the tree supports, and the bare label is not
attached.

`Rf_*` is `AlgebraicGeometry.derivedPushforwardModules`, and pseudo-coherence is
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, the spelling of [Stacks, Tag 08CB] part (3)
that [Stacks, Tag 08E8] concludes in. Perfectness is `Stacks.Cohomology.PerfectComplexes.IsPerfect`,
the spelling of [Stacks, Tag 08CM] that [Stacks, Tag 08CQ] is stated at; the two spellings of
pseudo-coherence on a ringed space are bridged by
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'`.

The hypothesis `haff` is inherited verbatim from [Stacks, Tag 08E2]: it is
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, the named
`Prop` this library carries for [Stacks, Tag 02O5]. For an affine `f` it is discharged, which is
why the affine variant below carries nothing.

## References

* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **An object of `D^b_Coh(𝒪_S)` on a Noetherian scheme is pseudo-coherent.** Coherent modules
are quasi-coherent by [Stacks, Tag 01BW], so the object lies in `D_QCoh(𝒪_S)`; it is bounded
above and all of its cohomology sheaves are coherent, which is the right-hand side of
[Stacks, Tag 08E8]. -/
theorem isPseudoCoherent_of_derivedCategoryBBounded_isCoherent (S : Scheme.{u}) [IsNoetherian S]
    (K : DerivedCategory S.Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent) K) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) K := by
  have hqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor S.Modules n).obj K).IsQuasicoherent := by
    intro n
    have := hK.2 n
    exact isQuasicoherent_of_isCoherent _
  exact (AlgebraicGeometry.isPseudoCoherent_iff_boundedAbove_coherent_homology S
    ⟨K, hqc⟩).2 ⟨hK.1.2, hK.2⟩

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 08EV], the pseudo-coherence half of the conclusion.** Let `S` be a Noetherian
scheme, `f : X ⟶ S` locally of finite type and `E` a bounded object of `D(𝒪_X)` whose cohomology
sheaves are coherent with support proper over `S`. Then `Rf_*E` is a pseudo-coherent object of
`D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor
dimension; this is the first of the two, obtained from [Stacks, Tag 08E2] and
[Stacks, Tag 08E8]. The hypothesis `haff` is the one [Stacks, Tag 08E2] carries for
[Stacks, Tag 02O5]; without it this half is registered at
`isPseudoCoherent_derivedPushforward_of_isProperOver_supp_unconditional`. -/
theorem isPseudoCoherent_derivedPushforward_of_isProperOver_supp [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPseudoCoherent_of_derivedCategoryBBounded_isCoherent S _
    (derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp f E hcoh hsupp haff a b
      hGE hLE)

/-- **The pseudo-coherence half of [Stacks, Tag 08EV] for an affine `f`**, unconditionally. The
appeal to [Stacks, Tag 02O5] is discharged for an affine morphism, the closed subscheme behind
the reduction of [Stacks, Tag 08DS] being proper and affine over `S`, hence finite over it.

`IsAffineHom f` is a hypothesis the source does not make, so this is a special case of a clause
of the tag rather than a clause of it, and its label is not attached. -/
theorem isPseudoCoherent_derivedPushforward_of_isAffineHom [IsNoetherian S]
    [LocallyOfFiniteType f] [IsAffineHom f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPseudoCoherent_of_derivedCategoryBBounded_isCoherent S _
    (derivedCategoryBBounded_derivedPushforward_of_isAffineHom f E hcoh hsupp a b hGE hLE)

/-- **What is left of [Stacks, Tag 08EV] once the Tor-dimension half is granted.** With the
hypotheses of the tag, if `Rf_*E` is locally of finite Tor dimension then it is a perfect object
of `D(𝒪_S)`.

This is the converse implication of [Stacks, Tag 08CQ] applied to the pseudo-coherence proved
above. The hypothesis `htor` is exactly the half of the source's proof that the tree cannot yet
carry out, so no label is attached: the tag asserts perfectness unconditionally. -/
theorem isPerfect_derivedPushforward_of_locallyHasFiniteTorDimension [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b)
    (htor : Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforwardModules f).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2
      (isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh hsupp haff a b hGE hLE))
    htor

end DerivedPushforward

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
