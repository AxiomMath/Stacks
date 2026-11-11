module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedBelowCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOverSheaf
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TorDimensionDirectImage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image of a relatively perfect complex along a proper flat morphism

Let `f : X ⟶ S` be a proper, flat morphism of finite presentation and let `E` be an `S`-perfect
object of `D(𝒪_X)` in the sense of Stacks 0DI0. [Stacks, Tag 0DJT] asserts that `Rf_*E` is a
perfect object of `D(𝒪_S)` and that its formation commutes with arbitrary base change.

The source proves perfectness by reducing to a Noetherian base — write an affine base as a
filtered colimit of Noetherian rings, descend `X` and `E` along it by [Stacks, Tag 0DI8], and
transfer back by base change — and then quotes [Stacks, Tag 08EV] over that Noetherian base.
This file is the Noetherian case: it discharges, from relative perfectness of `E` and properness
of `f`, every hypothesis [Stacks, Tag 08EV] makes of its source complex, and proves both halves
of the conclusion of [Stacks, Tag 08EV] for `Rf_*E`. The reduction to a Noetherian base and the
base change clause, that is the whole of [Stacks, Tag 0DJT], are
`isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap` in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange`.

## Main definitions

* `PushforwardTorDimensionResidue` is the Tor-dimension half of [Stacks, Tag 08EV], quantified
  over the source complex: `Rf_*K` is of locally finite Tor dimension for *every* `S`-perfect `K`.
  Over a Noetherian base it holds, by `pushforwardTorDimensionResidue_of_isGenuineTensorFamily`.

## Main results

* `isCoherent_homology_and_bounds_of_isPerfectRelativeTo`: what [Stacks, Tag 08EV] asks of its
  source complex, derived from relative perfectness — the cohomology sheaves of `E` are coherent
  and `E` is bounded.
* `isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo`: the pseudo-coherence half of
  the conclusion of [Stacks, Tag 08EV] for `Rf_*E`.
* `pushforwardTorDimensionResidue_of_isGenuineTensorFamily`: the Tor-dimension half of
  [Stacks, Tag 08EV] for every `S`-perfect object.
* `isPerfect_derivedPushforward_of_isPerfectRelativeTo`: `Rf_*E` is perfect over a Noetherian
  base, with no further hypothesis.

## How the hypotheses of [Stacks, Tag 08EV] are discharged

By [Stacks, Tag 08CQ] a perfect object of `D(𝒪_S)` is exactly a pseudo-coherent one of locally
finite Tor dimension, and the source's proof of [Stacks, Tag 08EV] establishes the two halves
separately. The pseudo-coherence half is
`Stacks.AlgebraicGeometry.ProperSupportCoherent`'s
`isPseudoCoherent_derivedPushforward_of_isProperOver_supp`, and the Tor-dimension half is
`AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver`.

`S` is Noetherian and `f` is of finite type and quasi-compact, so `X` is Noetherian. Relative
perfectness has pseudo-coherence of `E` as its first clause; the cohomology sheaves of a
pseudo-coherent object are quasi-coherent ([Stacks, Tag 08E5],
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`), and over a Noetherian scheme
they are coherent with a bound above by [Stacks, Tag 08E8]; and its Tor clause bounds the
cohomology of `E` below on the members of a covering, which quasi-compactness of `X` turns
into a global bound, by `AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo`. Finally `f` being
proper, *every* closed subset of `X` is proper over `S` — the reduced induced closed subscheme on
it maps to `X` by a closed immersion, which is proper, and a composition of proper morphisms is
proper — in particular the support of each cohomology sheaf. Coherence of higher direct images
over an affine base, [Stacks, Tag 02O5], is
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`.

The Tor-dimension half reads the Tor clause of relative perfectness at the genuine derived tensor
product (`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq`) as finite
Tor dimension over `f⁻¹𝒪_S`, which `X` being quasi-compact makes global.

## Implementation notes

`Rf_*` is `AlgebraicGeometry.derivedPushforwardModules`; pseudo-coherence is
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, the spelling of [Stacks, Tag 08CB] part (3)
that the pseudo-coherence half of [Stacks, Tag 08EV] concludes in; perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, the spelling of [Stacks, Tag 08CM] that
[Stacks, Tag 08CQ] is stated at. Relative perfectness is
`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo`, [Stacks, Tag 0DI0].

As everywhere in `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived
tensor product on the inverse-image ringed space is a family of certificates, one on each open
subspace, and it is pinned by the hypothesis `hD` that its underived tensor product is the
genuine `- ⊗_{f⁻¹𝒪_S} -` of Stacks 06YU. Without that pinning the Tor clause of relative
perfectness carries no information: at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` it holds for
every object.

Properness is Mathlib's `IsProper`, which extends `LocallyOfFiniteType` and gives `QuasiCompact`,
so neither a finite-type nor a quasi-compactness hypothesis is repeated; together with
`LocallyOfFinitePresentation` and the separatedness inside `IsProper` it is the source's "flat,
proper and of finite presentation". `IsNoetherian S` is [Stacks, Tag 01OV] part (2).

## References

* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

-- The imports needed for `pushforwardTorDimensionResidue_of_isGenuineTensorFamily` bring a second
-- abelian structure on sheaves of modules; the statements here are elaborated at
-- `SheafOfModules.instAbelian`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperSupportCoherent

universe u

namespace Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Certificates

variable [Flat f] [LocallyOfFinitePresentation f]

/-- The family of certificates for the derived tensor product on the inverse-image ringed space
`(X, f⁻¹𝒪_S)`, one on each open subspace, as part (3) of Stacks 08CG asks for. -/
abbrev TensorFamily : Type _ :=
  ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding)

/-- The pinning of a family of certificates: its underived tensor product is the genuine
`- ⊗_{f⁻¹𝒪_S} -` of Stacks 06YU on every open subspace. -/
abbrev IsGenuineTensorFamily (D : TensorFamily f) : Prop :=
  ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    (D U).tensor = Stacks.SheafOfModules.Tensor.sheafTensor
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding).sheaf

/-- **The Tor-dimension half of [Stacks, Tag 08EV], quantified over the source complex.** A
morphism `f` has this property when `Rf_*K` is of locally finite Tor dimension for *every*
`S`-perfect object `K` of `D(𝒪_X)`. For `f` proper, flat and locally of finite presentation over
a Noetherian base and `D` pinned to the genuine tensor product it holds:
`pushforwardTorDimensionResidue_of_isGenuineTensorFamily`. -/
def PushforwardTorDimensionResidue (D : TensorFamily f) : Prop :=
  ∀ K : DerivedCategory X.Modules, f.IsPerfectRelativeTo D K →
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforwardModules f).obj K)

end Certificates

section ProperSupport

/-- **Every closed subset of the source of a proper morphism is proper over the target.** The
reduced induced closed subscheme on it maps to `X` by a closed immersion, which is proper, and a
composition of proper morphisms is proper. -/
theorem isProperOver_of_isProper [IsProper f] (T : Closeds X) : IsProperOver f T := by
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
  infer_instance

end ProperSupport

section Hypotheses

variable [IsNoetherian S] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **What [Stacks, Tag 08EV] asks of its source complex, for an `S`-perfect complex.** Let `S` be
a Noetherian scheme, let `f : X ⟶ S` be proper, flat and locally of finite presentation and let
`E` be an `S`-perfect object of `D(𝒪_X)` whose cohomology sheaves are quasi-coherent. Then those
cohomology sheaves are coherent and `E` is bounded.

`X` is Noetherian, being quasi-compact and locally of finite type over a Noetherian scheme.
Coherence and the bound above are then [Stacks, Tag 08E8] applied to the pseudo-coherence clause
of relative perfectness, and the bound below comes from the Tor clause through
`AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo`. -/
theorem isCoherent_homology_and_bounds_of_isPerfectRelativeTo (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) :
    (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent) ∧
      ∃ a b : ℤ, E.IsGE a ∧ E.IsLE b := by
  have hXnoeth : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨⟨b, hb⟩, hcoh⟩ :=
    (AlgebraicGeometry.isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨E, hqc⟩).1 hE.1
  obtain ⟨a, hGE⟩ := AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo f D hD E hE
  exact ⟨hcoh, a, b, hGE, (DerivedCategory.isLE_iff E b).2 fun j hj => hb j hj⟩

/-- **The pseudo-coherence half of [Stacks, Tag 08EV] for `Rf_*E`.** Let `S` be a Noetherian
scheme, let `f : X ⟶ S` be proper, flat and locally of finite presentation and let `E` be an
`S`-perfect object of `D(𝒪_X)` with quasi-coherent cohomology sheaves. Then `Rf_*E` is a
pseudo-coherent object of `D(𝒪_S)`.

By [Stacks, Tag 08CQ] perfectness is pseudo-coherence together with locally finite Tor dimension;
this is the first of the two. Everything the pseudo-coherence half of [Stacks, Tag 08EV] asks of
`E` is supplied by `isCoherent_homology_and_bounds_of_isPerfectRelativeTo`, and its support
hypothesis by `isProperOver_of_isProper`. The hypothesis `haff` is the one that half takes for
[Stacks, Tag 02O5]. Both `hqc` and `haff` hold: `hqc` is [Stacks, Tag 08E5],
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`, and `haff` is
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`; they are
discharged in `isPerfect_derivedPushforward_of_isPerfectRelativeTo`. -/
theorem isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) := by
  obtain ⟨hcoh, a, b, hGE, hLE⟩ :=
    isCoherent_homology_and_bounds_of_isPerfectRelativeTo f D hD E hE hqc
  exact isPseudoCoherent_derivedPushforward_of_isProperOver_supp f E hcoh
    (fun _ => isProperOver_of_isProper f _) haff a b hGE hLE

/-- **The Tor-dimension half of [Stacks, Tag 08EV], for every `S`-perfect object.** Let `S` be a
Noetherian scheme and `f : X ⟶ S` proper, flat and locally of finite presentation. Then `Rf_*K`
is of locally finite Tor dimension for every `S`-perfect `K`.

`X` is quasi-compact, so the Tor clause of relative perfectness, read at the genuine derived
tensor product (`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq`),
is finite Tor dimension over `f⁻¹𝒪_S` (`locallyHasFiniteTorDimension_iff_hasFiniteTorDimension`
in `AlgebraicGeometry.AffineRelativeTorAmplitude`); the cohomology of `K` is quasi-coherent
([Stacks, Tag 08E5]) and supported on `X`, which is proper over `S`; so the Tor-dimension half of
[Stacks, Tag 08EV] applies, in the form
`AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver`. -/
@[sga "5 III 6.2" "partial"]
theorem pushforwardTorDimensionResidue_of_isGenuineTensorFamily (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) : PushforwardTorDimensionResidue f D := by
  intro K hK
  have hXnoeth : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hqc := AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K hK.1
  have : CompactSpace (RingedSpace.inverseImage S.toRingedSpace f.base).carrier :=
    inferInstanceAs (CompactSpace X)
  have htor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      ((Scheme.Hom.derivedScalarRestriction f).obj K) :=
    (AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
      _).1 ((RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq _ D (fun U => hD U) _).1
        hK.2)
  exact AlgebraicGeometry.locallyHasFiniteTorDimension_derivedPushforward_of_isProperOver f K hqc
    ⊤ (isProperOver_of_isProper f ⊤) (fun _ => by simp)
    ((AlgebraicGeometry.hasFiniteTorDimension_derivedScalarRestriction_iff f K).1 htor)

/-- **Perfectness of `Rf_*E` over a Noetherian base.** Let `S` be a Noetherian scheme, let
`f : X ⟶ S` be a proper, flat morphism of finite presentation and let `E` be an `S`-perfect
object of `D(𝒪_X)`. Then `Rf_*E` is a perfect object of `D(𝒪_S)`.

This is the converse implication of [Stacks, Tag 08CQ] applied to the two halves of
[Stacks, Tag 08EV]: pseudo-coherence, from
`isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo` with quasi-coherence of the
cohomology sheaves of `E` given by [Stacks, Tag 08E5] and [Stacks, Tag 02O5] by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, and locally
finite Tor dimension, from `pushforwardTorDimensionResidue_of_isGenuineTensorFamily`. It is the
Noetherian case to which the source reduces [Stacks, Tag 0DJT]; the tag itself, over an arbitrary
base and with its base change clause, is
`isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap`. -/
theorem isPerfect_derivedPushforward_of_isPerfectRelativeTo (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2
      (isPseudoCoherent_derivedPushforward_of_isPerfectRelativeTo f D hD E hE
        (AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X E hE.1)
        AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase))
    (pushforwardTorDimensionResidue_of_isGenuineTensorFamily f D hD E hE)

end Hypotheses

end Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

end
