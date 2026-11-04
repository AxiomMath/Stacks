module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOverSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TorDimensionDirectImage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image of a relatively perfect complex over a Noetherian base

Let `S` be a Noetherian scheme, `f : X ⟶ S` proper, flat and locally of finite presentation, and
`E` an `S`-perfect object of `D(𝒪_X)`. The perfectness clause of [Stacks, Tag 0DJT] over such a
base is `isPerfect_derivedPushforward_of_isPerfectRelativeTo`, which takes three inputs as
hypotheses: [Stacks, Tag 02O5] over an affine base, quasi-coherence of the cohomology sheaves of
`E`, and the Tor-dimension half of [Stacks, Tag 08EV] quantified over the source complex. This
file proves all three and states the clause with none of them.

## Main results

* `pushforwardTorDimensionResidue_of_isGenuine`: the Tor-dimension half of [Stacks, Tag 08EV] for
  every `S`-perfect object.
* `isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_isNoetherian`: the perfectness clause of
  [Stacks, Tag 0DJT] over a Noetherian base, with nothing granted.

## References

* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsNoetherian S] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

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
theorem pushforwardTorDimensionResidue_of_isGenuine (D : TensorFamily f)
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

/-- **The perfectness clause of [Stacks, Tag 0DJT] over a Noetherian base, with nothing granted.**
Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a proper, flat morphism locally of finite
presentation and let `E` be an `S`-perfect object of `D(𝒪_X)`. Then `Rf_*E` is a perfect object
of `D(𝒪_S)`.

This is `isPerfect_derivedPushforward_of_isPerfectRelativeTo` with its three inputs proved:
quasi-coherence of the cohomology sheaves of `E` is [Stacks, Tag 08E5] applied to the
pseudo-coherence clause of relative perfectness, [Stacks, Tag 02O5] over an affine base is
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, and the
Tor-dimension half of [Stacks, Tag 08EV] is `pushforwardTorDimensionResidue_of_isGenuine`. -/
@[sga "6 0 3.1" "special case",
  sga "6 0 4.1" "f proper, special case",
  sga "6 III 2.1" "Case Y = S",
  sga "6 III 2.2" "special case",
  sga "6 III 4.8" "clause (a), case Y = S",
  sga "6 IV 3.3.2" "3.3.2.3, special case",
  sga "6 XIV 2.2" "special case"]
theorem isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_isNoetherian (D : TensorFamily f)
    (hD : IsGenuineTensorFamily f D) (E : DerivedCategory X.Modules)
    (hE : f.IsPerfectRelativeTo D E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  isPerfect_derivedPushforward_of_isPerfectRelativeTo f D hD E hE
    (AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X E hE.1)
    AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase
    (pushforwardTorDimensionResidue_of_isGenuine f D hD)

end Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

end
