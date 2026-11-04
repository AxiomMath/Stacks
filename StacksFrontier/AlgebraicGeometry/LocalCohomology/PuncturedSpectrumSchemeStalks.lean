module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumReductionSteps

/-!
# The punctured spectrum of a local ring as a scheme

The induction of [Stacks, Tag 0BK1] applies its inductive hypothesis to the punctured spectrum
`P = Spec A ∖ {𝔪}` of a Noetherian local ring, regarded as a scheme in its own right. Its
inductive step, `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le`,
asks that this scheme be integral and Noetherian, and its hypothesis is a statement about the
local rings of that scheme at the points outside the open being pushed forward. This file
supplies both: the points of `P` are the primes of `A` other than the maximal ideal, and the
local ring of `P` at such a point is `A_𝔮`.

## Main results

* `Stacks.LocalCohomology.puncturedSpectrumStalkIso`: the local ring of the punctured spectrum of
  `A` at a point `𝔮` is `A_𝔮`.
* `Stacks.LocalCohomology.ringKrullDim_stalk_puncturedSpectrum_lt`: those local rings have
  strictly smaller Krull dimension than `A`, which is the measure the induction runs on.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum_stalk`: the
  coherence hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction` at `A_𝔮`, read at
  the stalk of the punctured spectrum.
* `Stacks.LocalCohomology.isNoetherian_puncturedSpectrum` and
  `Stacks.LocalCohomology.isIntegral_puncturedSpectrum`: the two scheme-level hypotheses of the
  inductive step.

## Implementation notes

Everything here is stated at the point `⟨𝔮, h𝔮⟩` of the punctured spectrum cut out by a prime
`𝔮` of `A` and a proof that it is not the closed point, rather than at an abstract point `z` of
that scheme. The reason is purely one of elaboration: `Localization.AtPrime (↑z).asIdeal`, the
spelling one would want in the statement, does not elaborate, because the `Ideal.IsPrime`
instance that `Localization.AtPrime` demands is not found for the ideal of a point reached
through the coercion `↥P → PrimeSpectrum A`, while it is found immediately for a prime named as
such. Applying the lemmas at an abstract `z` costs nothing: `⟨z.1, z.2⟩` and `z` are definitionally
equal by structure eta, so `puncturedSpectrumStalkIso z.1 z.2` has the stalk at `z` as its
domain.

The local ring at a point of the open subscheme is read in two steps:
`AlgebraicGeometry.Scheme.Opens.stalkIso` identifies it with the local ring of `Spec A` at the
same point, and `AlgebraicGeometry.Spec.stalkIso` identifies that with `A_𝔮`. The composite is a
`CommRingCat`-isomorphism, so everything downstream — the dimension, the Noetherian property, the
coherence hypothesis — travels along the underlying `RingEquiv`.

Noetherian-ness of the scheme is `IsLocallyNoetherian` (inherited by any open of `Spec A`)
together with `CompactSpace`, which holds because `Spec A` is a Noetherian space and therefore so
is every subspace of it. The Noetherian-space half is also stated, with the same one-line proof,
as `Stacks.Algebraization.noetherianSpace_puncturedSpectrum`; it is not reused here because the
file carrying it has an import closure of some 2660 modules, which is a poor trade for an
application of `TopologicalSpace.NoetherianSpace.set`.

Integrality needs `A` to be a domain and the punctured spectrum to be nonempty; both hold where
the induction uses it, since the ambient scheme of [Stacks, Tag 0BK1] is integral and the case of
an empty punctured spectrum is the case `dim A = 0`, which the induction disposes of separately.
`Nonempty` is therefore taken as a hypothesis rather than derived.

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-! ### Points and local rings -/

/-- A prime of a local ring other than the maximal ideal, read as a point of the punctured
spectrum. -/
def puncturedSpectrumPoint {A : Type u} [CommRing A] [IsLocalRing A] (q : PrimeSpectrum A)
    (hq : q ≠ closedPoint A) : (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  ⟨q, hq⟩

/-- A point of the punctured spectrum has an ideal other than the maximal ideal. -/
theorem asIdeal_ne_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A] {q : PrimeSpectrum A}
    (hq : q ≠ closedPoint A) : q.asIdeal ≠ maximalIdeal A :=
  fun h => hq (PrimeSpectrum.ext h)

/-- **The local ring of the punctured spectrum of `A` at a point `𝔮` is `A_𝔮`.** The punctured
spectrum is an open of `Spec A`, so its local ring at a point is the local ring of `Spec A`
there, which is the localization of `A` at the corresponding prime. -/
noncomputable def puncturedSpectrumStalkIso {A : Type u} [CommRing A] [IsLocalRing A]
    (q : PrimeSpectrum A) (hq : q ≠ closedPoint A) :
    (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.stalk
        (puncturedSpectrumPoint q hq) ≅
      CommRingCat.of (Localization.AtPrime q.asIdeal) :=
  (Stacks.Divisors.puncturedSpectrum A).stalkIso (puncturedSpectrumPoint q hq) ≪≫
    Spec.stalkIso (CommRingCat.of A) q

/-- **The local rings of the punctured spectrum of a Noetherian local ring `A` have strictly
smaller Krull dimension than `A`.** This is the measure on which the Noetherian induction of
[Stacks, Tag 0BK1] runs: passing from `Spec A` to its punctured spectrum drops the dimension of
every local ring, so the inductive hypothesis applies to the punctured spectrum.

The local ring at a point is `A_𝔮` by `puncturedSpectrumStalkIso`, the point is not the closed
point by `asIdeal_ne_maximalIdeal`, and `ringKrullDim_localization_atPrime_lt` is the drop. -/
theorem ringKrullDim_stalk_puncturedSpectrum_lt {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (q : PrimeSpectrum A) (hq : q ≠ closedPoint A) :
    ringKrullDim ((Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.stalk
      (puncturedSpectrumPoint q hq)) < ringKrullDim A := by
  rw [ringKrullDim_eq_of_ringEquiv (puncturedSpectrumStalkIso q hq).commRingCatIsoToRingEquiv]
  exact ringKrullDim_localization_atPrime_lt _ (asIdeal_ne_maximalIdeal hq)

/-- **The coherence hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction` at a point
of a punctured spectrum.** If the direct image of `𝒪` along the inclusion of the punctured
spectrum of `A_𝔮` is coherent, then the same holds for the local ring of the punctured spectrum
of `A` at `𝔮`, which is the spelling the inductive hypothesis consumes.

The two rings are isomorphic by `puncturedSpectrumStalkIso`, and
`isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv` transports coherence. -/
theorem isCoherent_pushforward_structureSheaf_puncturedSpectrum_stalk {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (q : PrimeSpectrum A) (hq : q ≠ closedPoint A)
    (h : ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime q.asIdeal)).ι).obj
      (SheafOfModules.unit.{u} (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime q.asIdeal)).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum
        ((Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.stalk
          (puncturedSpectrumPoint q hq))).ι).obj
      (SheafOfModules.unit.{u} (Stacks.Divisors.puncturedSpectrum
        ((Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.stalk
          (puncturedSpectrumPoint q hq))).toScheme.ringCatSheaf)).IsCoherent :=
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv
    (puncturedSpectrumStalkIso q hq).commRingCatIsoToRingEquiv.symm h

/-! ### The punctured spectrum is Noetherian and integral -/

/-- **The punctured spectrum of a Noetherian local ring is a Noetherian scheme.** It is an open
of `Spec A`, hence locally Noetherian, and quasi-compact because `Spec A` is a Noetherian
space. -/
theorem isNoetherian_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    AlgebraicGeometry.IsNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme := by
  have hns : NoetherianSpace (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    NoetherianSpace.set ((Stacks.Divisors.puncturedSpectrum A).1 : Set (PrimeSpectrum A))
  have : CompactSpace (Stacks.Divisors.puncturedSpectrum A).toScheme := inferInstance
  exact (AlgebraicGeometry.isNoetherian_iff _).2 ⟨inferInstance, inferInstance⟩

/-- **The punctured spectrum of a local domain is integral**, as soon as it is nonempty: it is
an open subscheme of the integral scheme `Spec A`. -/
theorem isIntegral_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [Nonempty (Stacks.Divisors.puncturedSpectrum A).toScheme] :
    IsIntegral (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  isIntegral_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι

end Stacks.LocalCohomology

end
