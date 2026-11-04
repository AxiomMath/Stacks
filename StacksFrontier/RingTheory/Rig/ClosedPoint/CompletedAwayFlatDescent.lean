module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import StacksFrontier.RingTheory.Rig.ClosedPoint.Regular
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.Flat
public import
  StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.RestrictedPowerSeriesAway

/-!
# Descent of flatness at a prime along a completed principal localization

Let

```
S  ⟶  S'
↑      ↑
R  ⟶  R'
```

be a commuting square of commutative rings whose horizontal arrows are flat, and let `q` be a
prime of `S'` lying over the prime `p = q ∩ S`.  If `S'_q` is flat over `R'`, then `S_p` is flat
over `R`.  The file specializes this to squares whose horizontal arrows are completed principal
localizations of Noetherian rings.

## Main results

* `Rig.flat_atPrime_of_flat_square`: the descent of flatness at a prime across a square with
  flat horizontal arrows.
* `Rig.flat_algebraMap_completedAway`: the completed principal localization of a Noetherian ring
  is flat over it.
* `Rig.flat_atPrime_of_flat_atPrime_comap`, `Rig.flat_atPrime_of_flat_atPrime_extendedIdeal`:
  flatness at a prime descends across the completed principal localizations of a square.
* `Rig.exists_flat_atPrime_reduction_completedAway`: for a rig-closed prime `q` of `B` there is
  `f : A` whose completed principal localizations carry rig-closed primes over `q`, flatness at
  which gives flatness of `B_q` over `A`.
* `Rig.flat_restrictedPowerSeriesMap_completedAway`: `A_{\{f\}}\{σ\}` is flat over `A\{σ\}`.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 039V](https://stacks.math.columbia.edu/tag/039V)
-/

@[expose] public section

namespace Rig

universe u

/-- **Descent of flatness at a prime across a square with flat horizontal arrows.**  For a
commuting square `β ∘ φ = φ' ∘ α` with `α` and `β` flat, a prime `q` of `S'` and the prime
`p = q ∩ S` it contracts to, flatness of `S'_q` over `R'` implies flatness of `S_p` over `R`. -/
public theorem flat_atPrime_of_flat_square
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (α : R →+* R') (β : S →+* S') (φ' : R' →+* S')
    (hsq : β.comp φ = φ'.comp α)
    (q : Ideal S') [q.IsPrime] (p : Ideal S) [p.IsPrime] (hp : p = q.comap β)
    (hα : _root_.RingHom.Flat α) (hβ : _root_.RingHom.Flat β)
    (hφ' : _root_.RingHom.Flat ((algebraMap S' (Localization.AtPrime q)).comp φ')) :
    _root_.RingHom.Flat ((algebraMap S (Localization.AtPrime p)).comp φ) := by
  let Sp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let ψ : Sp →+* Sq := Localization.localRingHom p q β hp
  have hSSq : _root_.RingHom.Flat ((algebraMap S' Sq).comp β) :=
    hβ.comp (_root_.RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Sq q.primeCompl))
  have hroute : ψ.comp ((algebraMap S Sp).comp φ) = ((algebraMap S' Sq).comp φ').comp α :=
    RingHom.ext fun x ↦ (Localization.localRingHom_to_map p q β hp (φ x)).trans
      (congrArg (algebraMap S' Sq) (RingHom.congr_fun hsq x))
  have hroute' : ψ.comp (algebraMap S Sp) = (algebraMap S' Sq).comp β :=
    RingHom.ext fun x ↦ Localization.localRingHom_to_map p q β hp x
  algebraize_only [ψ, (algebraMap S Sp).comp φ, (algebraMap S' Sq).comp β,
    ((algebraMap S' Sq).comp φ').comp α]
  have : IsScalarTower S Sp Sq := IsScalarTower.of_algebraMap_eq' hroute'.symm
  have hflatSp : Module.Flat Sp Sq :=
    (Module.flat_iff_of_isLocalization Sp p.primeCompl Sq).mpr hSSq
  have : IsLocalHom (algebraMap Sp Sq) := Localization.isLocalHom_localRingHom p q β hp
  have : Module.FaithfullyFlat Sp Sq := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsScalarTower R Sp Sq := IsScalarTower.of_algebraMap_eq' hroute.symm
  have : Module.Flat R Sq := hα.comp hφ'
  exact Stacks.Flatness.NilpotentFibreCriterion.flat_of_flat_of_faithfullyFlat Sq

/-- **A completed principal localization of a Noetherian ring is flat over it.**  The completion
of `A[1/f]` along the extension of `I` is flat over `A`. -/
public theorem flat_algebraMap_completedAway {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (f : A) :
    _root_.RingHom.Flat (algebraMap A (CompletedAway I f)) := by
  let A_f := Localization.Away f
  let I_f : Ideal A_f := I.map (algebraMap A A_f)
  have := (_root_.RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat A_f (Submonoid.powers f))).comp
    (_root_.RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian I_f))
  rwa [← IsScalarTower.algebraMap_eq A A_f (AdicCompletion I_f A_f)] at this

/-- **Flatness at a prime descends across the completed principal localizations of a square.**
Let `φ : A → B`, let `K` be any ideal and `g` any element of `B`, and let
`ψ : A_{\{f\}} → B_{\{g\}}` be any ring homomorphism commuting with the two structure maps.  If
`q'` is a prime of `B_{\{g\}}` contracting to a prime `q` of `B`, then flatness of
`(B_{\{g\}})_{q'}` over `A_{\{f\}}` gives flatness of `B_q` over `A`. -/
public theorem flat_atPrime_of_flat_atPrime_comap {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (I : Ideal A) (f : A) (K : Ideal B) (g : B)
    (ψ : CompletedAway I f →+* CompletedAway K g)
    (hcomm : ψ.comp (algebraMap A (CompletedAway I f)) =
      (algebraMap B (CompletedAway K g)).comp φ)
    (q : Ideal B) [q.IsPrime] (q' : Ideal (CompletedAway K g)) [q'.IsPrime]
    (hq : q = q'.comap (algebraMap B (CompletedAway K g)))
    (hflat : _root_.RingHom.Flat
      ((algebraMap (CompletedAway K g) (Localization.AtPrime q')).comp ψ)) :
    _root_.RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp φ) :=
  flat_atPrime_of_flat_square φ (algebraMap A (CompletedAway I f))
    (algebraMap B (CompletedAway K g)) ψ hcomm.symm q' q hq
    (flat_algebraMap_completedAway I f) (flat_algebraMap_completedAway K g) hflat

/-- **Flatness at a prime descends from a completed principal localization.**  Let `φ : A → B`,
let `q` be a prime of `B` and let `f : A` be an element whose image is a unit modulo `q`.  Write
`q'` for the extension of `q` to the completed principal localization `B_{\{φ f\}}` and
`ψ : A_{\{f\}} → B_{\{φ f\}}` for the induced map.  If `(B_{\{φ f\}})_{q'}` is flat over
`A_{\{f\}}`, then `B_q` is flat over `A`. -/
public theorem flat_atPrime_of_flat_atPrime_extendedIdeal {A B : Type u} [CommRing A]
    [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (I : Ideal A) (f : A) [IsAdicComplete (I.map φ) B]
    (q : Ideal B) [q.IsPrime] (hunit : IsUnit (Ideal.Quotient.mk q (φ f)))
    (hcomm : (RingHom.completedAwayMap φ I f).comp (algebraMap A (CompletedAway I f)) =
      (algebraMap B (CompletedAway (I.map φ) (φ f))).comp φ)
    (hq' : (extendedIdeal (I.map φ) q (φ f)).IsPrime)
    (hflat :
      letI : (extendedIdeal (I.map φ) q (φ f)).IsPrime := hq'
      _root_.RingHom.Flat
        ((algebraMap (CompletedAway (I.map φ) (φ f))
          (Localization.AtPrime (extendedIdeal (I.map φ) q (φ f)))).comp
            (RingHom.completedAwayMap φ I f))) :
    _root_.RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp φ) := by
  have : (extendedIdeal (I.map φ) q (φ f)).IsPrime := hq'
  exact flat_atPrime_of_flat_atPrime_comap φ I f (I.map φ) (φ f) (RingHom.completedAwayMap φ I f)
    hcomm q (extendedIdeal (I.map φ) q (φ f))
    (comap_extendedIdeal_eq (I.map φ) q (φ f) hunit).symm hflat

/-- **Reduction of flatness at a rig-closed prime to a completed principal localization, for a
given ideal of definition.**  The statement of `Rig.exists_flat_atPrime_reduction_completedAway`
for an ideal of definition `I` of `A` whose extension defines the topology of `B`. -/
public theorem exists_flat_atPrime_reduction_completedAway_of_isAdic {A B : Type u} [CommRing A]
    [CommRing B] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (I : Ideal A) (hIadic : _root_.IsAdic I)
    (hJadic : _root_.IsAdic (I.map φ))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (topologicalNilradical B) q) :
    let J := I.map φ
    ∃ f : A,
      let A_f := CompletedAway I f
      let B_f := CompletedAway J (φ f)
      let ψ : A_f →+* B_f := RingHom.completedAwayMap φ I f
      let I_f := I.map (algebraMap A (Localization.Away f))
      let J_f := J.map (algebraMap B (Localization.Away (φ f)))
      let I_hat := I_f.map (algebraMap (Localization.Away f) A_f)
      let J_hat := J_f.map (algebraMap (Localization.Away (φ f)) B_f)
      let q' := extendedIdeal J q (φ f)
      let p' := q'.comap ψ
      ∃ hqprime : q'.IsPrime,
        letI : q'.IsPrime := hqprime
        ∃ hpprime : p'.IsPrime,
          letI : p'.IsPrime := hpprime
          Ideal.IsClosedPointAwayFrom J_hat q' ∧
            Ideal.IsClosedPointAwayFrom I_hat p' ∧
            (_root_.RingHom.Flat ((algebraMap B_f (Localization.AtPrime q')).comp ψ) →
              _root_.RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp φ)) := by
  obtain ⟨f, hunit, hcomm, hqprime, hpprime, hJq', hIp'⟩ :=
    exists_isClosedPointAwayFrom_completedAway_comap_of_isAdic hA hB φ hφ I hIadic hJadic
      hft q hq
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : IsAdicComplete (I.map φ) B := (IsAdic.isAdicComplete_iff hJadic).2 ⟨hB.2.1, hB.2.2⟩
  exact ⟨f, hqprime, hpprime, hJq', hIp',
    flat_atPrime_of_flat_atPrime_extendedIdeal φ I f q hunit hcomm hqprime⟩

/-- **Reduction of flatness at a rig-closed prime to a completed principal localization.**  For
an adic, continuous homomorphism `φ : A → B` of topologically finite type between Noetherian
weakly admissible rings and a rig-closed prime `q` of `B`, there is an `f : A` such that the
prime `q'` above `q` of the completed principal localization `B_{\{φ f\}}` and the prime `p'` it
cuts out on `A_{\{f\}}` are rig-closed, and flatness of `(B_{\{φ f\}})_{q'}` over `A_{\{f\}}`
implies flatness of `B_q` over `A`. -/
public theorem exists_flat_atPrime_reduction_completedAway {A B : Type u} [CommRing A]
    [CommRing B] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ) (hadic : _root_.RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom (topologicalNilradical B) q) :
    let I := hadic.choose
    let J := I.map φ
    ∃ f : A,
      let A_f := CompletedAway I f
      let B_f := CompletedAway J (φ f)
      let ψ : A_f →+* B_f := RingHom.completedAwayMap φ I f
      let I_f := I.map (algebraMap A (Localization.Away f))
      let J_f := J.map (algebraMap B (Localization.Away (φ f)))
      let I_hat := I_f.map (algebraMap (Localization.Away f) A_f)
      let J_hat := J_f.map (algebraMap (Localization.Away (φ f)) B_f)
      let q' := extendedIdeal J q (φ f)
      let p' := q'.comap ψ
      ∃ hqprime : q'.IsPrime,
        letI : q'.IsPrime := hqprime
        ∃ hpprime : p'.IsPrime,
          letI : p'.IsPrime := hpprime
          Ideal.IsClosedPointAwayFrom J_hat q' ∧
            Ideal.IsClosedPointAwayFrom I_hat p' ∧
            (_root_.RingHom.Flat ((algebraMap B_f (Localization.AtPrime q')).comp ψ) →
              _root_.RingHom.Flat ((algebraMap B (Localization.AtPrime q)).comp φ)) :=
  exists_flat_atPrime_reduction_completedAway_of_isAdic hA hB φ hφ hadic.choose
    hadic.choose_spec.1 hadic.choose_spec.2 hft q hq

/-- **`A_{\{f\}}\{σ\}` is flat over `A\{σ\}`.**  The coefficientwise map from the restricted
power series ring over `A` to the one over the completed principal localization of `A` at `f` is
flat. -/
public theorem flat_restrictedPowerSeriesMap_completedAway {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (σ : Type u) [Finite σ] (f : A) :
    _root_.RingHom.Flat
      ((TopologicalRing.restrictedPowerSeriesMap
          (B := AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f))
          (I.map (algebraMap A (Localization.Away f))) σ).comp
        (TopologicalRing.restrictedPowerSeriesMap (B := Localization.Away f) I σ)) := by
  have : IsNoetherianRing (RestrictedPowerSeries I σ) := isNoetherianRing_restrictedPowerSeries I σ
  have hstruct : _root_.RingHom.Flat
      (algebraMap (RestrictedPowerSeries I σ)
        (AdicCompletion (TopologicalRing.awayCoefficientIdeal I σ f)
          (Localization.Away (RestrictedPowerSeries.coefficientRingHom I σ f)))) :=
    flat_algebraMap_completedAway (RestrictedPowerSeries.coefficientIdeal I σ)
      (RestrictedPowerSeries.coefficientRingHom I σ f)
  have := hstruct.comp (_root_.RingHom.Flat.of_bijective
    (TopologicalRing.bijective_restrictedPowerSeriesMap_comp_completedAway I
      (Ideal.fg_of_isNoetherianRing I) σ f))
  rwa [TopologicalRing.restrictedPowerSeriesMap_comp_completedAway_comp_algebraMap I
    (Ideal.fg_of_isNoetherianRing I) σ f] at this

end Rig

end
