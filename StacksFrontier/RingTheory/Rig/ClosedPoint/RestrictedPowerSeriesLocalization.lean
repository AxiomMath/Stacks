module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.ClosedPoint.CompletedAwayCoefficient
public import StacksFrontier.RingTheory.Rig.ClosedPoint.CompletedTensorProductFlat

/-!
# Flatness of `A{σ} → B{σ}` at a rig-closed point, from rig-closedness upstairs alone

The fifth paragraph of the proof of Stacks 0GGR establishes flatness of `A{σ} → B{σ}` at a
rig-closed prime `q` of `B{σ}` *under the extra assumption that the contraction `q ∩ A` is
rig-closed as well*; that is `Rig.flat_atPrime_restrictedPowerSeriesMap_of_isNaivelyRigFlat`,
which asks for rig-closedness of all four primes in the square.  Two of those four are free:
`Rig.isClosedPointAwayFrom_comap_restrictedPowerSeries` derives rig-closedness of `q ∩ B` and
of `q ∩ A{σ}` from rig-closedness of `q` and of `q ∩ A`.  This module records the resulting
two-hypothesis form.

What the fourth paragraph of that proof then contributes is the removal of the remaining
hypothesis on `q ∩ A`: one replaces `A` by a completed principal localization `A_{\{f\}}` at an
element `f` supplied by Stacks 0GGG, chosen so that the induced prime of `A_{\{f\}}` *is*
rig-closed, and descends flatness back along the resulting square.  The pieces of that descent
are `Rig.exists_flat_atPrime_reduction_completedAway_of_isAdic`,
`Rig.restrictedPowerSeriesCompletedAwayEquiv_comp_completedAwayMap`,
`Rig.isClosedPointAwayFrom_comap_of_bijective` and `RestrictedPowerSeries.congrEquiv`.

## Main results

* `Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint_of_comap`: flatness of
  `A{σ} → B{σ}` at a rig-closed prime whose contraction to `A` is rig-closed, with the two
  intermediate rig-closedness hypotheses discharged.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
-/

@[expose] public section

namespace Rig

section

universe u

open RestrictedPowerSeries TopologicalRing

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Flatness of `A{σ} → B{σ}` at a rig-closed prime whose contraction to `A` is
rig-closed.**  The fifth paragraph of the proof of Stacks 0GGR, with the rig-closedness of the
two intermediate primes `q ∩ B` and `q ∩ A{σ}` discharged by
`Rig.isClosedPointAwayFrom_comap_restrictedPowerSeries` instead of assumed.

The hypothesis on `q ∩ A` is what the fourth paragraph of that proof removes, by replacing `A`
with a completed principal localization. -/
public theorem flat_atPrime_restrictedPowerSeriesMap_of_rigPoint_of_comap
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hadic : _root_.RingHom.IsAdic (algebraMap A B))
    (hflat : RingHom.IsNaivelyRigFlat (algebraMap A B))
    (q : Ideal (RestrictedPowerSeries (I.map (algebraMap A B)) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      ((I.map (algebraMap A B)).map (coefficientRingHom (I.map (algebraMap A B)) σ)) q)
    (hpA : Ideal.IsClosedPointAwayFrom I
      ((q.comap (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)).comap
        (coefficientRingHom I σ))) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (Localization.AtPrime q)).comp
          (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ)) := by
  obtain ⟨hqB, hp⟩ :=
    isClosedPointAwayFrom_comap_restrictedPowerSeries I hI hJ σ hcont hft q hq hpA
  exact flat_atPrime_restrictedPowerSeriesMap_of_isNaivelyRigFlat I hI hJ σ hcont hA hB hadic
    hflat q hq hqB hp hpA

end

/-! ### `WAdm^Noeth` structure of a restricted power series ring

These three facts were re-derived inline wherever they were wanted, and against the non-instance
`RestrictedPowerSeries.adicTopology` rather than the default inverse-limit topology.  They are
stated here once, for the default instance, which `RestrictedPowerSeries.isAdic_coefficientIdeal`
identifies with the adic topology of the coefficient ideal whenever `I` is finitely generated.
-/

section Structure

universe u

open RestrictedPowerSeries TopologicalRing

variable {A : Type u} [CommRing A]

/-- **A restricted power series ring over a Noetherian ring is weakly admissible.**  It is
adically complete for its coefficient ideal, which defines its topology, so
`Rig.isWeaklyAdmissible_of_isAdicComplete` applies. -/
public theorem isWeaklyAdmissible_restrictedPowerSeries [IsNoetherianRing A] (I : Ideal A)
    (hI : I.FG) (σ : Type*) [Finite σ] :
    letI : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
      isLinearTopology_restrictedPowerSeries I hI σ
    TopologicalRing.IsWeaklyAdmissible (RestrictedPowerSeries I σ) := by
  let : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    isLinearTopology_restrictedPowerSeries I hI σ
  let : IsAdicComplete (coefficientIdeal I σ) (RestrictedPowerSeries I σ) :=
    isAdicComplete_restrictedPowerSeries I σ
  have hadic : _root_.IsAdic (coefficientIdeal I σ) := isAdic_coefficientIdeal I hI σ
  exact isWeaklyAdmissible_of_isAdicComplete (coefficientIdeal I σ) hadic
    ((isIdealOfDefinition_iff_isAdic ⟨_, hadic⟩ _).2 hadic)

/-- **The coefficient inclusion `A → A{σ}` is continuous.**  It is adic: the coefficient ideal
is by definition the extension of `I`, and defines the topology of `A{σ}`. -/
public theorem continuous_coefficientRingHom [TopologicalSpace A] [IsTopologicalRing A]
    (I : Ideal A) (hIadic : _root_.IsAdic I) (hI : I.FG) (σ : Type*) :
    Continuous (coefficientRingHom I σ) :=
  RingHom.continuous_of_isAdic _ ⟨I, hIadic, isAdic_coefficientIdeal I hI σ⟩

/-- **The induced map `A{σ} → B{σ}` is continuous.**  It is adic, by
`TopologicalRing.isAdic_restrictedPowerSeriesMap`. -/
public theorem continuous_restrictedPowerSeriesMap {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (σ : Type u) :
    Continuous (TopologicalRing.restrictedPowerSeriesMap (B := B) I σ) :=
  RingHom.continuous_of_isAdic _ (isAdic_restrictedPowerSeriesMap I hI σ)

end Structure

/-! ### The same, for a bare ring homomorphism

`TopologicalRing.restrictedPowerSeriesMap` and everything built on it are stated for an
`Algebra A B` instance.  The completed principal localizations of Stacks 0GGR's fourth paragraph
are not presented that way: the whole `Rig.RingHom.completedAwayMap` API is deliberately phrased
in bare `→+*` and `RingHom.Flat`, so as not to put algebra structures on adic completions, where
Mathlib already supplies `Algebra S (AdicCompletion I R)` and a competing local instance is
destructive.

So the arrow `A_{\{f\}} → B_{\{φ f\}}` has to be fed to the results above as a ring
homomorphism.  `Rig.restrictedPowerSeriesMapOfRingHom` is the bridge: it carries the algebra
instance *inside its own definition*, where it is a local definitional choice invisible to every
consumer, so nothing competes at the point of use.
-/

section RingHomForm

universe u

open RestrictedPowerSeries TopologicalRing

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **Coefficient reduction along a bare ring homomorphism.**  The map `A{σ} → B{σ}` induced by
`φ : A → B`, with no `Algebra A B` instance required of the caller: the instance `φ.toAlgebra` is
taken inside this definition, where it is a local definitional choice and cannot compete with
any instance in scope at the point of use. -/
public noncomputable def restrictedPowerSeriesMapOfRingHom (φ : A →+* B) (I : Ideal A)
    (σ : Type u) : RestrictedPowerSeries I σ →+* RestrictedPowerSeries (I.map φ) σ :=
  letI : Algebra A B := φ.toAlgebra
  TopologicalRing.restrictedPowerSeriesMap I σ

/-- For the algebra structure induced by `φ` itself, the bare-homomorphism coefficient reduction
is the usual one. -/
public theorem restrictedPowerSeriesMapOfRingHom_eq [Algebra A B] (I : Ideal A) (σ : Type u) :
    restrictedPowerSeriesMapOfRingHom (algebraMap A B) I σ =
      TopologicalRing.restrictedPowerSeriesMap (B := B) I σ := rfl

/-- **Flatness of `A{σ} → B{σ}` at a rig-closed prime whose contraction to `A` is rig-closed,
for a bare ring homomorphism.**  `Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint_of_comap`
with `φ : A →+* B` in place of an `Algebra A B` instance, so that it can be applied to the
induced map of completed principal localizations. -/
public theorem flat_atPrime_restrictedPowerSeriesMapOfRingHom_of_rigPoint_of_comap
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]
    (φ : A →+* B) (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map φ)) [IsAdicComplete (I.map φ) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hadic : _root_.RingHom.IsAdic φ)
    (hflat : RingHom.IsNaivelyRigFlat φ)
    (q : Ideal (RestrictedPowerSeries (I.map φ) σ)) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom ((I.map φ).map (coefficientRingHom (I.map φ) σ)) q)
    (hpA : Ideal.IsClosedPointAwayFrom I
      ((q.comap (restrictedPowerSeriesMapOfRingHom φ I σ)).comap (coefficientRingHom I σ))) :
    _root_.RingHom.Flat
      ((algebraMap (RestrictedPowerSeries (I.map φ) σ) (Localization.AtPrime q)).comp
        (restrictedPowerSeriesMapOfRingHom φ I σ)) := by
  let : Algebra A B := φ.toAlgebra
  exact flat_atPrime_restrictedPowerSeriesMap_of_rigPoint_of_comap I hI hJ σ hcont hft hA hB
    hadic hflat q hq hpA

end RingHomForm

end Rig

end
