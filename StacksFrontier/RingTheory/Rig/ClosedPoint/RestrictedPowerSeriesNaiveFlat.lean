module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeBaseChange
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeriesRigPoint
public import StacksFrontier.RingTheory.Rig.FlatIsLocal

/-!
# Naive rig-flatness of `A{σ} → B{σ}`

Let `A → B` be a continuous, rig-flat homomorphism of topological finite type between Noetherian
weakly admissible adic rings, complete along an ideal of definition `I` of `A` and along its
extension to `B`.  Then the induced map `A{σ} → B{σ}` of restricted power series rings on a
finite set of variables is *naively* rig-flat (Stacks 0GGM).

The flatness clause is the content: it is condition (1) of the four equivalent flatness tests
of Stacks 0GGL (`Rig.naivelyRigFlat_tfae`), reached from condition (4) — flatness at the
rig-closed primes only — which is exactly what the fourth and fifth paragraphs of the proof of
Stacks 0GGR deliver in `Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint`.  Adicness and
topological finite type of `A{σ} → B{σ}` are `Rig.isAdic_restrictedPowerSeriesMap` and
`Rig.isTopologicallyOfFiniteType_restrictedPowerSeriesMap`.

This is the form in which the third paragraph of the proof of Stacks 0GGR consumes the case
`C = A{x₁, …, xₙ}`: the paragraph replaces an arbitrary `C` by a restricted power series ring
it is a quotient of, and what it needs about that ring is not flatness at one prime but the
flatness clause of naive rig-flatness, which is what base change for flatness takes as input.

## Main results

* `Rig.isNaivelyRigFlat_restrictedPowerSeriesMap`: `A{σ} → B{σ}` is naively rig-flat.
* `Rig.flat_localizationAway_restrictedPowerSeriesMap`: its flatness clause, in the
  `Module.Flat` form that base change for flatness consumes.

## Implementation notes

Condition (4) of `Rig.naivelyRigFlat_tfae` quantifies over *some* ideal of definition of the
target, while `Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint` asks for the coefficient
ideal specifically.  The two are interchangeable because maximality among the primes avoiding an
ideal of definition does not depend on which ideal of definition is taken — any two are
cofinal in each other's powers — which is
`Rig.isMaximalAmongPrimesAvoiding_congr_isIdealOfDefinition` here.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0GGM](https://stacks.math.columbia.edu/tag/0GGM)
* [Stacks Project, Tag 0GGL](https://stacks.math.columbia.edu/tag/0GGL)
-/

@[expose] public section

namespace Rig

universe u

open RestrictedPowerSeries TopologicalRing

/-- A prime contained in a prime containing a cofinal power of an ideal contains the ideal. -/
private theorem le_of_pow_le_of_le {R : Type*} [CommRing R] {K L : Ideal R} {n : ℕ}
    (hKL : K ^ n ≤ L) (p : Ideal R) (hp : p.IsPrime) (hLp : L ≤ p) : K ≤ p :=
  fun _ hx => hp.mem_of_pow_mem n (hLp (hKL (Ideal.pow_mem_pow hx n)))

/-- **Maximality among the primes avoiding an ideal of definition does not depend on the ideal
of definition.**  Any two ideals of definition are cofinal in each other's powers, so a prime
contains one exactly when it contains the other. -/
public theorem isMaximalAmongPrimesAvoiding_congr_isIdealOfDefinition {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] {I J : Ideal R}
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (hJ : TopologicalRing.IsIdealOfDefinition J) (q : Ideal R) [hq : q.IsPrime]
    (h : Ideal.IsMaximalAmongPrimesAvoiding I q) :
    Ideal.IsMaximalAmongPrimesAvoiding J q := by
  obtain ⟨n, hIJ, hJI⟩ := hI.exists_pow_le_and_pow_le hJ
  refine ⟨fun hle => h.1 (le_of_pow_le_of_le hIJ q hq hle), fun p hp hqp hpJ => ?_⟩
  exact h.2 p hp hqp fun hpI => hpJ (le_of_pow_le_of_le hJI p hp hpI)

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]

/-- **`A{σ} → B{σ}` is naively rig-flat.**  For a continuous, rig-flat homomorphism `A → B` of
topologically finite type between Noetherian weakly admissible rings, complete along an ideal of
definition `I` of `A` and along its extension to `B`, the induced map of restricted power series
rings on a finite set of variables is naively rig-flat (Stacks 0GGM).

The flatness clause comes from flatness at the rig-closed primes
(`Rig.flat_atPrime_restrictedPowerSeriesMap_of_rigPoint`, the fourth and fifth paragraphs of the
proof of Stacks 0GGR) through condition (4) of `Rig.naivelyRigFlat_tfae`. -/
public theorem isNaivelyRigFlat_restrictedPowerSeriesMap
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hflat : RingHom.IsRigFlat (algebraMap A B)) :
    RingHom.IsNaivelyRigFlat (restrictedPowerSeriesMap (B := B) I σ) := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hJfg : (I.map (algebraMap A B)).FG := hIfg.map _
  let : IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) :=
    isLinearTopology_restrictedPowerSeries I hIfg σ
  let : IsLinearTopology (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    isLinearTopology_restrictedPowerSeries _ hJfg σ
  have hAadic : _root_.IsAdic (coefficientIdeal I σ) := isAdic_coefficientIdeal I hIfg σ
  have hBadic : _root_.IsAdic (coefficientIdeal (I.map (algebraMap A B)) σ) :=
    isAdic_coefficientIdeal _ hJfg σ
  have hmapadic : _root_.RingHom.IsAdic (restrictedPowerSeriesMap (B := B) I σ) :=
    isAdic_restrictedPowerSeriesMap I hIfg σ
  have hmapcont : Continuous (restrictedPowerSeriesMap (B := B) I σ) :=
    continuous_of_isAdic_of_map_le hAadic hBadic _
      (le_of_eq (map_coefficientIdeal_restrictedPowerSeriesMap I σ))
  refine ⟨hmapadic, isTopologicallyOfFiniteType_restrictedPowerSeriesMap I hIfg σ hJ hft, ?_⟩
  have hcrit := naivelyRigFlat_tfae (restrictedPowerSeriesMap (B := B) I σ) hmapcont
    (isWeaklyAdmissible_restrictedPowerSeries I hIfg σ)
    (isWeaklyAdmissible_restrictedPowerSeries (I.map (algebraMap A B)) hJfg σ)
    ⟨coefficientIdeal I σ, hAadic, hIfg.map _⟩
    ⟨coefficientIdeal (I.map (algebraMap A B)) σ, hBadic, hJfg.map _⟩ hmapadic
  refine (hcrit.out 4 1).mp ?_
  intro q hq hmax
  obtain ⟨J', hJ'def, hJ'max⟩ := hmax
  refine flat_atPrime_restrictedPowerSeriesMap_of_rigPoint I hI hJ σ hcont hft hA hflat q ?_
  exact (isClosedPointAway_iff_isMaximalAmongPrimesAvoiding _ q).2
    (isMaximalAmongPrimesAvoiding_congr_isIdealOfDefinition hJ'def
      (isIdealOfDefinition_of_isAdic hBadic) q hJ'max)

/-- **The flatness clause of naive rig-flatness of `A{σ} → B{σ}`, as a module statement.**  For
a topologically nilpotent `a : A{σ}`, the localization of `B{σ}` away from the image of `a` is
flat over `A{σ}`.  This is the shape base change for flatness
(`Rig.flat_atPrime_tensorProduct_of_flat`) takes as input. -/
public theorem flat_localizationAway_restrictedPowerSeriesMap
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    (hcont : Continuous (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hflat : RingHom.IsRigFlat (algebraMap A B))
    (a : RestrictedPowerSeries I σ) (ha : IsTopologicallyNilpotent a) :
    letI : Algebra (RestrictedPowerSeries I σ)
        (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
      (restrictedPowerSeriesMap (B := B) I σ).toAlgebra
    Module.Flat (RestrictedPowerSeries I σ)
      (Localization.Away (restrictedPowerSeriesMap (B := B) I σ a)) := by
  let : Algebra (RestrictedPowerSeries I σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ) :=
    (restrictedPowerSeriesMap (B := B) I σ).toAlgebra
  have h := (isNaivelyRigFlat_restrictedPowerSeriesMap I hI hJ σ hcont hft hA hflat).2.2 a ha
  rw [show (algebraMap (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
        (Localization.Away (restrictedPowerSeriesMap (B := B) I σ a))).comp
        (restrictedPowerSeriesMap (B := B) I σ) =
      algebraMap (RestrictedPowerSeries I σ)
        (Localization.Away (restrictedPowerSeriesMap (B := B) I σ a)) from
    (IsScalarTower.algebraMap_eq (RestrictedPowerSeries I σ)
      (RestrictedPowerSeries (I.map (algebraMap A B)) σ)
      (Localization.Away (restrictedPowerSeriesMap (B := B) I σ a))).symm] at h
  exact _root_.RingHom.flat_algebraMap_iff.mp h

end Main

section CompletedTensorProduct

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A] [IsLinearTopology A A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsNoetherianRing B] [IsLinearTopology B B]

/-- **`A{σ} → B ⊗̂[A] A{σ}` is naively rig-flat.**  The completed tensor product is `B{σ}`
(`TopologicalRing.completedTensorProductRestrictedEquiv`, Stacks 0GGG) and that identification
carries the canonical map `A{σ} → B ⊗̂[A] A{σ}` to `A{σ} → B{σ}`, so naive rig-flatness
transports from `Rig.isNaivelyRigFlat_restrictedPowerSeriesMap`.

This is the case `C = A{x₁, …, xₙ}` of the naive form of Stacks 0GGR, stated at the completed
tensor product, which is the shape the third paragraph of the proof uses as the base of its
reduction. -/
public theorem isNaivelyRigFlat_completedTensorProduct_restrictedPowerSeries
    (I : Ideal A) (hI : _root_.IsAdic I) [IsAdicComplete I A]
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    [IsAdicComplete (I.map (algebraMap A B)) B]
    (σ : Type u) [Finite σ]
    [IsLinearTopology (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ)]
    (hcont : Continuous (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hflat : RingHom.IsRigFlat (algebraMap A B)) :
    RingHom.IsNaivelyRigFlat (algebraMap (RestrictedPowerSeries I σ)
      (CompletedTensorProduct (R := A) (M := B) (N := RestrictedPowerSeries I σ))) := by
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hAadic : _root_.IsAdic (coefficientIdeal I σ) := isAdic_coefficientIdeal I hIfg σ
  obtain ⟨hadic, hftD⟩ :=
    isAdic_and_isTopologicallyOfFiniteType_completedTensorProduct_baseChange
      (R := A) (A := B) (C := RestrictedPowerSeries I σ)
      (isWeaklyAdmissible_of_isAdicComplete (I.map (algebraMap A B)) hJ
        (isIdealOfDefinition_of_isAdic hJ))
      (isWeaklyAdmissible_restrictedPowerSeries I hIfg σ)
      ⟨coefficientIdeal I σ, hIfg.map _, hAadic⟩ hcont
      (continuous_coefficientRingHom I hI hIfg σ) ⟨hflat.1, hflat.2.1⟩
  refine RingHom.isNaivelyRigFlat_of_ringEquiv _ (restrictedPowerSeriesMap (B := B) I σ)
    (completedTensorProductRestrictedEquiv I hIfg σ hJ)
    (RingHom.ext fun x => completedTensorProductRestrictedEquiv_tmul_one I hIfg σ hJ x)
    ⟨hadic, hftD⟩ (isNaivelyRigFlat_restrictedPowerSeriesMap I hI hJ σ hcont hft hA hflat)

end CompletedTensorProduct

end Rig

end
