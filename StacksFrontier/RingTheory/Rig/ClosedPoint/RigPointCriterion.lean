module

public import Mathlib.Order.SuccPred.ENat
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Separation.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz
public import StacksFrontier.RingTheory.KrullAkizuki
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Spectrum.Prime.DimensionTwoOpens
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.NeighbourhoodRestrictionEquivalence

/-!
# Rig points of a Noetherian adic ring

The conditions on a prime of a Noetherian adic ring of being maximal among the primes avoiding
an ideal of definition, of cutting out a closed point away from its vanishing locus, and the
complete one-dimensional local domain condition on the quotient, together with
`Rig.rigPoint_tfae`, the eight equivalent descriptions of a rig point.
-/

@[expose] public section

namespace Rig

section

open PrimeSpectrum
open Polynomial

universe u

private lemma radical_eq_of_isIdealOfDefinition
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I J : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (hJ : TopologicalRing.IsIdealOfDefinition J) : I.radical = J.radical := by
  have key : ∀ I J : Ideal A, TopologicalRing.IsIdealOfDefinition I →
      TopologicalRing.IsIdealOfDefinition J → I ≤ J.radical := fun I J hI hJ x hx => by
    obtain ⟨n, hn⟩ := hI.2 (J : Set A) (hJ.1.mem_nhds J.zero_mem)
    exact Ideal.mem_radical_iff.mpr ⟨n, hn (Ideal.pow_mem_pow hx n)⟩
  exact le_antisymm (Ideal.radical_le_radical_iff.mpr (key I J hI hJ))
    (Ideal.radical_le_radical_iff.mpr (key J I hJ hI))

/-- In a pre-adic topological ring, the source's ideals of definition are
exactly the ideals defining the adic topology. -/
public theorem isIdealOfDefinition_iff_isAdic {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (hadic : ∃ J : Ideal A, IsAdic J) (I : Ideal A) :
    TopologicalRing.IsIdealOfDefinition I ↔ IsAdic I := by
  rw [isAdic_iff]
  constructor
  · rintro ⟨hIopen, hIcofinal⟩
    refine ⟨?_, hIcofinal⟩
    obtain ⟨J, hJ⟩ := hadic
    intro n
    obtain ⟨m, -, hm⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp
      (hIopen.mem_nhds (I.zero_mem))
    have hpow : J ^ (m * n) ≤ I ^ n := by
      rw [pow_mul]
      exact Ideal.pow_right_mono hm n
    exact Submodule.isOpen_mono hpow ((isAdic_iff.mp hJ).1 (m * n))
  · rintro ⟨hIpowers, hIcofinal⟩
    exact ⟨by simpa using hIpowers 1, hIcofinal⟩

/-- A prime ideal `q` is maximal among the prime ideals not containing `I`. -/
public abbrev Ideal.IsMaximalAmongPrimesAvoiding {A : Type*} [CommRing A]
    (I q : Ideal A) : Prop :=
  ¬ I ≤ q ∧
    ∀ p : Ideal A, p.IsPrime → q ≤ p → ¬ I ≤ p → p = q

/-- The point defined by `q` is closed in `Spec(A) \ V(I)`. -/
public abbrev Ideal.IsClosedPointAwayFrom {A : Type*} [CommRing A]
    (I q : Ideal A) [q.IsPrime] : Prop :=
  ∃ hq : (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈
      (zeroLocus (I : Set A))ᶜ,
    IsClosed
      ({⟨(⟨q, inferInstance⟩ : PrimeSpectrum A), hq⟩} :
        Set {x : PrimeSpectrum A // x ∈ (zeroLocus (I : Set A))ᶜ})

/-- The local description in condition (8) of the rig-point criterion.  The
topology and completeness on the quotient are the ones induced from `A`. -/
@[stacks 0GG9 "rig-closed, via condition (8) of the rig-point criterion"]
public abbrev Ideal.IsRigPointLocalCondition {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (q : Ideal A) [q.IsPrime] : Prop :=
  ∃ hlocal : IsLocalRing (A ⧸ q),
    let _ : IsLocalRing (A ⧸ q) := hlocal
    ringKrullDim (A ⧸ q) = 1 ∧
      IsNoetherianRing (A ⧸ q) ∧
      IsDomain (A ⧸ q) ∧
      @CompleteSpace (A ⧸ q) (IsTopologicalAddGroup.rightUniformSpace (A ⧸ q)) ∧
      T2Space (A ⧸ q) ∧
      ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
        (I.map (Ideal.Quotient.mk q)).radical = IsLocalRing.maximalIdeal (A ⧸ q)

/-- The point `q` is closed in `Spec(A) \ V(I)` if and only if `q` avoids `I` and is maximal
among the primes avoiding `I`. -/
public lemma isClosedPointAway_iff_isMaximalAmongPrimesAvoiding
    {A : Type*} [CommRing A] (I q : Ideal A) [hq : q.IsPrime] :
    Ideal.IsClosedPointAwayFrom I q ↔ Ideal.IsMaximalAmongPrimesAvoiding I q := by
  constructor
  · rintro ⟨hqU, hclosed⟩
    have hqavoid : ¬ I ≤ q := fun h => hqU ((mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.2 h))
    refine ⟨hqavoid, ?_⟩
    intro p hp hqp hpavoid
    let x : PrimeSpectrum A := ⟨p, hp⟩
    have hxU : x ∈ (zeroLocus (I : Set A))ᶜ := by
      rw [Set.mem_compl_iff, mem_zeroLocus]
      exact fun hi => hpavoid (SetLike.coe_subset_coe.1 hi)
    have hx : (⟨x, hxU⟩ : {x : PrimeSpectrum A // x ∈ (zeroLocus (I : Set A))ᶜ}) ∈
        closure ({⟨(⟨q, hq⟩ : PrimeSpectrum A), hqU⟩} :
          Set {x : PrimeSpectrum A // x ∈ (zeroLocus (I : Set A))ᶜ}) := by
      rw [closure_subtype]
      simp only [Set.image_singleton, PrimeSpectrum.closure_singleton,
        mem_zeroLocus]
      exact SetLike.coe_subset_coe.2 hqp
    have : (⟨x, hxU⟩ : {x : PrimeSpectrum A // x ∈ (zeroLocus (I : Set A))ᶜ}) ∈
        ({⟨(⟨q, hq⟩ : PrimeSpectrum A), hqU⟩} :
          Set {x : PrimeSpectrum A // x ∈ (zeroLocus (I : Set A))ᶜ}) := by
      rwa [← hclosed.closure_eq]
    simpa [x] using congrArg Subtype.val (Set.mem_singleton_iff.1 this)
  · rintro ⟨hqavoid, hmax⟩
    refine ⟨?_, ?_⟩
    · rw [Set.mem_compl_iff, mem_zeroLocus]
      exact fun hi => hqavoid (SetLike.coe_subset_coe.1 hi)
    apply closure_eq_iff_isClosed.mp
    apply Set.Subset.antisymm ?_ subset_closure
    intro x hx
    rw [closure_subtype] at hx
    simp only [Set.image_singleton, PrimeSpectrum.closure_singleton, mem_zeroLocus] at hx
    have hxp : q ≤ x.1.asIdeal := SetLike.coe_subset_coe.1 hx
    have hxi : ¬ I ≤ x.1.asIdeal := by
      have hxU : x.1 ∈ (zeroLocus (I : Set A))ᶜ := x.2
      rw [Set.mem_compl_iff, mem_zeroLocus] at hxU
      exact fun hi => hxU (SetLike.coe_subset_coe.2 hi)
    rw [Set.mem_singleton_iff]
    exact Subtype.ext (PrimeSpectrum.ext (hmax x.1.asIdeal x.1.2 hxp hxi))

private lemma isMaximalAmongPrimesAvoiding_congr_radical
    {A : Type*} [CommRing A] (I J q : Ideal A) [hq : q.IsPrime]
    (hrad : I.radical = J.radical) :
    Ideal.IsMaximalAmongPrimesAvoiding I q ↔ Ideal.IsMaximalAmongPrimesAvoiding J q := by
  have havoid (p : Ideal A) [hp : p.IsPrime] : I ≤ p ↔ J ≤ p := by
    rw [← hp.radical_le_iff, hrad, hp.radical_le_iff]
  constructor
  · rintro ⟨hI, hmax⟩
    refine ⟨fun hJ => hI ((havoid q).2 hJ), ?_⟩
    intro p hp hqp hpJ
    exact hmax p hp hqp (mt (havoid p).1 hpJ)
  · rintro ⟨hJ, hmax⟩
    refine ⟨fun hI => hJ ((havoid q).1 hI), ?_⟩
    intro p hp hqp hpI
    exact hmax p hp hqp (mt (havoid p).2 hpI)

private lemma discreteTopology_quotient_iff_le_of_isIdealOfDefinition
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I q : Ideal A) [hq : q.IsPrime]
    (hI : TopologicalRing.IsIdealOfDefinition I) :
    DiscreteTopology (A ⧸ q) ↔ I ≤ q := by
  constructor
  · intro hdisc
    let := hdisc
    have hopen : IsOpen (q : Set A) := by
      have hset : (Ideal.Quotient.mk q) ⁻¹' ({0} : Set (A ⧸ q)) = (q : Set A) := by
        ext x
        simp [Ideal.Quotient.eq_zero_iff_mem]
      exact hset ▸ (QuotientRing.isOpenQuotientMap_mk q).continuous.isOpen_preimage _
        (isOpen_discrete _)
    obtain ⟨n, hn⟩ := hI.2 (q : Set A) (hopen.mem_nhds q.zero_mem)
    intro x hx
    exact hq.mem_of_pow_mem n (hn (Ideal.pow_mem_pow hx n))
  · intro hIq
    have himage : (Ideal.Quotient.mk q) '' (I : Set A) = ({0} : Set (A ⧸ q)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Set.mem_singleton_iff]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIq hx)
      · rintro rfl
        exact ⟨0, I.zero_mem, by simp⟩
    have hopen : IsOpen ((Ideal.Quotient.mk q) '' (I : Set A)) :=
      (QuotientRing.isOpenMap_coe q) _ hI.1
    exact discreteTopology_of_isOpen_singleton_zero (himage ▸ hopen)

private lemma isAdic_map_quotient {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (I q : Ideal A) (hI : IsAdic I) :
    IsAdic (I.map (Ideal.Quotient.mk q)) := by
  apply isAdic_iff.mpr
  constructor
  · intro n
    have hpow : IsOpen ((I ^ n : Ideal A) : Set A) := (isAdic_iff.mp hI).1 n
    have himage : IsOpen ((Ideal.Quotient.mk q) '' ((I ^ n : Ideal A) : Set A)) :=
      (QuotientRing.isOpenMap_coe q) _ hpow
    have heq : (Ideal.Quotient.mk q) '' ((I ^ n : Ideal A) : Set A) =
        ((I ^ n).map (Ideal.Quotient.mk q) : Set (A ⧸ q)) := by
      ext y
      change (∃ x, x ∈ I ^ n ∧ Ideal.Quotient.mk q x = y) ↔ _
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Ideal.mem_map_of_mem _ hx
      · intro hy
        exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    rwa [← Ideal.map_pow, ← heq]
  · intro s hs
    have hm : Continuous (Ideal.Quotient.mk q) :=
      (QuotientRing.isOpenQuotientMap_mk q).continuous
    have hpre_mem := hm.continuousAt.preimage_mem_nhds hs
    obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp
      hpre_mem
    refine ⟨n, ?_⟩
    intro y hy
    have hy' : y ∈ (I ^ n).map (Ideal.Quotient.mk q) := by rwa [Ideal.map_pow]
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy'
    exact hn hx

private lemma firstCountableTopology_of_isAdic {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (I : Ideal A) (hI : IsAdic I) : FirstCountableTopology A := by
  let : Filter.IsCountablyGenerated (nhds (0 : A)) := hI.hasBasis_nhds_zero.isCountablyGenerated
  refine ⟨fun a => ?_⟩
  rw [← nhds_translation_add_neg a]
  infer_instance

private lemma isAdicComplete_of_complete {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)] [T2Space A]
    (I : Ideal A) (hI : IsAdic I) : IsAdicComplete I A := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let := firstCountableTopology_of_isAdic I hI
  have hSep : IsHausdorff I A := hI.isHausdorff_iff.mpr inferInstance
  have hPre : IsPrecomplete I A := hI.isPrecomplete_iff.mpr inferInstance
  let : IsHausdorff I A := hSep
  let : IsPrecomplete I A := hPre
  exact IsAdicComplete.mk

private lemma isAdicComplete_map_quotient {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsNoetherianRing A]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)] [T2Space A]
    (I q : Ideal A) (hI : IsAdic I) [IsAdicComplete I A] :
    IsAdicComplete (I.map (Ideal.Quotient.mk q)) (A ⧸ q) ∧
      @CompleteSpace (A ⧸ q) (IsTopologicalAddGroup.rightUniformSpace (A ⧸ q)) ∧
      T2Space (A ⧸ q) := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : UniformSpace (A ⧸ q) := IsTopologicalAddGroup.rightUniformSpace (A ⧸ q)
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup (A ⧸ q) := isUniformAddGroup_of_addCommGroup
  let := firstCountableTopology_of_isAdic I hI
  let : CompleteSpace (A ⧸ q) :=
    QuotientAddGroup.completeSpace_right A q.toAddSubgroup
  have hJ : IsAdic (I.map (Ideal.Quotient.mk q)) := isAdic_map_quotient I q hI
  have hJjac : I.map (Ideal.Quotient.mk q) ≤ (⊥ : Ideal (A ⧸ q)).jacobson := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    rw [Ideal.mem_jacobson_bot]
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hu := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I ha)) b
    exact hu.map (Ideal.Quotient.mk q)
  have hSep : IsHausdorff (I.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
    IsHausdorff.of_le_jacobson _ _ hJjac
  have hPre : IsPrecomplete (I.map (Ideal.Quotient.mk q)) (A ⧸ q) :=
    hJ.isPrecomplete_iff.mpr inferInstance
  let : IsHausdorff (I.map (Ideal.Quotient.mk q)) (A ⧸ q) := hSep
  let : IsPrecomplete (I.map (Ideal.Quotient.mk q)) (A ⧸ q) := hPre
  exact ⟨IsAdicComplete.mk, inferInstance, hJ.isHausdorff_iff.mp hSep⟩

/-- An ideal of an adically complete ring lies in every maximal ideal. -/
private lemma le_of_isAdicComplete_of_isMaximal {R : Type*} [CommRing R] (J M : Ideal R)
    [IsAdicComplete J R] [M.IsMaximal] : J ≤ M :=
  (IsAdicComplete.le_jacobson_bot J).trans
    (Ideal.jacobson_bot.trans_le (Ring.jacobson_le_of_isMaximal M))

/-- The image of an ideal `I` in `A ⧸ q` is zero if and only if `I ≤ q`. -/
private lemma map_quotient_eq_bot_iff {A : Type*} [CommRing A] {I q : Ideal A} :
    I.map (Ideal.Quotient.mk q) = ⊥ ↔ I ≤ q := by
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

private lemma complete_one_dimensional_domain_is_local {S : Type*} [CommRing S]
    [IsNoetherianRing S] [IsDomain S] [TopologicalSpace S] [IsTopologicalRing S]
    [@CompleteSpace S (IsTopologicalAddGroup.rightUniformSpace S)] [T2Space S]
    (J : Ideal S) (hJ : IsAdic J) [IsAdicComplete J S]
    (hdim : ringKrullDim S = 1) (hndisc : ¬ DiscreteTopology S) :
    ∃ _hlocal : IsLocalRing S,
      (J.radical = IsLocalRing.maximalIdeal S) := by
  have hJne : J ≠ ⊥ := by
    intro hbot
    apply hndisc
    have hopen : IsOpen ({0} : Set S) := by
      have h := (isAdic_iff.mp hJ).1 1
      simpa [hbot] using h
    exact discreteTopology_of_isOpen_singleton_zero hopen
  let T := S ⧸ J
  have hdimLE : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr hdim.le
  have hmax : ∀ P : Ideal S, P.IsPrime → J ≤ P → P.IsMaximal := fun P hP hJP =>
    Ideal.IsPrime.isMaximal_of_ne_bot hP (ne_bot_of_le_ne_bot hJne hJP)
  have hzero : Ring.KrullDimLE 0 T := by
    apply Ring.KrullDimLE.mk₀
    intro P hP
    have hJp : J ≤ P.comap (Ideal.Quotient.mk J) := by
      intro x hx
      change Ideal.Quotient.mk J x ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact P.zero_mem
    have : (P.comap (Ideal.Quotient.mk J)).IsMaximal := hmax _ inferInstance hJp
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective P]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  let : Ring.KrullDimLE 0 T := hzero
  let : IsNoetherianRing T := inferInstance
  let : IsArtinianRing T := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : Finite (PrimeSpectrum T) := IsArtinianRing.instFinitePrimeSpectrum T
  let f : PrimeSpectrum T → PrimeSpectrum S :=
    PrimeSpectrum.comap (Ideal.Quotient.mk J)
  let V : Set (PrimeSpectrum S) := zeroLocus (J : Set S)
  have hrange : Set.range f = V := by
    rw [range_comap_of_surjective T (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective]
    rw [Ideal.mk_ker]
  have hfinite : V.Finite := by
    rw [← hrange]
    rw [← Set.image_univ]
    exact Set.Finite.image f Set.finite_univ
  have hVmax (x : V) : x.1.asIdeal.IsMaximal :=
    hmax _ x.1.2 ((mem_zeroLocus _ _).1 x.2)
  let : Finite V := hfinite.to_subtype
  let : T1Space V := ⟨fun x => by
    rw [isClosed_induced_iff]
    refine ⟨{x.1}, (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.1).2 (hVmax x), ?_⟩
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subtype.ext_iff.symm⟩
  let : HenselianRing S J := IsAdicComplete.henselianRing S J
  have hpair : HenselianPair S J := henselianPair_of_henselianRing S J
  have hconn : IsConnected V := by
    simpa [V] using
      (isConnected_zeroLocus_add J ⊥ hpair
        (Ideal.isPrime_bot : (⊥ : Ideal S).IsPrime))
  let : PreconnectedSpace V := Subtype.preconnectedSpace hconn.isPreconnected
  have hVsub : Subsingleton V := PreconnectedSpace.trivial_of_discrete
  have hunique : ∃! M : Ideal S, M.IsMaximal := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal S
    refine ⟨M, hM, ?_⟩
    intro N hN
    let x : V := ⟨⟨M, hM.isPrime⟩, le_of_isAdicComplete_of_isMaximal J M⟩
    let y : V := ⟨⟨N, hN.isPrime⟩, le_of_isAdicComplete_of_isMaximal J N⟩
    have hxy : x = y := Subsingleton.elim x y
    exact (congrArg (fun z : V => z.1.asIdeal) hxy).symm
  let hlocal : IsLocalRing S := IsLocalRing.of_unique_max_ideal hunique
  let := hlocal
  have hJle : J ≤ IsLocalRing.maximalIdeal S := le_of_isAdicComplete_of_isMaximal J _
  have hrad : J.radical = IsLocalRing.maximalIdeal S := by
    apply le_antisymm
    · rw [← (IsLocalRing.maximalIdeal.isMaximal S).isPrime.radical]
      exact Ideal.radical_le_radical_iff.mpr (le_trans hJle Ideal.le_radical)
    · rw [Ideal.radical_eq_sInf]
      apply le_sInf
      intro P hP
      rw [IsLocalRing.eq_maximalIdeal (hmax P hP.2 hP.1)]
  exact ⟨hlocal, hrad⟩

private lemma map_le_nonzero_prime_of_maximalAvoiding {A : Type*} [CommRing A]
    (I q : Ideal A) [_hq : q.IsPrime] (_havoid : ¬ I ≤ q)
    (hmax : ∀ p : Ideal A, p.IsPrime → q ≤ p → ¬ I ≤ p → p = q)
    (P : Ideal (A ⧸ q)) [hP : P.IsPrime] (hPne : P ≠ ⊥) :
    I.map (Ideal.Quotient.mk q) ≤ P := by
  by_contra hnot
  let p : Ideal A := P.comap (Ideal.Quotient.mk q)
  have hp : p.IsPrime := inferInstance
  have hqp : q ≤ p := by
    intro x hx
    change Ideal.Quotient.mk q x ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.zero_mem
  have hIp : ¬ I ≤ p := fun hIp => hnot (Ideal.map_le_iff_le_comap.mpr hIp)
  have heq : p = q := hmax p hp hqp hIp
  have hPbot : P = ⊥ := by
    calc
      P = p.map (Ideal.Quotient.mk q) :=
        (Ideal.map_comap_of_surjective (Ideal.Quotient.mk q)
          Ideal.Quotient.mk_surjective P).symm
      _ = q.map (Ideal.Quotient.mk q) := by rw [heq]
      _ = ⊥ := by rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact hPne hPbot

private lemma ringKrullDim_le_one_of_maximalAvoiding {A : Type*} [CommRing A]
    [IsNoetherianRing A] (I q : Ideal A) [hq : q.IsPrime]
    (havoid : ¬ I ≤ q)
    (hmax : ∀ p : Ideal A, p.IsPrime → q ≤ p → ¬ I ≤ p → p = q) :
    Ring.KrullDimLE 1 (A ⧸ q) := by
  let S := A ⧸ q
  let J : Ideal S := I.map (Ideal.Quotient.mk q)
  have hJne : J ≠ ⊥ := map_quotient_eq_bot_iff.not.2 havoid
  have hall : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P.IsMaximal := by
    intro P hPne hP
    by_contra hPmax
    obtain ⟨M, hMmax, hPM⟩ := P.exists_le_maximal hP.ne_top
    have hPMne : P ≠ M := by
      intro h
      apply hPmax
      rw [h]
      exact hMmax
    have hPMlt : P < M := lt_of_le_of_ne hPM hPMne
    let L := Localization.AtPrime M
    let : Algebra S L := inferInstance
    let : IsLocalization.AtPrime L M := inferInstance
    have hPpos : 0 < P.height := by
      have hPheight : P.height ≠ 0 := by
        intro h
        exact hPne ((Ideal.height_eq_zero_iff_eq_bot).mp h)
      exact lt_of_le_of_ne bot_le (Ne.symm hPheight)
    have hPMheight : P.height < M.height := Ideal.height_strict_mono_of_isPrime hPMlt
    have hPge1 : (1 : ℕ∞) ≤ P.height := by
      exact (ENat.add_one_le_iff ENat.zero_ne_top).2 hPpos
    have hMgt1 : (1 : ℕ∞) < M.height := hPge1.trans_lt hPMheight
    have hMge2 : (2 : ℕ∞) ≤ M.height :=
      (ENat.add_one_le_iff ENat.one_ne_top).2 hMgt1
    have hdim : 2 ≤ ringKrullDim L := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height M L]
      exact WithBot.coe_le_coe.mpr hMge2
    have ⟨x, hxJ, hx0⟩ : ∃ x : S, x ∈ J ∧ x ≠ 0 := by
      by_contra h
      push Not at h
      apply hJne
      ext x
      constructor
      · intro hx
        have hx0 := h x hx
        simp [hx0]
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        exact J.zero_mem
    let xL : L := algebraMap S L x
    have hxL : xL ≠ 0 := by
      have hden : M.primeCompl ≤ nonZeroDivisors S := by
        intro a ha
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro ha0
        exact ha (ha0 ▸ M.zero_mem)
      have hinj : Function.Injective (algebraMap S L) :=
        IsLocalization.injective L hden
      intro hzero
      exact hx0 (hinj (by simpa [xL] using hzero))
    let U : Set (PrimeSpectrum L) := PrimeSpectrum.basicOpen xL
    have hUopen : IsOpen U := PrimeSpectrum.isOpen_basicOpen
    have hUeq : U = {⟨⊥, Ideal.isPrime_bot⟩} := by
      apply Set.Subset.antisymm
      · intro y hy
        have hyx : xL ∉ y.asIdeal := (PrimeSpectrum.mem_basicOpen xL y).mp hy
        let p : Ideal S := y.asIdeal.comap (algebraMap S L)
        have hpp : p.IsPrime := inferInstance
        have hxnotp : x ∉ p := by
          simpa [p, xL] using hyx
        by_cases hpbot : p = ⊥
        · have hinj : Function.Injective (PrimeSpectrum.comap (algebraMap S L)) :=
            PrimeSpectrum.localization_comap_injective (R := S) (S := L) M.primeCompl
          apply hinj
          apply PrimeSpectrum.ext
          simpa [p] using hpbot
        · let : p.IsPrime := hpp
          have hJp : J ≤ p :=
            map_le_nonzero_prime_of_maximalAvoiding I q havoid hmax p hpbot
          exact (hxnotp (hJp hxJ)).elim
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact (PrimeSpectrum.mem_basicOpen xL ⟨⊥, Ideal.isPrime_bot⟩).mpr hxL
    have hUnonempty : U.Nonempty := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      change (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L) ∈ PrimeSpectrum.basicOpen xL
      rw [PrimeSpectrum.mem_basicOpen]
      exact hxL
    have hUinf := PrimeSpectrum.infinite_of_two_le_ringKrullDim L hdim U hUopen hUnonempty
    have hUfin : U.Finite := by rw [hUeq]; exact Set.finite_singleton _
    exact hUinf hUfin
  exact Ring.krullDimLE_one_iff_of_isPrime_bot.mpr hall

/-- The eight equivalent characterizations of a rig point in a Noetherian adic
topological ring. -/
@[stacks 0GG8]
public lemma rigPoint_tfae {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsNoetherianRing A]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)] [T2Space A]
    (_hadic : ∃ I : Ideal A, IsAdic I) (q : Ideal A) [q.IsPrime] :
    List.TFAE
      [ ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
          Ideal.IsMaximalAmongPrimesAvoiding I q,
        ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
          Ideal.IsClosedPointAwayFrom I q,
        ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
          Ideal.IsMaximalAmongPrimesAvoiding I q,
        ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
          Ideal.IsClosedPointAwayFrom I q,
        ringKrullDim (A ⧸ q) = 1 ∧
          ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ ¬ I ≤ q,
        ringKrullDim (A ⧸ q) = 1 ∧
          ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I → ¬ I ≤ q,
        ringKrullDim (A ⧸ q) = 1 ∧ ¬ DiscreteTopology (A ⧸ q),
          Ideal.IsRigPointLocalCondition q ] := by
  obtain ⟨I, hIadic⟩ := _hadic
  let : IsAdicComplete I A := isAdicComplete_of_complete I hIadic
  have hIdef : TopologicalRing.IsIdealOfDefinition I :=
    (isIdealOfDefinition_iff_isAdic ⟨I, hIadic⟩ I).2 hIadic
  have hJadic : IsAdic (I.map (Ideal.Quotient.mk q)) := isAdic_map_quotient I q hIadic
  obtain ⟨hJcomplete, hScomplete, hST2⟩ := isAdicComplete_map_quotient I q hIadic
  let : IsAdicComplete (I.map (Ideal.Quotient.mk q)) (A ⧸ q) := hJcomplete
  tfae_have 1 ↔ 2 := by simp only [isClosedPointAway_iff_isMaximalAmongPrimesAvoiding]
  tfae_have 3 ↔ 4 := by simp only [isClosedPointAway_iff_isMaximalAmongPrimesAvoiding]
  tfae_have 2 → 4 := by
    rintro ⟨I, hI, hclosed⟩ J hJ
    have hrad := radical_eq_of_isIdealOfDefinition I J hI hJ
    exact (isClosedPointAway_iff_isMaximalAmongPrimesAvoiding J q).mpr
      ((isMaximalAmongPrimesAvoiding_congr_radical I J q hrad).mp
        ((isClosedPointAway_iff_isMaximalAmongPrimesAvoiding I q).mp hclosed))
  tfae_have 4 → 5 := by
    intro h
    have hmax :=
      (isClosedPointAway_iff_isMaximalAmongPrimesAvoiding I q).mp (h I hIdef)
    have hdimLE : Ring.KrullDimLE 1 (A ⧸ q) :=
      ringKrullDim_le_one_of_maximalAvoiding I q hmax.1 hmax.2
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (A ⧸ q)
    have hMne : M ≠ ⊥ := ne_bot_of_le_ne_bot (map_quotient_eq_bot_iff.not.2 hmax.1)
      (le_of_isAdicComplete_of_isMaximal _ M)
    have hMheight : (1 : ℕ∞) ≤ M.height := by
      have hlt : (⊥ : Ideal (A ⧸ q)) < M := bot_lt_iff_ne_bot.mpr hMne
      have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      simpa [Ideal.height_bot] using h
    have hdimLower : (1 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) :=
      le_trans (WithBot.coe_le_coe.mpr hMheight)
        (Ideal.height_le_ringKrullDim_of_isPrime (I := M))
    have hdim : ringKrullDim (A ⧸ q) = 1 :=
      le_antisymm (Ring.krullDimLE_iff.mp hdimLE) hdimLower
    exact ⟨hdim, I, hIdef, hmax.1⟩
  tfae_have 5 → 6 := by
    rintro ⟨hdim, I, hI, hIavoid⟩
    refine ⟨hdim, ?_⟩
    intro J hJ hJle
    have hrad := radical_eq_of_isIdealOfDefinition I J hI hJ
    have hIrad : I.radical ≤ q := by
      rw [hrad]
      simpa [(inferInstance : q.IsPrime).radical] using Ideal.radical_mono hJle
    exact hIavoid (le_trans Ideal.le_radical hIrad)
  tfae_have 5 → 1 := by
    rintro ⟨hdim, I', hIdef', hIavoid⟩
    have hdimLE : Ring.KrullDimLE 1 (A ⧸ q) := Ring.krullDimLE_iff.mpr hdim.le
    refine ⟨I', hIdef', ?_⟩
    refine ⟨hIavoid, ?_⟩
    intro p hp hqp hpavoid
    by_contra hne
    let P : Ideal (A ⧸ q) := p.map (Ideal.Quotient.mk q)
    have hP : P.IsPrime := by
      dsimp [P]
      exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hqp)
    have hPne : P ≠ ⊥ := by
      intro hPbot
      have hpq : p ≤ q := by
        intro x hx
        have hxP : Ideal.Quotient.mk q x ∈ P := Ideal.mem_map_of_mem _ hx
        rw [hPbot] at hxP
        exact Ideal.Quotient.eq_zero_iff_mem.mp hxP
      exact hne (le_antisymm hqp hpq).symm
    have hPmax : P.IsMaximal :=
      Ideal.IsPrime.isMaximal_of_ne_bot hP hPne
    have hJleP : I.map (Ideal.Quotient.mk q) ≤ P := le_of_isAdicComplete_of_isMaximal _ P
    have hcomap : P.comap (Ideal.Quotient.mk q) = p := by
      dsimp [P]
      rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr hqp]
    have hIleP : I ≤ p := by
      simpa [hcomap] using (Ideal.map_le_iff_le_comap).mp hJleP
    have hradII' := radical_eq_of_isIdealOfDefinition I I' hIdef hIdef'
    have hI'radle : I'.radical ≤ p := by
      rw [← hp.radical, ← hradII']
      exact Ideal.radical_le_radical_iff.mpr (le_trans hIleP Ideal.le_radical)
    exact hpavoid (le_trans Ideal.le_radical hI'radle)
  tfae_have 6 ↔ 7 := by
    constructor
    · rintro ⟨hdim, hall⟩
      refine ⟨hdim, ?_⟩
      intro hdisc
      exact (hall I hIdef) ((discreteTopology_quotient_iff_le_of_isIdealOfDefinition
        I q hIdef).mp hdisc)
    · rintro ⟨hdim, hndisc⟩
      refine ⟨hdim, ?_⟩
      intro I hI hIq
      exact hndisc ((discreteTopology_quotient_iff_le_of_isIdealOfDefinition
        I q hI).mpr hIq)
  tfae_have 7 → 8 := by
    rintro ⟨hdim, hndisc⟩
    let : @CompleteSpace (A ⧸ q)
        (IsTopologicalAddGroup.rightUniformSpace (A ⧸ q)) := hScomplete
    let : T2Space (A ⧸ q) := hST2
    obtain ⟨hlocal, hJrad⟩ :=
      complete_one_dimensional_domain_is_local _ hJadic hdim hndisc
    let := hlocal
    refine ⟨hlocal, hdim, inferInstance, inferInstance, hScomplete, hST2, ?_⟩
    intro K hKdef
    have hKrad := radical_eq_of_isIdealOfDefinition I K hIdef hKdef
    have key : ∀ I K : Ideal A, I.radical = K.radical →
        (I.map (Ideal.Quotient.mk q)).radical ≤ (K.map (Ideal.Quotient.mk q)).radical :=
      fun I K h => Ideal.radical_le_radical_iff.mpr
        ((Ideal.map_mono (Ideal.le_radical.trans h.le)).trans (Ideal.map_radical_le _))
    have hmaprad := le_antisymm (key I K hKrad) (key K I hKrad.symm)
    rw [← hmaprad, hJrad]
  tfae_have 8 → 5 := by
    rintro ⟨hlocal, hdim, hNoeth, hdom, hcomplete, hT2, hrad⟩
    let := hlocal
    refine ⟨hdim, I, hIdef, fun hIq => ?_⟩
    have hmaxbot : IsLocalRing.maximalIdeal (A ⧸ q) = ⊥ := by
      simpa [map_quotient_eq_bot_iff.2 hIq] using (hrad I hIdef).symm
    have hfield : IsField (A ⧸ q) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmaxbot
    have hzero := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at hzero
    exact (by norm_num : (1 : WithBot ℕ∞) ≠ 0) hzero
  tfae_finish

end

end Rig

end
