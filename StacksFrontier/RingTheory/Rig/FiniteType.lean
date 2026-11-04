module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Homeomorph.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Adic morphisms of topologically finite type

Let `φ : A →+* B` be a continuous map of adic topological rings whose topologies admit
finitely generated ideals of definition.  Being adic and topologically of finite type admits
eight equivalent descriptions: tautness together with topological finite type; finite type of
the reduction modulo some, respectively every, ideal of definition of the source; membership
of `B` in the category of adically complete algebras of finite type modulo some, respectively
every, such ideal; and a presentation of `B` as the quotient by a closed ideal of a ring of
restricted power series, respectively of a completed polynomial ring.

The equivalences are obtained from the four conditions of Tag 0ANU by comparing an ideal of
definition with the ideal witnessing adicness: cofinality of their power filtrations shows
that an ideal of definition extends to an ideal inducing the topology of `B`, and an ideal
inducing the topology of `B` is closed, so the reduction modulo its closure is the reduction
modulo the ideal itself.  The restricted-power-series and completed-polynomial presentations
are identified by comparing the restricted-power-series uniformity on a polynomial ring with
the adic uniformity of the extended ideal.

## Main definitions

The untagged predicates below encode conditions (3)–(6) and (8) of the source lemma.
Condition (7) uses the restricted-power-series presentation predicate of Tag 0ANU.

* `Rig.FiniteTypeModuloSomeIdealOfDefinition`, `Rig.FiniteTypeModuloEveryIdealOfDefinition`,
  `Rig.FiniteTypeAdicAlgebraForSomeIdeal`, `Rig.FiniteTypeAdicAlgebraForEveryIdeal`,
  `Rig.HasCompletedPolynomialPresentation`.

## Main results

* `Rig.adicFiniteType_tfae` — the eight equivalent conditions.

## Implementation notes

Conditions (5) and (6) use the two properties defining the objects of the category in
Tag 0AL4, for the algebra structure induced by the specified ring homomorphism.  In condition
(8), the presentation identifies the target with the quotient by a closed ideal as a
topological algebra, including compatibility with the coefficient map.  Condition (7) uses the
existing presentation by the restricted power series ring of Tag 0ANU.

## References

* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
-/

@[expose] public section

namespace Rig

open Filter
open scoped Topology

universe u v

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- In an adic topological ring every ideal of definition defines the topology through its
powers, not only the one witnessing adicness. -/
public lemma idealOfDefinition_isAdic_of_isAdicRing
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hR : TopologicalRing.IsAdic R)
    (I : Ideal R) (hI : TopologicalRing.IsIdealOfDefinition I) : _root_.IsAdic I := by
  obtain ⟨J, _, hJ⟩ := hR.1
  obtain ⟨n, -, hn⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp (hI.1.mem_nhds I.zero_mem)
  have hn' : J ^ n ≤ I := fun x hx => hn hx
  refine isAdic_iff.mpr ⟨fun k => ?_, hI.2⟩
  have hpow : J ^ (n * k) ≤ I ^ k := by
    rw [pow_mul]
    exact Ideal.pow_right_mono hn' k
  have hmem : ((J ^ (n * k) : Ideal R) : Set R) ∈ 𝓝 (0 : R) :=
    hJ.hasBasis_nhds_zero.mem_iff.mpr ⟨n * k, trivial, fun _ hx => hx⟩
  exact (I ^ k).toAddSubgroup.isOpen_of_mem_nhds
    (Filter.mem_of_superset hmem (fun x hx => hpow hx))

/-- An open ideal defining the topology through its powers is a weak ideal of definition. -/
private lemma isWeakIdealOfDefinition_of_isAdic
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] {I : Ideal R} (hIopen : IsOpen (I : Set R))
    (hIadic : _root_.IsAdic I) :
    TopologicalRing.IsWeakIdealOfDefinition I := by
  refine ⟨hIopen, fun x hx => ?_⟩
  suffices hpow : ∀ m : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → x ^ n ∈ I ^ m by
    simpa [IsTopologicallyNilpotent, hIadic.hasBasis_nhds_zero.tendsto_right_iff] using hpow
  exact fun m => ⟨m, fun n hn =>
    Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx _)⟩

/-- An adic topological ring is weakly admissible: an ideal of definition consists of
topologically nilpotent elements, and adicness supplies completeness and separatedness. -/
public lemma weaklyAdmissible_of_isAdicRing
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hR : TopologicalRing.IsAdic R) :
    TopologicalRing.IsWeaklyAdmissible R := by
  obtain ⟨I, hI, _⟩ := hR.1
  exact ⟨⟨I, isWeakIdealOfDefinition_of_isAdic hI.1
    (idealOfDefinition_isAdic_of_isAdicRing hR I hI)⟩, hR.2.2, hR.2.1⟩

/-- The neighbourhood filter of zero in an adic topological ring is countably generated: the
powers of an ideal of definition form a countable basis of it. -/
public lemma countablyGenerated_nhds_of_isAdicRing
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hR : TopologicalRing.IsAdic R) :
    (nhds (0 : R)).IsCountablyGenerated := by
  obtain ⟨I, _, hI⟩ := hR.1
  exact hI.hasBasis_nhds_zero.isCountablyGenerated

/-- In an adic topological ring every ideal of definition is a weak ideal of definition. -/
public lemma weakIdealOfDefinition_of_isAdicRing
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hR : TopologicalRing.IsAdic R)
    (I : Ideal R) (hI : TopologicalRing.IsIdealOfDefinition I) :
    TopologicalRing.IsWeakIdealOfDefinition I := by
  exact isWeakIdealOfDefinition_of_isAdic hI.1 (idealOfDefinition_isAdic_of_isAdicRing hR I hI)

private lemma adicTopology_eq_of_power_cofinal
    {R : Type*} [CommRing R] {I J : Ideal R}
    (hIJ : ∀ n, ∃ m, I ^ m ≤ J ^ n)
    (hJI : ∀ n, ∃ m, J ^ m ≤ I ^ n) : I.adicTopology = J.adicTopology := by
  let tI := I.adicTopology
  let tJ := J.adicTopology
  have hI : @IsTopologicalAddGroup R tI _ := by
    let : TopologicalSpace R := tI
    exact (Ideal.ringFilterBasis I).isTopologicalRing.isTopologicalAddGroup
  have hJ : @IsTopologicalAddGroup R tJ _ := by
    let : TopologicalSpace R := tJ
    exact (Ideal.ringFilterBasis J).isTopologicalRing.isTopologicalAddGroup
  have hnhds : @nhds R tI 0 = @nhds R tJ 0 := by
    ext s
    rw [I.hasBasis_nhds_zero_adic.mem_iff, J.hasBasis_nhds_zero_adic.mem_iff]
    constructor
    · rintro ⟨n, -, hns⟩
      obtain ⟨m, hm⟩ := hJI n
      exact ⟨m, trivial, fun _ hx => hns (hm hx)⟩
    · rintro ⟨n, -, hns⟩
      obtain ⟨m, hm⟩ := hIJ n
      exact ⟨m, trivial, fun _ hx => hns (hm hx)⟩
  exact IsTopologicalAddGroup.ext hI hJ hnhds

private lemma powers_cofinal_of_isAdic
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {I J : Ideal R} (hI : _root_.IsAdic I) (hJ : _root_.IsAdic J) :
    (∀ n, ∃ m, J ^ m ≤ I ^ n) ∧ (∀ n, ∃ m, I ^ m ≤ J ^ n) := by
  have key {I J : Ideal R} (hI : _root_.IsAdic I) (hJ : _root_.IsAdic J) (n : ℕ) :
      ∃ m, J ^ m ≤ I ^ n := by
    obtain ⟨m, -, hm⟩ := hJ.hasBasis_nhds_zero.mem_iff.mp
      (hI.hasBasis_nhds_zero.mem_iff.mpr ⟨n, trivial, subset_rfl⟩)
    exact ⟨m, fun x hx => hm hx⟩
  exact ⟨key hI hJ, key hJ hI⟩

private lemma mappedIdealOfDefinition_isAdic
    {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLinearTopology B B] (hA : TopologicalRing.IsAdic A)
    (φ : A →+* B) (hadic : RingHom.IsAdic φ)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I) :
    _root_.IsAdic (I.map φ) := by
  rcases hadic with ⟨J, hJ, hJmap⟩
  have hIadic := idealOfDefinition_isAdic_of_isAdicRing hA I hI
  have hpow := powers_cofinal_of_isAdic hIadic hJ
  have hmap {K L : Ideal A} (h : ∀ n, ∃ m, K ^ m ≤ L ^ n) (n : ℕ) :
      ∃ m, (K.map φ) ^ m ≤ (L.map φ) ^ n := by
    obtain ⟨m, hm⟩ := h n
    exact ⟨m, by simpa [Ideal.map_pow] using Ideal.map_mono (f := φ) hm⟩
  exact hJmap.trans (adicTopology_eq_of_power_cofinal (hmap hpow.2) (hmap hpow.1)).symm

private lemma isAdicComplete_of_isAdic_and_complete
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (I : Ideal R) (hI : _root_.IsAdic I)
    (hcomplete : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R))
    (hT2 : T2Space R) : IsAdicComplete I R := by
  let : IsTopologicalAddGroup R := inferInstance
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact (IsAdic.isAdicComplete_iff hI).2 ⟨hcomplete, hT2⟩

private lemma closure_eq_of_isAdic
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (I : Ideal R) (hI : _root_.IsAdic I) : Ideal.closure I = I := by
  have hopen : IsOpen (I : Set R) := by
    simpa using (isAdic_iff.mp hI).1 1
  exact Ideal.closure_eq_of_isClosed I (I.toAddSubgroup.isClosed_of_isOpen hopen)

private lemma quotientMap_finiteType_iff_of_closure_eq
    {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (I : Ideal A) (hclosure :
      Ideal.closure (I.map φ) = I.map φ) :
    (Ideal.quotientMap (I := I) (I.map φ) φ
      (Ideal.map_le_iff_le_comap.mp (le_refl (I.map φ)))).FiniteType ↔
    (Ideal.quotientMap (I := I) (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FiniteType := by
  let q₁ := Ideal.quotientMap (I := I) (I.map φ) φ
    (Ideal.map_le_iff_le_comap.mp (le_refl (I.map φ)))
  let q₂ := Ideal.quotientMap (I := I) (Ideal.closure (I.map φ)) φ
    (Ideal.map_le_iff_le_comap.mp subset_closure)
  let e := Ideal.quotientEquiv (I.map φ) (Ideal.closure (I.map φ))
    (RingEquiv.refl B) (hclosure.trans (by simp))
  let : Algebra (A ⧸ I) (B ⧸ I.map φ) := q₁.toAlgebra
  let : Algebra (A ⧸ I) (B ⧸ Ideal.closure (I.map φ)) := q₂.toAlgebra
  have he (x : A ⧸ I) : e (algebraMap (A ⧸ I) (B ⧸ I.map φ) x) =
      algebraMap (A ⧸ I) (B ⧸ Ideal.closure (I.map φ)) x := by
    refine Quotient.inductionOn x fun a => ?_
    show e (q₁ (Ideal.Quotient.mk I a)) = q₂ (Ideal.Quotient.mk I a)
    simp [e, q₁, q₂, Ideal.quotientMap_mk]
  let eAlg : (B ⧸ I.map φ) ≃ₐ[A ⧸ I] (B ⧸ Ideal.closure (I.map φ)) :=
    AlgEquiv.ofRingEquiv he
  show Algebra.FiniteType (A ⧸ I) (B ⧸ I.map φ) ↔
    Algebra.FiniteType (A ⧸ I) (B ⧸ Ideal.closure (I.map φ))
  exact ⟨fun h => h.equiv eAlg, fun h => h.equiv eAlg.symm⟩

/-- Condition (3): one ideal of definition induces the target topology, while possibly another
gives finite type on reductions. -/
public abbrev FiniteTypeModuloSomeIdealOfDefinition (φ : A →+* B) : Prop :=
  (∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ _root_.IsAdic (I.map φ)) ∧
    (∃ J : Ideal A, TopologicalRing.IsIdealOfDefinition J ∧
      (Ideal.quotientMap (I := J) (J.map φ) φ
        (Ideal.map_le_iff_le_comap.mp (le_refl (J.map φ)))).FiniteType)

/-- Condition (4): every ideal of definition induces the target topology and gives finite
type on reductions. -/
public abbrev FiniteTypeModuloEveryIdealOfDefinition (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
    (_root_.IsAdic (I.map φ) ∧
      (Ideal.quotientMap (I := I) (I.map φ) φ
        (Ideal.map_le_iff_le_comap.mp (le_refl (I.map φ)))).FiniteType)

local syntax "IAdicallyCompleteRing " term:max term:max : term
local macro_rules
  | `(IAdicallyCompleteRing $R $I) => `(IsAdicComplete $I $R)

/-- Condition (5): for some ideal of definition, the target has its induced adic topology and
is an object of the category of Tag 0AL4. -/
public abbrev FiniteTypeAdicAlgebraForSomeIdeal (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
    _root_.IsAdic (I.map φ) ∧
      (letI : Algebra A B := φ.toAlgebra
       letI : Algebra (A ⧸ I) (B ⧸ I.map φ) :=
         (Ideal.quotientMap (I := I) (I.map φ) φ
           (Ideal.map_le_iff_le_comap.mp (le_refl (I.map φ)))).toAlgebra
       IAdicallyCompleteRing B (I.map φ) ∧
         Algebra.FiniteType (A ⧸ I) (B ⧸ I.map φ))

/-- Condition (6): the target is an object of the category of Tag 0AL4 for every ideal of
definition, with its induced adic topology. -/
public abbrev FiniteTypeAdicAlgebraForEveryIdeal (φ : A →+* B) : Prop :=
  ∀ I : Ideal A, TopologicalRing.IsIdealOfDefinition I →
    (_root_.IsAdic (I.map φ) ∧
      (letI : Algebra A B := φ.toAlgebra
       letI : Algebra (A ⧸ I) (B ⧸ I.map φ) :=
         (Ideal.quotientMap (I := I) (I.map φ) φ
           (Ideal.map_le_iff_le_comap.mp (le_refl (I.map φ)))).toAlgebra
       IAdicallyCompleteRing B (I.map φ) ∧
         Algebra.FiniteType (A ⧸ I) (B ⧸ I.map φ)))

/-- Condition (8): a closed topological algebra quotient presentation by the completion of
a polynomial ring for an ideal of definition of the source. -/
public abbrev HasCompletedPolynomialPresentation (φ : A →+* B) : Prop :=
  ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
    ∃ n : ℕ,
      let P := MvPolynomial (Fin n) A
      let J := I.map (MvPolynomial.C : A →+* P)
      let C := AdicCompletion J P
      letI : TopologicalSpace C :=
        RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin n)
      ∃ K : Ideal C, IsClosed (K : Set C) ∧
        ∃ e : (C ⧸ K) ≃+* B,
          Continuous e ∧ Continuous e.symm ∧
            e.toRingHom.comp ((Ideal.Quotient.mk K).comp
              ((algebraMap P C).comp MvPolynomial.C)) = φ

private theorem restrictedPolynomialTopology_eq_adic
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (I : Ideal R) (_hIopen : IsOpen (I : Set R))
    (hIadic : _root_.IsAdic I) (σ : Type*) :
    let P := MvPolynomial σ R
    let J := I.map (MvPolynomial.C : R →+* P)
    TopologicalRing.restrictedPolynomialTopology R σ = J.adicTopology := by
  let P := MvPolynomial σ R
  let J := I.map (MvPolynomial.C : R →+* P)
  show (TopologicalRing.restrictedPolynomialTopology R σ :
      TopologicalSpace P) = (J.adicTopology : TopologicalSpace P)
  have hpowopen (n : ℕ) : IsOpen ((I ^ n : Ideal R) : Set R) := (isAdic_iff.mp hIadic).1 n
  have hmap (n : ℕ) : (I ^ n).map (MvPolynomial.C : R →+* P) = J ^ n := by
    simp [J, Ideal.map_pow]
  let t₁ := TopologicalRing.restrictedPolynomialTopology R σ
  let t₂ := J.adicTopology
  have h₁ : @IsTopologicalAddGroup P t₁ _ := by
    let : TopologicalSpace P := t₁
    exact
      (TopologicalRing.restrictedPolynomialIsTopologicalRing R σ).isTopologicalAddGroup
  have h₂ : @IsTopologicalAddGroup P t₂ _ := by
    let : TopologicalSpace P := t₂
    exact (Ideal.ringFilterBasis J).isTopologicalRing.isTopologicalAddGroup
  have hnhds : @nhds P t₁ 0 = @nhds P t₂ 0 := by
    let b : RingSubgroupsBasis
        (fun U : {U : Ideal R // IsOpen (U : Set R)} ↦
          (U.1.map (MvPolynomial.C : R →+* P)).toAddSubgroup) := by
      apply RingSubgroupsBasis.of_comm
      · intro U V
        exact ⟨⟨U.1 ⊓ V.1, U.2.inter V.2⟩,
          le_inf (Ideal.map_mono inf_le_left) (Ideal.map_mono inf_le_right)⟩
      · intro U
        refine ⟨U, ?_⟩
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact Ideal.mul_mem_left _ _ hy
      · intro x U
        exact ⟨U, fun y hy => (U.1.map (MvPolynomial.C : R →+* P)).mul_mem_left x hy⟩
    let : Nonempty {U : Ideal R // IsOpen (U : Set R)} := ⟨⟨⊤, isOpen_univ⟩⟩
    have hb := b.hasBasis_nhds_zero
    have hc := J.hasBasis_nhds_zero_adic
    ext s
    rw [hb.mem_iff, hc.mem_iff]
    constructor
    · rintro ⟨U, -, hUs⟩
      obtain ⟨n, -, hn⟩ := hIadic.hasBasis_nhds_zero.mem_iff.mp
        (U.2.mem_nhds U.1.zero_mem)
      refine ⟨n, trivial, ?_⟩
      exact Set.Subset.trans (by rw [← hmap n]; exact Ideal.map_mono hn) hUs
    · rintro ⟨n, -, hns⟩
      refine ⟨⟨I ^ n, hpowopen n⟩, trivial, ?_⟩
      rwa [hmap n]
  exact IsTopologicalAddGroup.ext h₁ h₂ hnhds

private noncomputable def restrictedPolynomialCompletionData
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (I : Ideal R) (hIopen : IsOpen (I : Set R))
    (hIadic : _root_.IsAdic I) (σ : Type*) :
    let P := MvPolynomial σ R
    let J := I.map (MvPolynomial.C : R →+* P)
    letI : WithIdeal P := ⟨J⟩
    let pkg := AdicCompletionBridge.adicAbstractCompletion J (by rfl : IsAdic J)
    letI : UniformSpace (AdicCompletion J P) := pkg.uniformStruct
    letI : T0Space (AdicCompletion J P) := pkg.separation
    letI : UniformSpace
      (TopologicalRing.RestrictedPowerSeries R σ) :=
        TopologicalRing.restrictedPowerSeriesUniformSpace R σ
    Σ e : (TopologicalRing.RestrictedPowerSeries R σ ≃+*
      AdicCompletion J P),
      {_q : {u : (TopologicalRing.RestrictedPowerSeries R σ ≃ᵤ
        AdicCompletion J P) // e.toEquiv = u.toEquiv} //
        ∀ p : P, e (TopologicalRing.polynomialToRestrictedPowerSeries
          R σ p) = algebraMap P (AdicCompletion J P) p} := by
  let P := MvPolynomial σ R
  let J := I.map (MvPolynomial.C : R →+* P)
  letI : WithIdeal P := ⟨J⟩
  have htop := restrictedPolynomialTopology_eq_adic I hIopen hIadic σ
  have hU : TopologicalRing.restrictedPolynomialUniformSpace R σ =
      @WithIdeal.instUniformSpace P _ ⟨J⟩ := by
    apply @UniformSpace.ext P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (@WithIdeal.instUniformSpace P _ ⟨J⟩)
    change @uniformity P
        (TopologicalRing.restrictedPolynomialUniformSpace R σ) =
      @uniformity P (@WithIdeal.instUniformSpace P _ ⟨J⟩)
    change @Filter.comap (P × P) P (fun p : P × P => p.2 + -p.1)
        (@nhds P (TopologicalRing.restrictedPolynomialTopology R σ) 0) =
      @Filter.comap (P × P) P (fun p : P × P => p.2 + -p.1)
        (@nhds P J.adicTopology 0)
    exact congrArg (fun t : TopologicalSpace P =>
      Filter.comap (fun p : P × P => p.2 + -p.1) (@nhds P t 0)) htop
  have hcontU : @UniformContinuous P P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (@WithIdeal.instUniformSpace P _ ⟨J⟩) id :=
    (@le_iff_uniformContinuous_id P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (@WithIdeal.instUniformSpace P _ ⟨J⟩)).mp (le_of_eq hU)
  let eP : @UniformEquiv P P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (@WithIdeal.instUniformSpace P _ ⟨J⟩) :=
    @UniformEquiv.mk P P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (@WithIdeal.instUniformSpace P _ ⟨J⟩) (Equiv.refl P)
      hcontU
      ((@le_iff_uniformContinuous_id P
          (@WithIdeal.instUniformSpace P _ ⟨J⟩)
          (TopologicalRing.restrictedPolynomialUniformSpace R σ)).mp
          (le_of_eq hU.symm))
  letI : CommRing (@UniformSpace.Completion P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)) :=
    TopologicalRing.restrictedPowerSeriesCommRing R σ
  letI : CommRing (@UniformSpace.Completion P (@WithIdeal.instUniformSpace P _ ⟨J⟩)) :=
    inferInstance
  let eC := @UniformSpace.Completion.mapEquiv P
    (TopologicalRing.restrictedPolynomialUniformSpace R σ)
    P (@WithIdeal.instUniformSpace P _ ⟨J⟩) eP
  let mapC : @UniformSpace.Completion P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ) →+*
      @UniformSpace.Completion P (@WithIdeal.instUniformSpace P _ ⟨J⟩) :=
    @UniformSpace.Completion.mapRingHom P (inferInstance : Ring P)
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (TopologicalRing.restrictedPolynomialIsTopologicalRing R σ)
      ((TopologicalRing.restrictedPolynomialRingFilterBasis R σ).isUniformAddGroup)
      P (@WithIdeal.instUniformSpace P _ ⟨J⟩) (inferInstance : Ring P)
      (inferInstance : IsUniformAddGroup P) (inferInstance : IsTopologicalRing P)
      (RingHom.id P)
      (@UniformContinuous.continuous P P
        (TopologicalRing.restrictedPolynomialUniformSpace R σ)
        (@WithIdeal.instUniformSpace P _ ⟨J⟩) id hcontU)
  have hmapC_coe (p : P) : mapC (↑p : @UniformSpace.Completion P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)) =
      (↑p : @UniformSpace.Completion P (@WithIdeal.instUniformSpace P _ ⟨J⟩)) := by
    dsimp only [mapC]
    rw [@UniformSpace.Completion.mapRingHom_apply P (inferInstance : Ring P)
        (TopologicalRing.restrictedPolynomialUniformSpace R σ)
        (TopologicalRing.restrictedPolynomialIsTopologicalRing R σ)
        ((TopologicalRing.restrictedPolynomialRingFilterBasis R σ).isUniformAddGroup)
        P (@WithIdeal.instUniformSpace P _ ⟨J⟩) (inferInstance : Ring P)
        (inferInstance : IsUniformAddGroup P) (inferInstance : IsTopologicalRing P)
        (RingHom.id P) (@UniformContinuous.continuous P P
          (TopologicalRing.restrictedPolynomialUniformSpace R σ)
          (@WithIdeal.instUniformSpace P _ ⟨J⟩) id hcontU)]
    exact @UniformSpace.Completion.map_coe P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      P (@WithIdeal.instUniformSpace P _ ⟨J⟩) (RingHom.id P) hcontU p
  have hmap_eq : (mapC : @UniformSpace.Completion P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ) →
      @UniformSpace.Completion P (@WithIdeal.instUniformSpace P _ ⟨J⟩)) = eC := by
    apply (@UniformSpace.Completion.ext P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ)
      (@UniformSpace.Completion P (@WithIdeal.instUniformSpace P _ ⟨J⟩)) _ _)
    · dsimp only [mapC]
      rw [@UniformSpace.Completion.coe_mapRingHom P (inferInstance : Ring P)
        (TopologicalRing.restrictedPolynomialUniformSpace R σ)
        (TopologicalRing.restrictedPolynomialIsTopologicalRing R σ)
        ((TopologicalRing.restrictedPolynomialRingFilterBasis R σ).isUniformAddGroup)
        P (@WithIdeal.instUniformSpace P _ ⟨J⟩) (inferInstance : Ring P)
        (inferInstance : IsUniformAddGroup P) (inferInstance : IsTopologicalRing P)
        (RingHom.id P) (@UniformContinuous.continuous P P
          (TopologicalRing.restrictedPolynomialUniformSpace R σ)
          (@WithIdeal.instUniformSpace P _ ⟨J⟩) id hcontU)]
      exact @UniformSpace.Completion.continuous_map P
        (TopologicalRing.restrictedPolynomialUniformSpace R σ)
        P (@WithIdeal.instUniformSpace P _ ⟨J⟩) (id : P → P)
    · exact @UniformContinuous.continuous
        (@UniformSpace.Completion P
          (TopologicalRing.restrictedPolynomialUniformSpace R σ))
        (@UniformSpace.Completion P (@WithIdeal.instUniformSpace P _ ⟨J⟩))
        (@UniformSpace.Completion.uniformSpace P
          (TopologicalRing.restrictedPolynomialUniformSpace R σ))
        (@UniformSpace.Completion.uniformSpace P (@WithIdeal.instUniformSpace P _ ⟨J⟩))
        (eC : _ → _) eC.uniformContinuous_toFun
    · intro p
      rw [hmapC_coe p, @UniformSpace.Completion.mapEquiv_coe P
        (TopologicalRing.restrictedPolynomialUniformSpace R σ)
        P (@WithIdeal.instUniformSpace P _ ⟨J⟩) eP p]
      rfl
  have hmap : Function.Bijective mapC := by
    constructor
    · intro x y hxy
      have heq : eC x = eC y := by rw [← hmap_eq]; exact hxy
      exact eC.injective heq
    · intro y
      obtain ⟨x, hx⟩ := eC.surjective y
      exact ⟨x, by rw [hmap_eq]; exact hx⟩
  let eD := RingEquiv.ofBijective mapC hmap
  let pkg := AdicCompletionBridge.adicAbstractCompletion J (by rfl : IsAdic J)
  letI : UniformSpace (AdicCompletion J P) := pkg.uniformStruct
  letI : T0Space (AdicCompletion J P) := pkg.separation
  letI : UniformSpace
    (TopologicalRing.RestrictedPowerSeries R σ) :=
      TopologicalRing.restrictedPowerSeriesUniformSpace R σ
  let ringE := eD.trans (uniformCompletionRingEquiv J)
  let pkg₀ : AbstractCompletion P :=
    @UniformSpace.Completion.cPkg P (@WithIdeal.instUniformSpace P _ ⟨J⟩)
  letI : UniformSpace pkg.space := pkg.uniformStruct
  let uniformE : @UniformSpace.Completion P
      (TopologicalRing.restrictedPolynomialUniformSpace R σ) ≃ᵤ
        pkg.space :=
    eC.trans (AbstractCompletion.compareEquiv pkg₀ pkg)
  have heq : ringE.toEquiv = uniformE.toEquiv := by
    apply Equiv.ext
    intro x
    change uniformCompletionRingEquiv J (mapC x) =
      (AbstractCompletion.compareEquiv
        pkg₀ pkg) (eC x)
    rw [hmap_eq]
    rfl
  have hcoeff (p : P) : ringE
      (TopologicalRing.polynomialToRestrictedPowerSeries R σ p) =
        algebraMap P (AdicCompletion J P) p := by
    exact (congrArg (uniformCompletionRingEquiv J) (hmapC_coe p)).trans
      (uniformCompletionRingEquiv_coe J p)
  exact ⟨ringE, ⟨⟨uniformE, heq⟩, hcoeff⟩⟩

private theorem polynomialCompletionPkgTopology_eq
    {A : Type*} [CommRing A] (I : Ideal A) (σ : Type*) :
    let P := MvPolynomial σ A
    let J := I.map (MvPolynomial.C : A →+* P)
    letI : WithIdeal P := ⟨J⟩
    let C := AdicCompletion J P
    let pkg := AdicCompletionBridge.adicAbstractCompletion J (by rfl : IsAdic J)
    @UniformSpace.toTopologicalSpace C pkg.uniformStruct =
      RestrictedPowerSeries.polynomialCompletionLimitTopology I σ := by
  let P := MvPolynomial σ A
  let J := I.map (MvPolynomial.C : A →+* P)
  let C := AdicCompletion J P
  let : WithIdeal P := ⟨J⟩
  let pkg := AdicCompletionBridge.adicAbstractCompletion J (by rfl : IsAdic J)
  let : UniformSpace C := pkg.uniformStruct
  let tPkg : TopologicalSpace C := @UniformSpace.toTopologicalSpace C pkg.uniformStruct
  let Q₁ := ∀ n : ℕ, P ⧸ (J ^ n • (⊤ : Submodule P P))
  let Q₂ := ∀ n : ℕ, P ⧸ J ^ n
  let : ∀ n : ℕ, TopologicalSpace (P ⧸ (J ^ n • (⊤ : Submodule P P))) := fun _ => ⊥
  let : ∀ n : ℕ, UniformSpace (P ⧸ (J ^ n • (⊤ : Submodule P P))) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology (P ⧸ (J ^ n • (⊤ : Submodule P P))) := fun _ => ⟨rfl⟩
  let : ∀ n : ℕ, TopologicalSpace (P ⧸ J ^ n) := fun _ => ⊥
  let : ∀ n : ℕ, UniformSpace (P ⧸ J ^ n) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology (P ⧸ J ^ n) := fun _ => ⟨rfl⟩
  let eQ (n : ℕ) : (P ⧸ (J ^ n • (⊤ : Submodule P P))) ≃ (P ⧸ J ^ n) :=
    (Ideal.quotientEquivAlgOfEq P (by ext x; simp)).toEquiv
  let F : Q₁ ≃ Q₂ := Equiv.piCongrRight eQ
  let FH : Q₁ ≃ₜ Q₂ := {
    toEquiv := F
    continuous_toFun := by
      apply continuous_pi
      intro n
      show Continuous (fun x : Q₁ => eQ n (x n))
      exact (continuous_of_discreteTopology).comp (continuous_apply n)
    continuous_invFun := by
      apply continuous_pi
      intro n
      show Continuous (fun x : Q₂ => (eQ n).symm (x n))
      exact (continuous_of_discreteTopology).comp (continuous_apply n) }
  have hval : @Topology.IsInducing C Q₁ tPkg Pi.topologicalSpace Subtype.val := ⟨rfl⟩
  let f : C → Q₂ := fun x n => AdicCompletion.evalₐ J n x
  have hf : (F ∘ (Subtype.val : C → Q₁)) = f := by
    funext x n
    show eQ n (x.val n) = AdicCompletion.evalₐ J n x
    rfl
  have hcomp : @Topology.IsInducing C Q₂ tPkg Pi.topologicalSpace
      (F ∘ (Subtype.val : C → Q₁)) := FH.isInducing.comp hval
  have hPkg : tPkg = @TopologicalSpace.induced C Q₂ f Pi.topologicalSpace := by
    calc
      tPkg = @TopologicalSpace.induced C Q₂
          (F ∘ (Subtype.val : C → Q₁)) Pi.topologicalSpace := hcomp.eq_induced
      _ = @TopologicalSpace.induced C Q₂ f Pi.topologicalSpace :=
        congrArg (fun g : C → Q₂ => TopologicalSpace.induced g Pi.topologicalSpace) hf
  exact hPkg

private noncomputable def uniformEquivHomeomorph
    {X Y : Type*} [uX : UniformSpace X] [uY : UniformSpace Y]
    (e : X ≃ᵤ Y) (tY : TopologicalSpace Y)
    (ht : @UniformSpace.toTopologicalSpace Y uY = tY) :
    @Homeomorph X Y (@UniformSpace.toTopologicalSpace X uX) tY := by
  refine @Homeomorph.mk X Y _ _ e.toEquiv ?_ ?_
  · rw [← ht]
    exact @UniformContinuous.continuous X Y uX uY
      e.toEquiv e.uniformContinuous_toFun
  · rw [← ht]
    exact @UniformContinuous.continuous Y X uY uX
      e.symm.toEquiv e.uniformContinuous_invFun

private theorem transport_closed_quotient_presentation_forward
    {A X Y B : Type*} [CommRing A] [CommRing X] [TopologicalSpace X]
    [CommRing Y] [TopologicalSpace Y] [CommRing B] [TopologicalSpace B]
    (E : X ≃+* Y) (H : X ≃ₜ Y) (hEH : E.toEquiv = H.toEquiv)
    (f : A →+* X) (g : A →+* Y) (φ : A →+* B)
    (hfg : E.toRingHom.comp f = g) :
    (∃ K : Ideal X, IsClosed (K : Set X) ∧
      ∃ e : (X ⧸ K) ≃+* B, Continuous e ∧ Continuous e.symm ∧
        e.toRingHom.comp ((Ideal.Quotient.mk K).comp f) = φ) →
    (∃ L : Ideal Y, IsClosed (L : Set Y) ∧
      ∃ e : (Y ⧸ L) ≃+* B, Continuous e ∧ Continuous e.symm ∧
        e.toRingHom.comp ((Ideal.Quotient.mk L).comp g) = φ) := by
  rintro ⟨K, hK, e, he, hes, hcomp⟩
  have hHE (x : X) : H x = E x := (congrFun (congrArg Equiv.toFun hEH) x).symm
  let L : Ideal Y := Ideal.map E.toRingHom K
  have hLset : (L : Set Y) = H '' (K : Set X) := by
    ext y
    show y ∈ Ideal.map E.toRingHom K ↔ y ∈ H '' (K : Set X)
    rw [Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hHE x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hHE x).symm⟩
  have hL : IsClosed (L : Set Y) := by
    rw [hLset]
    exact H.isClosedMap _ hK
  let Hq : (X ⧸ K) ≃ₜ (Y ⧸ L) :=
    Homeomorph.Quotient.congr H (fun x y => by
      rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
      rw [hHE x, hHE y]
      show x - y ∈ K ↔ E x - E y ∈ L
      rw [← map_sub, Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective]
      constructor
      · exact fun hx => ⟨x - y, hx, rfl⟩
      · rintro ⟨z, hz, hzeq⟩
        have hz' : z = x - y := E.injective (by simpa using hzeq)
        simpa [hz'] using hz)
  let q : (X ⧸ K) ≃+* (Y ⧸ L) := Ideal.quotientEquiv K L E rfl
  have hHq : Hq.toEquiv = q.toEquiv := by
    refine Equiv.ext fun x => Quotient.inductionOn x fun x => ?_
    show Ideal.Quotient.mk L (H x) = Ideal.Quotient.mk L (E x)
    exact congrArg (Ideal.Quotient.mk L) (hHE x)
  let e' : (Y ⧸ L) ≃+* B := q.symm.trans e
  have hqInv : (q.symm : Y ⧸ L → X ⧸ K) = Hq.symm := by
    funext x
    exact congrFun (congrArg Equiv.toFun (congrArg Equiv.symm hHq.symm)) x
  have hqFun : (q : X ⧸ K → Y ⧸ L) = Hq :=
    congrArg Equiv.toFun hHq.symm
  refine ⟨L, hL, e', ?_, ?_, ?_⟩
  · show Continuous ((e : X ⧸ K → B) ∘ (q.symm : Y ⧸ L → X ⧸ K))
    rw [hqInv]
    exact he.comp Hq.symm.continuous
  · show Continuous ((q : X ⧸ K → Y ⧸ L) ∘ (e.symm : B → X ⧸ K))
    rw [hqFun]
    exact Hq.continuous.comp hes
  · ext a
    have hfa : E.toRingHom (f a) = g a := RingHom.congr_fun hfg a
    have hqmk : q.symm (Ideal.Quotient.mk L (E.toRingHom (f a))) =
        Ideal.Quotient.mk K (f a) := by
      show (K.quotientEquiv L E rfl).symm
        (Ideal.Quotient.mk L (E.toRingHom (f a))) = _
      rw [Ideal.quotientEquiv_symm_mk K L E rfl]
      simp
    show e (q.symm (Ideal.Quotient.mk L (g a))) = φ a
    rw [← hfa, hqmk]
    exact congrArg (fun k : A →+* B => k a) hcomp

private theorem transport_closed_quotient_presentation
    {A X Y B : Type*} [CommRing A] [CommRing X] [TopologicalSpace X]
    [CommRing Y] [TopologicalSpace Y] [CommRing B] [TopologicalSpace B]
    (E : X ≃+* Y) (H : X ≃ₜ Y) (hEH : E.toEquiv = H.toEquiv)
    (f : A →+* X) (g : A →+* Y) (φ : A →+* B)
    (hfg : E.toRingHom.comp f = g) :
    (∃ K : Ideal X, IsClosed (K : Set X) ∧
      ∃ e : (X ⧸ K) ≃+* B, Continuous e ∧ Continuous e.symm ∧
        e.toRingHom.comp ((Ideal.Quotient.mk K).comp f) = φ) ↔
    (∃ L : Ideal Y, IsClosed (L : Set Y) ∧
      ∃ e : (Y ⧸ L) ≃+* B, Continuous e ∧ Continuous e.symm ∧
        e.toRingHom.comp ((Ideal.Quotient.mk L).comp g) = φ) := by
  constructor
  · exact transport_closed_quotient_presentation_forward E H hEH f g φ hfg
  · intro h
    have hfg' : E.symm.toRingHom.comp g = f := by
      ext a
      apply E.injective
      simpa using (RingHom.congr_fun hfg a).symm
    exact transport_closed_quotient_presentation_forward
      E.symm H.symm (congrArg Equiv.symm hEH) g f φ hfg' h

private theorem restrictedPresentation_iff_completed_of_ideal
    {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B) (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (hIadic : _root_.IsAdic I) (hA : TopologicalRing.IsAdic A) :
    TopologicalRing.HasRestrictedPowerSeriesPresentation φ ↔
      HasCompletedPolynomialPresentation φ := by
  have key (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
      (hIadic : _root_.IsAdic I) (n : ℕ) :
      (∃ K : Ideal (TopologicalRing.RestrictedPowerSeries A (Fin n)),
        IsClosed (K : Set (TopologicalRing.RestrictedPowerSeries A (Fin n))) ∧
          ∃ e : (TopologicalRing.RestrictedPowerSeries A (Fin n) ⧸ K) ≃+* B,
            Continuous e ∧ Continuous e.symm ∧
              e.toRingHom.comp ((Ideal.Quotient.mk K).comp
                (TopologicalRing.coeffToRestrictedPowerSeries A (Fin n))) = φ) ↔
        let P := MvPolynomial (Fin n) A
        let J := I.map (MvPolynomial.C : A →+* P)
        let C := AdicCompletion J P
        let : TopologicalSpace C :=
          RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin n)
        ∃ K : Ideal C, IsClosed (K : Set C) ∧
          ∃ e : (C ⧸ K) ≃+* B,
            Continuous e ∧ Continuous e.symm ∧
              e.toRingHom.comp ((Ideal.Quotient.mk K).comp
                ((algebraMap P C).comp MvPolynomial.C)) = φ := by
    let P := MvPolynomial (Fin n) A
    let J := I.map (MvPolynomial.C : A →+* P)
    let C := AdicCompletion J P
    let : TopologicalSpace C :=
      RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin n)
    let : WithIdeal P := ⟨J⟩
    let pkg := AdicCompletionBridge.adicAbstractCompletion J (by rfl : IsAdic J)
    let : UniformSpace C := pkg.uniformStruct
    let d := restrictedPolynomialCompletionData I hI.1 hIadic (Fin n)
    let E := d.1
    let U := d.2.1.1
    let hEU := d.2.1.2
    let hpoly := d.2.2
    let H := uniformEquivHomeomorph U
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I (Fin n))
      (polynomialCompletionPkgTopology_eq I (Fin n))
    let f := TopologicalRing.coeffToRestrictedPowerSeries A (Fin n)
    let g := (algebraMap P C).comp MvPolynomial.C
    have hfg : E.toRingHom.comp f = g := by
      apply RingHom.ext
      intro a
      simpa [f, g, TopologicalRing.coeffToRestrictedPowerSeries,
        RingHom.comp_apply] using hpoly (MvPolynomial.C a)
    exact transport_closed_quotient_presentation E H hEU f g φ hfg
  constructor
  · rintro ⟨n, h⟩
    exact ⟨I, hI, n, (key I hI hIadic n).mp h⟩
  · rintro ⟨I', hI', n, h⟩
    exact ⟨n, (key I' hI' (idealOfDefinition_isAdic_of_isAdicRing hA I' hI') n).mpr h⟩

/-- The eight characterizations of an adic morphism of topologically finite type. -/
@[stacks 0GBW "equivalent_conditions",
  ega "I 10.13.4",
  ega "I 10.13.1" "affine case",
  ega "0 7.5.5" "(a) <=> (c)"]
public theorem adicFiniteType_tfae (φ : A →+* B) (hφ : Continuous φ)
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (hBfg : ∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧ J.FG) :
    List.TFAE [
      RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ,
      RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ,
      FiniteTypeModuloSomeIdealOfDefinition φ,
      FiniteTypeModuloEveryIdealOfDefinition φ,
      FiniteTypeAdicAlgebraForSomeIdeal φ,
      FiniteTypeAdicAlgebraForEveryIdeal φ,
    TopologicalRing.HasRestrictedPowerSeriesPresentation φ,
      HasCompletedPolynomialPresentation φ] := by
  -- `hBfg` is not needed by the proof: the finite generation it asserts on `B` is
  -- recovered from `hB` below. It is named in the Stacks statement, so it is kept
  -- and referenced here rather than renamed away.
  have := hBfg
  obtain ⟨IA, hIA, hIAfg⟩ := hAfg
  have hIAadic := idealOfDefinition_isAdic_of_isAdicRing hA IA hIA
  let : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := hB.2.2
  let : T2Space B := hB.2.1
  have hAfgadic : ∃ I : Ideal A, I.FG ∧ _root_.IsAdic I := ⟨IA, hIAfg, hIAadic⟩
  have hAweak := weaklyAdmissible_of_isAdicRing hA
  have hBweak := weaklyAdmissible_of_isAdicRing hB
  have hAcount := countablyGenerated_nhds_of_isAdicRing hA
  have hANU := TopologicalRing.finiteType_tfae'
    (B := A) (A := B) φ hφ hAweak hBweak hAcount
  tfae_have 1 ↔ 2 := and_congr (RingHom.isAdic_iff_isTaut φ hφ hAfgadic) Iff.rfl
  tfae_have 2 ↔ 7 := hANU.out 3 4
  tfae_have 7 ↔ 8 :=
    restrictedPresentation_iff_completed_of_ideal φ IA hIA hIAadic hA
  tfae_have 3 → 2 := by
    rintro ⟨⟨I, hI, hImap⟩, ⟨J, hJ, hJft⟩⟩
    have hadic : RingHom.IsAdic φ :=
      ⟨I, idealOfDefinition_isAdic_of_isAdicRing hA I hI, hImap⟩
    have hJclosure :=
      closure_eq_of_isAdic (J.map φ) (mappedIdealOfDefinition_isAdic hA φ hadic J hJ)
    exact (hANU.out 1 3).mp
      ((TopologicalRing.finiteTypeModuloEveryWeakIdeal_iff_exists_idealOfDefinition
        φ ⟨IA, hIA⟩).mpr
        ⟨RingHom.isTaut_of_isAdic φ hφ hadic, J, hJ,
          (quotientMap_finiteType_iff_of_closure_eq φ J hJclosure).mp hJft⟩)
  tfae_have 2 → 6 := by
    intro htautFT I hI
    have hadic := (RingHom.isAdic_iff_isTaut φ hφ hAfgadic).mpr htautFT.1
    have hmap := mappedIdealOfDefinition_isAdic hA φ hadic I hI
    have hweak := (hANU.out 1 3).mpr htautFT
    refine ⟨hmap, isAdicComplete_of_isAdic_and_complete (I.map φ) hmap hB.2.2 hB.2.1, ?_⟩
    exact (quotientMap_finiteType_iff_of_closure_eq φ I (closure_eq_of_isAdic _ hmap)).mpr
      (hweak.2 I (weakIdealOfDefinition_of_isAdicRing hA I hI))
  tfae_have 6 → 5 := fun h6 => ⟨IA, hIA, h6 IA hIA⟩
  tfae_have 6 → 4 := by
    intro h6 I hI
    obtain ⟨hmap, -, hft⟩ := h6 I hI
    exact ⟨hmap, hft⟩
  tfae_have 5 → 3 := by
    rintro ⟨I, hI, hmap, -, hft⟩
    exact ⟨⟨I, hI, hmap⟩, I, hI, hft⟩
  tfae_have 4 → 3 := fun h4 => ⟨⟨IA, hIA, (h4 IA hIA).1⟩, IA, hIA, (h4 IA hIA).2⟩
  tfae_finish

end Rig

end
