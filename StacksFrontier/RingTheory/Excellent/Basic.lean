module

public import Mathlib
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import StacksFrontier.RingTheory.Catenary.Henselization
import StacksFrontier.RingTheory.Branches.Completion
import StacksFrontier.RingTheory.Catenary.Basic
import StacksFrontier.RingTheory.Nilpotent.Ideal
import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Criteria
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Catenary
public import StacksFrontier.RingTheory.CohenMacaulay.Localization
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.FormalFibres.EssFiniteType
public import StacksFrontier.RingTheory.FormalFibres.Examples
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.Nagata.AnalyticallyUnramified
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Nagata.N1
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.Regular.SingularLocus
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Quasi-excellent and excellent rings

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07QT, 07QU, 07QV, 07QW, 0BJ0.

## Tag 07QT — Excellent rings

A commutative ring is quasi-excellent if it is Noetherian, a G-ring, and J-2. It is excellent
if it is quasi-excellent and universally catenary.

### Main definitions

* `IsQuasiExcellent`: the predicate that a commutative ring is quasi-excellent.
* `IsExcellent`: the predicate that a commutative ring is excellent.

### Main results

There are no results beyond the definitions.

### Implementation notes

The constituent properties are represented by their corresponding predicates for G-rings, J-2
rings, and universally catenary rings.

### References

* [Stacks Project, Tag 07QT](https://stacks.math.columbia.edu/tag/07QT)

## Tag 07QU — Essentially finite-type algebras over excellent rings

An algebra essentially of finite type over a quasi-excellent ring is quasi-excellent, and an
algebra essentially of finite type over an excellent ring is excellent.

### Main definitions

There are no new definitions.

### Main results

* `isQuasiExcellent_and_isExcellent_of_essFiniteType`: quasi-excellence and excellence
  ascend along essentially finite-type algebras.

### Implementation notes

A localization of a finite-type algebra is represented abstractly by
`Algebra.EssFiniteType R S`. The two variants in the source are combined into one conjunction.

### References

* [Stacks Project, Tag 07QU](https://stacks.math.columbia.edu/tag/07QU)

## Tag 07QV — Quasi-excellent rings are Nagata

Every quasi-excellent commutative ring is a Nagata ring.

### Main definitions

There are no new definitions.

### Main results

* `isNagataRing_of_isQuasiExcellent`: a quasi-excellent ring is Nagata.

### Implementation notes

Quasi-excellence is expressed by `IsQuasiExcellent`, and the Nagata property by
`IsNagataRing`.

### References

* [Stacks Project, Tag 07QV](https://stacks.math.columbia.edu/tag/07QV)

## Tag 07QW — Standard classes of excellent rings

Fields, Noetherian complete local rings, the integers, and Dedekind domains whose fraction
fields have characteristic zero are excellent. Excellence is preserved by finite-type ring
extensions.

### Main definitions

There are no new definitions.

### Main results

* `isExcellent_of_standard_classes_and_finiteType` gives the standard classes of
  excellent rings and stability under finite-type extensions.

### Implementation notes

Completeness of a Noetherian local ring is expressed by precompleteness for its maximal ideal,
as in Tags 07PJ and 07PX. The finite-type assertion is stated for every excellent base ring,
which simultaneously gives all the finite-type extensions listed in the source.

### References

* [Stacks Project, Tag 07QW](https://stacks.math.columbia.edu/tag/07QW)

## Tag 0BJ0 — Nagata local rings and geometrically reduced formal fibres

A Noetherian local ring is Nagata exactly when all of its formal fibres are geometrically
reduced over their residue fields.

### Main definitions

There are no new definitions.

### Main results

* `isNagataRing_iff_formalFibers_geometricallyReduced`: the characterization of a
  Noetherian local Nagata ring by geometric reducedness of its formal fibres.

### Implementation notes

The formal fibre at a prime `q` is expressed as
`q.Fiber (AdicCompletion (maximalIdeal A) A)`, namely the base change of the completion of `A`
to the residue field at `q`. This is the tensor-factor-reversed presentation of the formal fibre
used by `FormalFibersHaveAt`.

### References

* [The Stacks Project, Tag 0BJ0](https://stacks.math.columbia.edu/tag/0BJ0)

-/

/-! ### Stacks Tag 07QT -/

section

@[expose] public section

universe u

/-- A commutative ring is quasi-excellent if it is Noetherian, a G-ring, and J-2. -/
@[stacks 07QT "(1)", ega "IV 7.8.2" "(ii), (iii)"]
public def IsQuasiExcellent (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsGRing R ∧ IsJ2 R

/-- A commutative ring is excellent if it is quasi-excellent and universally catenary. -/
@[stacks 07QT "(2)", ega "IV 7.8.2"]
public def IsExcellent (R : Type u) [CommRing R] : Prop :=
  IsQuasiExcellent R ∧ Ring.IsUniversallyCatenary R

end

/-! ### Stacks Tag 07QU -/

section

section

universe u v

private lemma isJ1_of_isLocalization
    (A : Type*) [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (h : IsJ1 A) : IsJ1 B := by
  have hopen := h.preimage (PrimeSpectrum.continuous_comap (algebraMap A B))
  change IsOpen {p : PrimeSpectrum B |
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)}
  convert hopen using 1
  ext p
  let : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
      (p.asIdeal.comap (algebraMap A B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (T := Localization.AtPrime p.asIdeal) p.asIdeal
  let e := IsLocalization.algEquiv
    (p.asIdeal.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (p.asIdeal.comap (algebraMap A B)))
    (Localization.AtPrime p.asIdeal)
  change IsRegularLocalRing (Localization.AtPrime p.asIdeal) ↔
    IsRegularLocalRing (Localization.AtPrime (p.asIdeal.comap (algebraMap A B)))
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun _ => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩

/-- A finite-type algebra `T` over an essentially finite-type `R`-algebra `S` is a localization
of a ring `T₀` that is isomorphic to a finite-type `R`-algebra in the universe of `R`. -/
private lemma exists_isLocalization_of_finiteType
    (R : Type u) (S : Type v) (T : Type v) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra.EssFiniteType R S] [Algebra S T] [Algebra.FiniteType S T] :
    ∃ (T₀ : Type v) (_ : CommRing T₀) (M : Submonoid T₀) (_ : Algebra T₀ T)
      (_ : IsLocalization M T) (T₁ : Type u) (_ : CommRing T₁) (_ : Algebra R T₁)
      (_ : Algebra.FiniteType R T₁), Nonempty (T₁ ≃+* T₀) := by
  let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType S T := Algebra.EssFiniteType.of_finiteType S T
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.comp R S T
  obtain ⟨T₀, M, hT₀, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra R T).mp inferInstance
  have : Small.{u} T₀ := Algebra.FiniteType.small (R := R) (S := T₀)
  exact ⟨T₀, inferInstance, M, inferInstance, hloc, Shrink.{u} T₀, inferInstance, inferInstance,
    Algebra.FiniteType.equiv inferInstance (Shrink.algEquiv R T₀).symm,
    ⟨(Shrink.algEquiv R T₀).toRingEquiv⟩⟩

private lemma isJ2_of_essFiniteType
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S]
    (hR : IsJ2 R) : IsJ2 S := by
  intro T _ _ _
  obtain ⟨T₀, _, M, _, _, T₁, _, _, _, ⟨e⟩⟩ := exists_isLocalization_of_finiteType R S T
  exact isJ1_of_isLocalization T₀ M T (isJ1_of_ringEquiv e (hR T₁))

private lemma isCatenary_of_isLocalization_07qu
    (A : Type*) [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (hA : Ring.IsCatenary A) : Ring.IsCatenary B := by
  let e : PrimeSpectrum B ↪o PrimeSpectrum A :=
    { toFun := PrimeSpectrum.comap (algebraMap A B)
      inj' := PrimeSpectrum.localization_comap_injective B M
      map_rel_iff' := by
        intro p q
        change p.asIdeal.under A ≤ q.asIdeal.under A ↔ p.asIdeal ≤ q.asIdeal
        refine ⟨fun hpq => ?_, Ideal.comap_mono (f := algebraMap A B)⟩
        rw [← IsLocalization.map_under M B p.asIdeal,
          ← IsLocalization.map_under M B q.asIdeal]
        exact Ideal.map_mono hpq }
  have he : (Set.range e).OrdConnected := by
    rw [show Set.range e =
      {p : PrimeSpectrum A | Disjoint (M : Set A) p.asIdeal} from
        PrimeSpectrum.localization_comap_range B M]
    refine ⟨?_⟩
    rintro _ _ q hq x ⟨-, hxq⟩
    change Disjoint (M : Set A) q.asIdeal at hq
    change Disjoint (M : Set A) x.asIdeal
    rw [Set.disjoint_left] at hq ⊢
    intro a ha hax
    exact hq ha (hxq hax)
  intro p q hpq
  exact Stacks.Catenary.SurjectiveImage.IsCatenaryAt.of_image e he
    (hA (e p) (e q) (e.monotone hpq))

@[ega "IV 7.8.2" "Direction"]
private lemma isUniversallyCatenary_of_essFiniteType
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S]
    (hR : Ring.IsUniversallyCatenary R) : Ring.IsUniversallyCatenary S := by
  intro T _ _ _
  obtain ⟨T₀, _, M, _, _, T₁, _, _, _, ⟨e⟩⟩ := exists_isLocalization_of_finiteType R S T
  exact isCatenary_of_isLocalization_07qu T₀ M T
    (StacksDraft.Catenary.isCatenary_of_ringEquiv e (hR T₁))

/-- An algebra essentially of finite type over a quasi-excellent ring is quasi-excellent, and
an algebra essentially of finite type over an excellent ring is excellent. -/
@[stacks 07QU, ega "IV 7.8.3" "more general", ega "IV 7.8.4" "more general"]
public theorem isQuasiExcellent_and_isExcellent_of_essFiniteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    (IsQuasiExcellent R → IsQuasiExcellent S) ∧
      (IsExcellent R → IsExcellent S) := by
  have hq : IsQuasiExcellent R → IsQuasiExcellent S := by
    rintro ⟨_, hg, hj2⟩
    exact ⟨Algebra.EssFiniteType.isNoetherianRing R S, isGRing_of_essFiniteType hg,
      isJ2_of_essFiniteType R S hj2⟩
  exact ⟨hq, fun h => ⟨hq h.1, isUniversallyCatenary_of_essFiniteType R S h.2⟩⟩

end

end

/-! ### Stacks Tag 07QV -/

section

section

universe u

private theorem exists_isIntegrallyClosed_away_of_isJ1
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hA : IsJ1 A) :
    ∃ f : A, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ∈ {x : PrimeSpectrum A |
      IsRegularLocalRing (Localization.AtPrime x.asIdeal)} := by
    change IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A))
    let : Field (Localization.AtPrime (⊥ : Ideal A)) := IsField.toField <| by
      simp [IsLocalRing.isField_iff_maximalIdeal_eq,
        ← Localization.AtPrime.map_eq_maximalIdeal]
    infer_instance
  obtain ⟨V, ⟨f, rfl⟩, hηf, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hη hA
  have hf : f ≠ 0 := by simpa [η] using hηf
  refine ⟨f, hf, ?_⟩
  have : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain _ hf
  have : IsRegularRing (Localization.Away f) := (isRegularRing_iff.mpr fun p hp => by
    have hfc : f ∉ p.comap (algebraMap A (Localization.Away f)) := by
      rw [Ideal.mem_comap]
      intro hf
      exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hf
        (IsLocalization.Away.algebraMap_isUnit f))
    have hreg : IsRegularLocalRing
        (Localization.AtPrime (p.comap (algebraMap A (Localization.Away f)))) :=
      hfV (show (⟨p.comap (algebraMap A (Localization.Away f)), inferInstance⟩ :
        PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen f by simpa using hfc)
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Submonoid.powers f) p).toRingEquiv)
  exact IsRegularRing.isIntegrallyClosed _

@[ega "IV 7.8.4" "partial, special case"]
private theorem isN1_of_isQuasiExcellent_domain
    (A : Type u) [CommRing A] [IsDomain A]
    (hA : IsQuasiExcellent A) : IsN1 A := by
  have : IsNoetherianRing A := hA.1
  refine (isN1_iff_exists_isIntegrallyClosed_away_and_forall_isN1_atPrime A).2
    ⟨exists_isIntegrallyClosed_away_of_isJ1 A (hA.2.2 A), fun m hm => ?_⟩
  let B := Localization.AtPrime m
  let C := AdicCompletion (IsLocalRing.maximalIdeal B) B
  exact (isAnalyticallyUnramified_iff_minimalPrimes_and_isN1 B).2
    (isReduced_of_isRegularRingHom (algebraMap B C) (hA.2.1.2 m))

/-- **Stacks 07QV.** A quasi-excellent commutative ring is a Nagata ring. -/
@[stacks 07QV, ega "IV 7.8.3" "more general", ega "IV 7.8.4" "(iii)"]
public theorem isNagataRing_of_isQuasiExcellent {R : Type u} [CommRing R]
    (hR : IsQuasiExcellent R) : IsNagataRing R := by
  have : IsNoetherianRing R := hR.1
  apply ((isNagataRing_tfae (R := R)).out 3 1).mp
  refine ⟨isUniversallyJapanese_of_finiteType_isN1 R ?_, inferInstance⟩
  intro S _ _ _ _
  exact isN1_of_isQuasiExcellent_domain S
    (isQuasiExcellent_and_isExcellent_of_essFiniteType.1 hR)

end

end

/-! ### Stacks Tag 07QW -/

section

section

universe u v

@[ega "IV 5.6.4" "special case"]
private theorem isUniversallyCatenary_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R] : Ring.IsUniversallyCatenary R :=
  isUniversallyCatenary_of_forall_isMaximalCohenMacaulay R fun p _ =>
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (Localization.AtPrime p)).2

/-- **Stacks 07QW.** Fields, Noetherian complete local rings, the integers, and Dedekind domains
whose fraction fields have characteristic zero are excellent; moreover, every finite-type
algebra over an excellent ring is excellent. -/
@[stacks 07QW,
  ega "IV 7.8.3" "(iii), part of (ii)",
  ega "IV 7.8.6" "(i), affine case",
  ega "IV 6.12.6" "special case", sga "3 VIB 10.10" "more general"]
public theorem isExcellent_of_standard_classes_and_finiteType :
    (∀ (K : Type u) [Field K], IsExcellent K) ∧
      (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
        [IsPrecomplete (IsLocalRing.maximalIdeal R) R], IsExcellent R) ∧
      IsExcellent ℤ ∧
      (∀ (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)],
        IsExcellent R) ∧
      (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
        [Algebra.FiniteType R S], IsExcellent R → IsExcellent S) := by
  obtain ⟨hJField, hJComplete, hJInt, _, _, hJDedekind, _⟩ :=
    isJ2_of_standard_classes_and_finiteType.{u, v}
  obtain ⟨hGField, hGComplete, hGInt, hGDedekind, _⟩ :=
    isGRing_basic_examples.{u, v}
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K _
    exact ⟨⟨(hGField K).1, hGField K, hJField K⟩, isUniversallyCatenary_of_isRegularRing K⟩
  · intro R _ _ _ _
    exact ⟨⟨(hGComplete R).1, hGComplete R, hJComplete R⟩,
      isUniversallyCatenary_of_isPrecomplete_maximalIdeal R⟩
  · exact ⟨⟨hGInt.1, hGInt, hJInt⟩, isUniversallyCatenary_of_isRegularRing ℤ⟩
  · intro R _ _ _
    have : CharZero R := (algebraMap R (FractionRing R)).charZero
    exact ⟨⟨(hGDedekind R).1, hGDedekind R, hJDedekind R⟩,
      isUniversallyCatenary_of_isRegularRing R⟩
  · intro R S _ _ _ _ hR
    exact (isQuasiExcellent_and_isExcellent_of_essFiniteType
      (R := R) (S := S)).2 hR

end

end

/-! ### Stacks Tag 0BJ0 -/

section

section

open IsLocalRing
open scoped TensorProduct

universe u v

@[ega "IV 7.8.3" "(v), (vii): Â is reduced"]
private lemma isReduced_tensor_completion_of_isNagataRing
    {A : Type u} {S : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing S] [IsDomain S] [Algebra A S] [Module.Finite A S] (hA : IsNagataRing A) :
    IsReduced (S ⊗[A] AdicCompletion (maximalIdeal A) A) := by
  have h := (isNagataRing_tfae_isAnalyticallyUnramified.{u, v, u}
    (R := A)).out 1 2
  -- Lift the finite algebra to the test universe required by Tag 0BI2.
  have : IsDomain (ULift.{u} S) := ULift.ringEquiv.toMulEquiv.isDomain S
  have : IsReduced (ULift.{u} S ⊗[A] AdicCompletion (maximalIdeal A) A) :=
    isReduced_tensor_completion_iff.mpr (h.mp hA (ULift.{u} S))
  let e := Algebra.TensorProduct.congr (ULift.algEquiv : ULift.{u} S ≃ₐ[A] S)
    (AlgEquiv.refl (R := A) (A₁ := AdicCompletion (maximalIdeal A) A))
  exact isReduced_of_injective e.symm e.symm.injective

private lemma isReduced_tensor_completion_finite_extension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNagataRing A) (p : Ideal A) [p.IsPrime]
    (K : Type u) [Field K] [Algebra p.ResidueField K] [Module.Finite p.ResidueField K]
    [Algebra (A ⧸ p) K] [IsScalarTower (A ⧸ p) p.ResidueField K]
    [Algebra A K] [IsScalarTower A (A ⧸ p) K] :
    IsReduced (K ⊗[A] AdicCompletion (maximalIdeal A) A) := by
  let B := integralClosure (A ⧸ p) K
  have : Module.Finite (A ⧸ p) B :=
    module_finite_integralClosure_of_isJapaneseRing (hA.2 p) p.ResidueField K
  let : Algebra A B := ((algebraMap (A ⧸ p) B).comp (algebraMap A (A ⧸ p))).toAlgebra
  have : IsScalarTower A (A ⧸ p) B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A K a = algebraMap (A ⧸ p) K (algebraMap A (A ⧸ p) a)
    exact IsScalarTower.algebraMap_apply A (A ⧸ p) K a
  have : Module.Finite A B := Module.Finite.trans (A ⧸ p) B
  have : IsFractionRing B K :=
    IsIntegralClosure.isFractionRing_of_finite_extension (A ⧸ p) p.ResidueField K B
  have : IsReduced (B ⊗[A] AdicCompletion (maximalIdeal A) A) :=
    isReduced_tensor_completion_of_isNagataRing hA
  let T := B ⊗[A] AdicCompletion (maximalIdeal A) A
  let : Algebra T (K ⊗[B] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors B)) (K ⊗[B] T) :=
    IsLocalization.tensorRight (S := T) (A := K) (nonZeroDivisors B)
  have : IsReduced (K ⊗[B] T) :=
    isReduced_localizationPreserves (R := T)
      (Algebra.algebraMapSubmonoid T (nonZeroDivisors B)) (K ⊗[B] T) inferInstance
  let e := Algebra.TensorProduct.cancelBaseChange A B K K (AdicCompletion (maximalIdeal A) A)
  exact isReduced_of_injective e.symm e.symm.injective

/-- **Stacks 0BJ0.** A Noetherian local ring is Nagata if and only if all its formal fibres are
geometrically reduced. -/
@[stacks 0BJ0,
  ega "IV 7.6.4" "local case, a'')<=>b)",
  ega "IV 7.7.3" "A local Noetherian",
  ega "IV 7.7.4" "formal fibres clause"]
public theorem isNagataRing_iff_formalFibers_geometricallyReduced
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsNagataRing A ↔
      ∀ q : PrimeSpectrum A,
        Algebra.IsGeometricallyReduced q.asIdeal.ResidueField
          (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A)) := by
  constructor
  · intro hA q
    let k := q.asIdeal.ResidueField
    let C := AdicCompletion (maximalIdeal A) A
    rw [Algebra.isGeometricallyReduced_field_iff]
    let F := k ⊗[A] C
    suffices h : IsReduced (F ⊗[k] AlgebraicClosure k) from
      isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) F)
        (Algebra.TensorProduct.comm k (AlgebraicClosure k) F).injective
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    let : Field B := B.isField_of_algebraic.toField
    have : Algebra.FiniteType k B := ⟨B.fg_top.mpr hB⟩
    have : Algebra.IsIntegral k B := Algebra.IsIntegral.of_injective B.val Subtype.val_injective
    have : Module.Finite k B := Algebra.IsIntegral.finite
    let : Algebra (A ⧸ q.asIdeal) B :=
      ((algebraMap k B).comp (algebraMap (A ⧸ q.asIdeal) k)).toAlgebra
    have : IsScalarTower (A ⧸ q.asIdeal) k B := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A B :=
      ((algebraMap (A ⧸ q.asIdeal) B).comp (algebraMap A (A ⧸ q.asIdeal))).toAlgebra
    have : IsScalarTower A (A ⧸ q.asIdeal) B := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower A k B := IsScalarTower.of_algebraMap_eq' rfl
    have : IsReduced (B ⊗[A] C) := isReduced_tensor_completion_finite_extension hA q.asIdeal B
    let eB := (Algebra.TensorProduct.comm k F B).trans
      (Algebra.TensorProduct.cancelBaseChange A k k B C)
    exact isReduced_of_injective eB eB.injective
  · intro hA
    have h := (isNagataRing_tfae_isAnalyticallyUnramified.{u, u, u}
      (R := A)).out 1 2
    apply h.mpr
    intro S _ _ _ _ q _
    exact isReduced_tensor_completion_iff.mp
      (isReduced_tensor_completion_of_formalFibers hA) q

end

end

end
