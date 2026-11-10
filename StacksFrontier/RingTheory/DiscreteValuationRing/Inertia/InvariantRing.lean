module


public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.Invariant.Primes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inertia-invariant ring of a discrete valuation ring

The ring of invariants of the inertia group in the integral closure of a discrete valuation ring
in a finite Galois extension is the integral closure in the inertia fixed field, its localization
below the chosen maximal ideal is étale (Tag 09EH), and the residue extension above it is purely
inseparable.
-/

@[expose] public section

open scoped Pointwise

namespace IsDiscreteValuationRing

section RamificationHelpers

/-- A discrete valuation ring has only the two prime ideals. -/
theorem finite_primeSpectrum_of_isDiscreteValuationRing
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    Finite (PrimeSpectrum A) := by
  apply Finite.of_injective (fun x : PrimeSpectrum A ↦ x = ⊥)
  intro x y h
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top x with hx | hx <;>
    rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top y with hy | hy <;>
    simp_all

/-- The decomposition group at a prime has order the product of the ramification index and the
residue degree of that prime. -/
theorem card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    (A B G : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (m : Ideal B) [m.IsPrime] :
    Nat.card (MulAction.stabilizer G m) = m.ramificationIdx A * m.inertiaDeg A := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (m.under A) B G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (m.under A) m G,
    Ideal.inertiaDegIn_eq_inertiaDeg (m.under A) m G,
    ← Algebra.IsInvariant.orbit_eq_primesOver A B G (m.under A) m,
    ← MulAction.index_stabilizer] at h
  have hpos : 0 < (MulAction.stabilizer G m).index := by
    by_contra! hz
    have he := (MulAction.stabilizer G m).index_mul_card
    rw [Nat.eq_zero_of_le_zero hz, zero_mul] at he
    exact Nat.card_pos (α := G) |>.ne' he.symm
  exact Nat.eq_of_mul_eq_mul_left hpos
    ((MulAction.stabilizer G m).index_mul_card.trans h.symm)

section ResidueFields

attribute [local instance] Ideal.Quotient.field

/-- The decomposition group at a maximal ideal has order the order of the inertia group times the
separable degree of the residue extension. -/
private theorem card_stabilizer_eq_card_inertia_mul_finSepDegree
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [SMulCommClass G A B] (p : Ideal A) (P : Ideal B)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Field.finSepDegree (A ⧸ p) (B ⧸ P) := by
  let := Ideal.Quotient.normal G p P
  have heq : Subgroup.index ((P.inertia G).subgroupOf (MulAction.stabilizer G P)) =
      Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [finSepDegree_eq_card_aut_of_normal, ← heq,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv]
  exact ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index.symm

/-- If the inertia group acts as the Galois group of `B` over `C`, then it is its own decomposition
group and its own inertia group, and the residue extension of `C ⧸ q` in `B ⧸ P` has trivial
separable degree. -/
private theorem card_inertia_inertia_and_finSepDegree_eq_one
    {B G C : Type*} [CommRing B] [CommRing C] [Algebra C B]
    [Group G] [Finite G] [MulSemiringAction G B] (P : Ideal B) (q : Ideal C)
    [q.IsMaximal] [P.IsMaximal] [P.LiesOver q] [IsGaloisGroup (P.inertia G) C B] :
    Nat.card (MulAction.stabilizer (P.inertia G) P) = Nat.card (P.inertia G) ∧
      Nat.card (P.inertia (P.inertia G)) = Nat.card (P.inertia G) ∧
      Field.finSepDegree (C ⧸ q) (B ⧸ P) = 1 := by
  have hcard : Nat.card (MulAction.stabilizer (P.inertia G) P) = Nat.card (P.inertia G) := by
    rw [top_unique (a := MulAction.stabilizer (P.inertia G) P) fun g _ ↦
      Ideal.inertia_le_stabilizer (M := G) P g.property,
      Nat.card_congr (Subgroup.topEquiv (G := P.inertia G)).toEquiv]
  have hcardi : Nat.card (P.inertia (P.inertia G)) = Nat.card (P.inertia G) := by
    rw [top_unique (a := P.inertia (P.inertia G)) fun g _ ↦
      Ideal.mem_inertia.mpr (Ideal.mem_inertia.mp g.property),
      Nat.card_congr (Subgroup.topEquiv (G := P.inertia G)).toEquiv]
  have hsep := card_stabilizer_eq_card_inertia_mul_finSepDegree (G := P.inertia G) q P
  erw [hcard, hcardi] at hsep
  exact ⟨hcard, hcardi, by nlinarith [Nat.card_pos (α := P.inertia G)]⟩

/-- A ring with finitely many primes is a finitely presented algebra over itself localized at a
prime, since that localization is a localization away from a single element. -/
private theorem finitePresentation_atPrime_of_finite_spectrum
    (R : Type*) [CommRing R] [Finite (PrimeSpectrum R)] (p : Ideal R) [p.IsPrime] :
    Algebra.FinitePresentation R (Localization.AtPrime p) := by
  classical
  let T := {q : PrimeSpectrum R // ¬ q.asIdeal ≤ p}
  have hex (q : T) : ∃ x : R, x ∈ q.1.asIdeal ∧ x ∉ p := IsConcreteLE.not_le_iff_exists.mp q.2
  choose x hx hxp using hex
  let := Fintype.ofFinite T
  let f := ∏ q : T, x q
  have hfp : f ∉ p := by
    simpa only [f, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists] using hxp
  have hpow : ∀ s ∈ p.primeCompl, ∃ m ∈ Submonoid.powers f, s ∣ m := by
    intro s hs
    have hf : f ∈ (Ideal.span ({s} : Set R)).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro q hq
      have hnot : ¬ q ≤ p := fun h ↦ hs (h (Ideal.subset_span (Set.mem_singleton s) |> hq.1))
      let q' : T := ⟨⟨q, hq.2⟩, hnot⟩
      exact q.mem_of_dvd (Finset.dvd_prod_of_mem x (Finset.mem_univ q')) (hx q')
    obtain ⟨n, hn⟩ := hf
    exact ⟨f ^ n, ⟨n, rfl⟩, Ideal.mem_span_singleton.mp hn⟩
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : IsLocalization.Away f (Localization.AtPrime p) :=
    (IsLocalization.iff_of_le_of_exists_dvd
      (Submonoid.powers f) p.primeCompl hle hpow).mpr inferInstance
  exact IsLocalization.Away.finitePresentation f

/-- A finite flat algebra with finitely many primes and separable residue extension is étale at a
prime of ramification index one. -/
theorem etale_atPrime_of_ramificationIdx_eq_one
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [Module.Finite A C] [Module.Flat A C]
    [Finite (PrimeSpectrum C)]
    (p : Ideal A) (q : Ideal C) [p.IsMaximal] [q.IsMaximal] [q.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (C ⧸ q)] (he : q.ramificationIdx A = 1) :
    Algebra.Etale A (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FinitePresentation A C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmap : p.map (algebraMap A (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff] at he
    simpa only [← q.over_def p] using he
  have : Algebra.IsUnramifiedAt A q :=
    (Algebra.isUnramifiedAt_iff_map_eq A p q).mpr ⟨inferInstance, hmap⟩
  have : Algebra.IsEtaleAt A q := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q
  have : Algebra.FinitePresentation C (Localization.AtPrime q) :=
    finitePresentation_atPrime_of_finite_spectrum C q
  have : Algebra.FinitePresentation A (Localization.AtPrime q) :=
    Algebra.FinitePresentation.trans A C (Localization.AtPrime q)
  exact ⟨inferInstance, inferInstance⟩

/-- In a tower where the inertia group acts as the whole Galois group upstairs, the intermediate
ring is unramified over the base at the contracted prime: the ramification index is one and the
residue extension is separable. -/
@[sga "7 I 0.3" "partial"]
private theorem ramificationIdx_eq_one_and_isSeparable_of_inertia
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) (P : Ideal B) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p]
    (C : Type*) [CommRing C] [IsDomain C] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] [Module.Finite A C] [Module.Finite C B] [Module.Flat C B]
    [IsGaloisGroup (P.inertia G) C B]
    (q : Ideal C) [q.IsMaximal] [q.LiesOver p] [P.LiesOver q] :
    q.ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ p) (C ⧸ q) := by
  obtain ⟨hcard, hcardi, hsep1⟩ := card_inertia_inertia_and_finSepDegree_eq_one (G := G) P q
  have : IsScalarTower (A ⧸ p) (C ⧸ q) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change Ideal.Quotient.mk P (algebraMap A B a) =
        Ideal.Quotient.mk P (algebraMap C B (algebraMap A C a))
      rw [← IsScalarTower.algebraMap_apply A C B])
  have htower := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic
    (A ⧸ p) (C ⧸ q) (B ⧸ P)
  rw [hsep1, mul_one] at htower
  have hupper := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg C B (P.inertia G) P
  erw [hcard] at hupper
  have htotal := card_stabilizer_eq_ramificationIdx_mul_inertiaDeg A B G P
  rw [card_stabilizer_eq_card_inertia_mul_finSepDegree p P, hupper,
    Ideal.ramificationIdx_tower (R := A) q P, Ideal.inertiaDeg_tower (R := A) q P,
    ← htower] at htotal
  have hepos := P.ramificationIdx_pos C
  have hfpos := P.inertiaDeg_pos C
  have hcancel : Field.finSepDegree (A ⧸ p) (C ⧸ q) =
      q.ramificationIdx A * q.inertiaDeg A := by
    nlinarith
  have hle := Field.finSepDegree_le_finrank (A ⧸ p) (C ⧸ q)
  rw [← Ideal.inertiaDeg_eq_of_isMaximal p q] at hle
  have heq : q.ramificationIdx A = 1 := by
    have := q.ramificationIdx_pos A
    have := q.inertiaDeg_pos A
    nlinarith
  refine ⟨heq, (Field.finSepDegree_eq_finrank_iff (A ⧸ p) (C ⧸ q)).mp ?_⟩
  rw [hcancel, heq, one_mul, Ideal.inertiaDeg_eq_of_isMaximal p q]

end ResidueFields

end RamificationHelpers

/-- **Stacks Tag 09EH.** The subring of the integral closure fixed by the inertia group is the
integral closure in the fixed field, and its localization at the prime below the chosen maximal
ideal is étale over the original discrete valuation ring. -/
@[stacks 09EH, sga "7 I 0.3" "partial"]
theorem inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B :=
      ⟨fun g a b ↦ by
        simp only [Algebra.smul_def]
        change galRestrict A K L B g (algebraMap A B a * b) =
          algebraMap A B a * galRestrict A K L B g b
        rw [map_mul, AlgEquiv.commutes]⟩
    let I := P.inertia Gal(L/K)
    let B' := FixedPoints.subalgebra A B I
    let L' := IntermediateField.fixedField I
    let inclusion : B' →ₐ[A] L := (integralClosure A L).val.comp B'.val
    let iota : B' →ₐ[A] L' :=
      inclusion.codRestrict (L'.toSubalgebra.restrictScalars A) (fun b ↦ by
        change (inclusion b : L) ∈ L'
        rw [IntermediateField.mem_fixedField_iff]
        intro g hg
        exact (algebraMap_galRestrict_apply A g (b : B)).symm.trans
          (congrArg (algebraMap B L) (b.property ⟨g, hg⟩)))
    letI := iota.toAlgebra
    IsIntegralClosure B' A L' ∧
      Algebra.Etale A (Localization.AtPrime (P.under B')) := by
  dsimp only
  let B := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L B
  let : SMulCommClass Gal(L/K) A B :=
    ⟨fun g a b ↦ by
      simp only [Algebra.smul_def]
      change galRestrict A K L B g (algebraMap A B a * b) =
        algebraMap A B a * galRestrict A K L B g b
      rw [map_mul, AlgEquiv.commutes]⟩
  let I := P.inertia Gal(L/K)
  let B' := FixedPoints.subalgebra A B I
  let L' := IntermediateField.fixedField I
  let inclusion : B' →ₐ[A] L := (integralClosure A L).val.comp B'.val
  let iota : B' →ₐ[A] L' :=
    inclusion.codRestrict (L'.toSubalgebra.restrictScalars A) (fun b ↦ by
      change (inclusion b : L) ∈ L'
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (algebraMap_galRestrict_apply A g (b : B)).symm.trans
        (congrArg (algebraMap B L) (b.property ⟨g, hg⟩)))
  let := iota.toAlgebra
  have hIC : IsIntegralClosure B' A L' := by
    have hiota : Function.Injective iota := by
      intro x y h
      have hL := congrArg L'.val h
      change inclusion x = inclusion y at hL
      exact Subtype.ext (Subtype.ext hL)
    refine ⟨hiota, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
    · obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hx.map L'.val)
      have hfix : ∀ g : I, g • b = b := by
        intro g
        apply Subtype.ext
        change algebraMap B L (galRestrict A K L B (g : Gal(L/K)) b) = algebraMap B L b
        rw [algebraMap_galRestrict_apply A (g : Gal(L/K)) (b : B), hb]
        exact x.property g
      exact ⟨⟨b, hfix⟩, Subtype.ext hb⟩
    · rintro ⟨b, rfl⟩
      exact ((isIntegral_algHom_iff B'.val Subtype.val_injective).mp
        (Algebra.IsIntegral.isIntegral (b : B))).map iota
  let := hIC
  refine ⟨hIC, ?_⟩
  have : IsScalarTower A B' L' := IsScalarTower.of_algebraMap_eq fun a ↦ (iota.commutes a).symm
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : Module.Finite A B' := IsIntegralClosure.finite A K L' B'
  have : IsDedekindDomain B' := IsIntegralClosure.isDedekindDomain A K L' B'
  have : Module.Finite B' B := Module.Finite.right A B' B
  have : Module.IsTorsionFree B' B := inferInstance
  have : Module.Flat B' B := inferInstance
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := Module.IsTorsionFree.of_faithfulSMul B A L
  have : Module.Flat A B := inferInstance
  have : IsGaloisGroup Gal(L/K) A B := IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
  have : IsGaloisGroup I B' B := inferInstance
  let p := P.under A
  let q := P.under B'
  have : p.IsMaximal := Ideal.IsMaximal.under A P
  have : q.IsMaximal := Ideal.IsMaximal.under B' P
  have : q.LiesOver p := Ideal.LiesOver.tower_bot P q p
  obtain ⟨he, hsep⟩ := ramificationIdx_eq_one_and_isSeparable_of_inertia
    (G := Gal(L/K)) p P B' q
  have : Finite (PrimeSpectrum A) := finite_primeSpectrum_of_isDiscreteValuationRing A
  have : Finite (PrimeSpectrum B') := Algebra.QuasiFinite.finite_primeSpectrum A B'
  have : Module.IsTorsionFree A B' := Module.IsTorsionFree.of_faithfulSMul B' A B
  exact etale_atPrime_of_ramificationIdx_eq_one p q he

/-- The residue extension above the inertia fixed ring is purely inseparable.

This is the precise upper half of the inertia-field factorization.  It deliberately does not
claim that the upper field extension is totally ramified: over an imperfect residue field a
finite Galois extension may be fiercely ramified, and then this purely inseparable residue
extension is nontrivial.  Total ramification follows only after one separately proves that the
residue map is surjective (equivalently, that this purely inseparable extension is trivial).

Together with
`inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization`, this says that the inertia
fixed field isolates the maximal separable residue extension downstairs, while every residue
extension left upstairs is purely inseparable. -/
theorem inertia_fixedSubalgebra_residue_purelyInseparable
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B :=
      ⟨fun g a b ↦ by
        simp only [Algebra.smul_def]
        change galRestrict A K L B g (algebraMap A B a * b) =
          algebraMap A B a * galRestrict A K L B g b
        rw [map_mul, AlgEquiv.commutes]⟩
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    letI : IsGaloisGroup Gal(L/K) A B :=
      IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
    let I := P.inertia Gal(L/K)
    let B' := FixedPoints.subalgebra A B I
    letI : IsGaloisGroup I B' B := inferInstance
    letI : Algebra.IsIntegral B' B :=
      (inferInstance : IsGaloisGroup I B' B).isInvariant.isIntegral
    let q := P.under B'
    letI : q.IsMaximal := Ideal.IsMaximal.under B' P
    letI : Field (B' ⧸ q) := Ideal.Quotient.field q
    letI : Field (B ⧸ P) := Ideal.Quotient.field P
    IsPurelyInseparable (B' ⧸ q) (B ⧸ P) := by
  dsimp only
  let B := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L B
  let : SMulCommClass Gal(L/K) A B :=
    ⟨fun g a b ↦ by
      simp only [Algebra.smul_def]
      change galRestrict A K L B g (algebraMap A B a * b) =
        algebraMap A B a * galRestrict A K L B g b
      rw [map_mul, AlgEquiv.commutes]⟩
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : IsGaloisGroup Gal(L/K) A B :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
  let I := P.inertia Gal(L/K)
  let B' := FixedPoints.subalgebra A B I
  let : IsGaloisGroup I B' B := inferInstance
  let : Algebra.IsIntegral B' B :=
    (inferInstance : IsGaloisGroup I B' B).isInvariant.isIntegral
  let q := P.under B'
  have hqmax : q.IsMaximal := Ideal.IsMaximal.under B' P
  let : q.IsMaximal := hqmax
  let : q.IsPrime := hqmax.isPrime
  let : P.LiesOver q := ⟨rfl⟩
  let : Field (B' ⧸ q) := Ideal.Quotient.field q
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  exact isPurelyInseparable_of_finSepDegree_eq_one
    (card_inertia_inertia_and_finSepDegree_eq_one (G := Gal(L/K)) P q).2.2

end IsDiscreteValuationRing
