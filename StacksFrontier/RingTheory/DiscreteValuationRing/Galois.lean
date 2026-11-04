module

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.Invariant.Primes

/-!
# Galois extensions and ramification of a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K`, let `L / K` be a finite Galois
extension with Galois group `Gal(L/K)`, and let `B` be the integral closure of `A` in `L`. The
Galois group acts on `B` and permutes its maximal ideals transitively, so the ramification
indices and the residue degrees of these maximal ideals are constant: writing `n` for their
number and `e` and `f` for the two common values, the degree of `L / K` is `n * e * f`.

The stabilizer of a maximal ideal `m` of `B` is its *decomposition group*, and the kernel of the
induced action on the residue field `κ(m)` is its *inertia group*. The residue extension
`κ(m) / κ_A` is always normal and the decomposition group surjects onto its relative automorphism
group; separability at one maximal ideal is equivalent to separability at all of them, and in
that case the residue extension is Galois. The inertia group itself is an extension of a *wild*
inertia group, which acts trivially on `m / m²`, by a cyclic *tame* quotient identified with the
group of `e`-th roots of unity in `κ(m)`: the identification is the *inertia character*, which
sends an inertia element `σ` to the residue of `σ(x) / x` for `x ∈ m \ m²`.

## Main results

* `IsDiscreteValuationRing.galAction_transitive_on_maximalIdeals_integralClosure`: any two
  maximal ideals of `B` differ by the canonical action of a Galois automorphism.
* `IsDiscreteValuationRing.exists_uniform_ramificationIdx_inertiaDeg_and_finrank_eq`: the common
  positive ramification index and residue degree, together with the degree identity
  `n * e * f = [L : K]`.
* `MulAction.stabilizer` and `Ideal.inertia`, the decomposition and the inertia group, together
  with the canonical action `Ideal.Quotient.stabilizerHom` of the former on the residue algebra
  and the identification `Ideal.Quotient.ker_stabilizerHom` of the latter as its kernel;
  `IsDiscreteValuationRing.under_eq_maximalIdeal_and_ker_stabilizerHom_eq_inertia` identifies
  these as the two groups above, the residue extension being `κ(m)/κ_A`, for any `L / K`.
* `IsDiscreteValuationRing.residueField_normal_and_stabilizerHom_surjective_of_isGalois`:
  normality of the residue extension, surjectivity of the decomposition group onto its relative
  automorphisms, the equivalence of separability at some and at all maximal ideals, and the
  resulting Galois property.
* `IsDiscreteValuationRing.exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity`: the
  canonical wild–tame exact sequence, the description of wild inertia, and the identification of
  the tame quotient with roots of unity.
* `IsDiscreteValuationRing.exists_uniformizerRatioMap_to_rootsOfUnity`: the local calculation
  producing the inertia character, for an abstract group acting on a discrete valuation ring
  trivially on the residue field.

## Implementation notes

The action on the integral closure is Mathlib's canonical
`IsIntegralClosure.MulSemiringAction`, and transitivity on maximal ideals is expressed directly
by the existence of an automorphism carrying one to another. The maximal ideals of `B` are the
set `Ideal.primesOver` of primes over the maximal ideal of `A`, and its finite cardinality is
the integer `n`. The residue field at a maximal ideal is
represented by the quotient, which is already a field; for a maximal ideal `P` of `B` the
contraction `P.under A` is the unique maximal ideal of `A`.

The common integer `e` is represented canonically by `Ideal.ramificationIdx`, and the
prime-to-`p` part of `e` is written `e / p ^ e.factorization p`, which also equals `e` in
residue characteristic zero. The formula characterizing the inertia character is written without
division: for `x ∈ P \ P²` the congruence `σ(x) ≡ a x (mod P²)` says that the residue of
`σ(x) / x` is the residue of `a`. Trivial action on the associated graded ring is expressed by
membership in inertia together with `σ(b) - b ∈ P²` for every `b ∈ P`, since its degree-zero and
degree-one pieces generate it. Note that `κ(m)` may be inseparable over `κ_A`, so the residue
extension need not be Galois; it is when `κ_A` is perfect.

## References

* [The Stacks Project, Tag 09EA](https://stacks.math.columbia.edu/tag/09EA)
* [The Stacks Project, Tag 09EB](https://stacks.math.columbia.edu/tag/09EB)
* [The Stacks Project, Tag 09EC](https://stacks.math.columbia.edu/tag/09EC)
* [The Stacks Project, Tag 09ED](https://stacks.math.columbia.edu/tag/09ED)
* [The Stacks Project, Tag 09EE](https://stacks.math.columbia.edu/tag/09EE)
* [The Stacks Project, Tag 0BU3](https://stacks.math.columbia.edu/tag/0BU3)
-/

@[expose] public section

universe u v

open scoped Pointwise

add_to_stacks 09EC "(1), the decomposition group" MulAction.stabilizer
add_to_sga "1 V 6.13" MulAction.stabilizer
add_to_sga "3 I 2.3.3" "special case" MulAction.stabilizer
add_to_sga "3 VIIB 2.5.A" MulAction.stabilizer
add_to_sga "3 XXI 6.7.2" "more general" MulAction.stabilizer
add_to_sga "5 IIIB 5.13" "more general" MulAction.stabilizer
add_to_sga "5 X 4.2" MulAction.stabilizer

add_to_stacks 09EC "(2), the inertia group" Ideal.inertia
add_to_sga "7 I 0.3" Ideal.inertia
add_to_sga "7 XIII 0.2" Ideal.inertia

add_to_stacks 09EC "The action of the decomposition group on the residue algebra"
  Ideal.Quotient.stabilizerHom

add_to_stacks 09EC "The inertia group as the kernel of the residue-algebra action"
  Ideal.Quotient.ker_stabilizerHom

namespace IsDiscreteValuationRing

/-- Two maximal ideals of an integral extension of a local ring lie over the same ideal. -/
private theorem under_eq_of_isMaximal {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (P Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] :
    P.under A = Q.under A :=
  (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).trans
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A Q)).symm

/-- For a finite Galois extension `L / K` of the fraction field of an integrally closed domain `A`,
`Gal(L/K)` is a Galois group of the integral closure of `A` in `L`. -/
private theorem isGaloisGroup_integralClosure
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    IsGaloisGroup Gal(L/K) A (integralClosure A L) := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let := IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  exact IsGaloisGroup.of_isFractionRing _ _ _ K L

/-- The integral closure of `A` in a field extension `L` of its fraction field is a faithful
`A`-module. -/
private theorem faithfulSMul_integralClosure
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    FaithfulSMul A (integralClosure A L) := by
  have : FaithfulSMul A L := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  infer_instance

/-- For a finite Galois extension `L / K`, the canonical action of `Gal(L/K)` on the integral
closure of a discrete valuation ring `A` in `L` is transitive on its maximal ideals. -/
@[stacks 09EA]
theorem galAction_transitive_on_maximalIdeals_integralClosure
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ P Q : Ideal B, P.IsMaximal → Q.IsMaximal →
      ∃ σ : Gal(L/K), σ • P = Q := by
  dsimp only
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro P Q hP hQ
  let : P.IsMaximal := hP
  let : Q.IsMaximal := hQ
  let : P.IsPrime := hP.isPrime
  let : Q.IsPrime := hQ.isPrime
  have := isGaloisGroup_integralClosure A K L
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    A (integralClosure A L) Gal(L/K) P Q (under_eq_of_isMaximal P Q)
  exact ⟨σ, hσ.symm⟩

/-- In a finite Galois extension of the fraction field of a discrete valuation ring, all primes
of the integral closure over the maximal ideal have the same positive ramification index and
inertia degree. The field degree is the number of these primes times the two common values. -/
@[stacks 09EB]
theorem exists_uniform_ramificationIdx_inertiaDeg_and_finrank_eq
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L] :
    let B := integralClosure A L
    let p := IsLocalRing.maximalIdeal A
    ∃ e f : ℕ,
      1 ≤ e ∧
      1 ≤ f ∧
      (∀ P : p.primesOver B, P.1.ramificationIdx A = e ∧ P.1.inertiaDeg A = f) ∧
      (p.primesOver B).ncard * e * f = Module.finrank K L := by
  dsimp only
  let B := integralClosure A L
  let p := IsLocalRing.maximalIdeal A
  have hB := integralClosure_finite_dedekind_and_degree_eq_sum_ramification_inertia A K L
  let : Module.Finite A B := hB.1
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have := faithfulSMul_integralClosure A K L
  let : IsDedekindDomain B := hB.2.2.2.1
  let := IsIntegralClosure.MulSemiringAction A K L B
  have := isGaloisGroup_integralClosure A K L
  let P₀ := Classical.choice (inferInstance : Nonempty (p.primesOver B))
  let e := P₀.1.ramificationIdx A
  let f := P₀.1.inertiaDeg A
  have hunif (P : p.primesOver B) : P.1.ramificationIdx A = e ∧ P.1.inertiaDeg A = f := by
    obtain ⟨σ, hσ⟩ := galAction_transitive_on_maximalIdeals_integralClosure
      A K L P₀.1 P.1
      (P₀.2.1.isMaximal (Ideal.ne_bot_of_mem_primesOver (IsDiscreteValuationRing.not_a_field A)
        P₀.2))
      (P.2.1.isMaximal (Ideal.ne_bot_of_mem_primesOver (IsDiscreteValuationRing.not_a_field A) P.2))
    exact ⟨by rw [← hσ, Ideal.ramificationIdx_smul], by rw [← hσ, Ideal.inertiaDeg_smul]⟩
  refine ⟨e, f, P₀.1.ramificationIdx_pos A, P₀.1.inertiaDeg_pos A, hunif, ?_⟩
  show (p.primesOver B).ncard * e * f = Module.finrank K L
  rw [IsFractionRing.finrank_eq A K B L, ← Ideal.sum_ramification_inertia_eq_finrank p B]
  simp_rw [hunif]
  rw [← Set.fintypeCard_eq_ncard]
  simp [Nat.mul_assoc]

/-- The decomposition and the inertia group at a maximal ideal `P` of the integral closure `B`
of a discrete valuation ring `A` in a field extension `L / K`.

The decomposition group is the stabilizer `{σ ∈ Gal(L/K) | σ P = P}`, and the ideal of `A` below
`P` is the maximal ideal, so the residue extension the decomposition group acts on really is
`κ(P) / κ_A`. The inertia group is the kernel of that action: it is `Ideal.inertia`, sitting
inside the decomposition group, and an element of the decomposition group lies in it exactly when
it acts trivially on `κ(P)`. -/
@[stacks 09EC "The decomposition group is `MulAction.stabilizer` and the inertia group is
`Ideal.inertia`, both of which Mathlib already has for an arbitrary action; what is recorded here
is that they are the source's two groups, the ideal below `P` being the maximal ideal of `A` so
that the extension acted on is `κ(P)/κ_A`. Stated without the fraction-field, finiteness and
Galois hypotheses, which the comparison does not use, so the source's setting is a special
case.", sga "7 I 0.3" "partial"]
theorem under_eq_maximalIdeal_and_ker_stabilizerHom_eq_inertia
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K]
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    let D := MulAction.stabilizer Gal(L/K) P
    let I := P.inertia Gal(L/K)
    (∀ σ : Gal(L/K), σ ∈ D ↔ σ • P = P) ∧
      P.under A = IsLocalRing.maximalIdeal A ∧
      I ≤ D ∧
      (Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K)).ker = I.subgroupOf D ∧
      (∀ σ : D, σ ∈ (Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K)).ker ↔
        ∀ b : B, Ideal.Quotient.mk P ((σ : Gal(L/K)) • b) = Ideal.Quotient.mk P b) := by
  dsimp only
  refine ⟨fun σ ↦ Iff.rfl, ?_, Ideal.inertia_le_stabilizer P, ?_, ?_⟩
  · exact IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)
  · rw [Ideal.Quotient.ker_stabilizerHom, AddSubgroup.subgroupOf_inertia]
  · intro σ
    rw [Ideal.Quotient.ker_stabilizerHom, Ideal.mem_inertia]
    exact forall_congr' fun b ↦ (Ideal.Quotient.eq (I := P)).symm

/-- In a finite Galois extension of the fraction field of a discrete valuation ring, every
residue extension at a maximal ideal of the integral closure is normal, and its decomposition
group surjects onto the relative automorphism group. Separability of one such residue extension is
equivalent to separability of all of them; when this holds, the fixed residue extension is Galois
and the same canonical map is surjective onto its Galois group. -/
@[stacks 09ED, sga "1 V 1.1" "special case", sga "1 V 1.3" "special case"]
theorem residueField_normal_and_stabilizerHom_surjective_of_isGalois
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    let p := P.under A
    letI : Field (A ⧸ p) := Ideal.Quotient.field p
    letI : Field (B ⧸ P) := Ideal.Quotient.field P
    Normal (A ⧸ p) (B ⧸ P) ∧
      Function.Surjective (Ideal.Quotient.stabilizerHom P p Gal(L/K)) ∧
      ((∃ (Q : Ideal B) (_hQ : Q.IsMaximal),
          let q := Q.under A
          letI : Field (A ⧸ q) := Ideal.Quotient.field q
          letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
          Algebra.IsSeparable (A ⧸ q) (B ⧸ Q)) ↔
        (∀ (Q : Ideal B) (_hQ : Q.IsMaximal),
          let q := Q.under A
          letI : Field (A ⧸ q) := Ideal.Quotient.field q
          letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
          Algebra.IsSeparable (A ⧸ q) (B ⧸ Q))) ∧
      ((∃ (Q : Ideal B) (_hQ : Q.IsMaximal),
          let q := Q.under A
          letI : Field (A ⧸ q) := Ideal.Quotient.field q
          letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
          Algebra.IsSeparable (A ⧸ q) (B ⧸ Q)) →
        IsGalois (A ⧸ p) (B ⧸ P) ∧
          Function.Surjective (Ideal.Quotient.stabilizerHom P p Gal(L/K))) := by
  dsimp only
  let : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  let : Algebra.IsInvariant A (integralClosure A L) Gal(L/K) :=
    ⟨fun b hb ↦ by
      have hfixed : algebraMap (integralClosure A L) L b ∈
          IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) := by
        rintro ⟨σ, -⟩
        show σ • (b : L) = (b : L)
        simpa only [integralClosure.coe_smul] using congrArg Subtype.val (hb σ)
      have hbot : IntermediateField.fixedField (⊤ : Subgroup Gal(L/K)) = ⊥ :=
        ((IsGalois.tfae (F := K) (E := L)).out 1 2).mp (inferInstance : IsGalois K L)
      rw [hbot, IntermediateField.mem_bot] at hfixed
      obtain ⟨k, hk⟩ := hfixed
      have hbint : IsIntegral A b := IsIntegralClosure.isIntegral A L b
      rw [← isIntegral_algebraMap_iff (B := L), ← hk, isIntegral_algebraMap_iff] at hbint
      obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hbint
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply A (integralClosure A L) L,
        (FaithfulSMul.algebraMap_injective (integralClosure A L) L).eq_iff] at hk
      exact ⟨a, hk⟩⟩
  let : Field (A ⧸ P.under A) := Ideal.Quotient.field (P.under A)
  let : Field ((integralClosure A L) ⧸ P) := Ideal.Quotient.field P
  have hn : Normal (A ⧸ P.under A) ((integralClosure A L) ⧸ P) :=
    Ideal.Quotient.normal (A := A) (B := integralClosure A L) Gal(L/K) (P.under A) P
  have hs : Function.Surjective
      (Ideal.Quotient.stabilizerHom P (P.under A) Gal(L/K)) :=
    Ideal.Quotient.stabilizerHom_surjective (A := A) (B := integralClosure A L)
      Gal(L/K) (P.under A) P
  have hsep :
      ((∃ (Q : Ideal (integralClosure A L)) (hQ : Q.IsMaximal),
          let q := Q.under A
          let : Field (A ⧸ q) := Ideal.Quotient.field q
          let : Field ((integralClosure A L) ⧸ Q) := Ideal.Quotient.field Q
          Algebra.IsSeparable (A ⧸ q) ((integralClosure A L) ⧸ Q)) ↔
       (∀ (Q : Ideal (integralClosure A L)) (hQ : Q.IsMaximal),
          let q := Q.under A
          let : Field (A ⧸ q) := Ideal.Quotient.field q
          let : Field ((integralClosure A L) ⧸ Q) := Ideal.Quotient.field Q
          Algebra.IsSeparable (A ⧸ q) ((integralClosure A L) ⧸ Q))) := by
    constructor
    · rintro ⟨Q, hQ, hsepQ⟩ R hR
      let : Q.IsMaximal := hQ
      let : R.IsMaximal := hR
      have hpq : Q.under A = R.under A := under_eq_of_isMaximal Q R
      obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
        A (integralClosure A L) Gal(L/K) Q R hpq
      let : Q.LiesOver (R.under A) := ⟨hpq.symm⟩
      let : Field (A ⧸ Q.under A) := Ideal.Quotient.field (Q.under A)
      let : Field (A ⧸ R.under A) := Ideal.Quotient.field (R.under A)
      let : Field ((integralClosure A L) ⧸ Q) := Ideal.Quotient.field Q
      let : Field ((integralClosure A L) ⧸ R) := Ideal.Quotient.field R
      let e₁ : (A ⧸ Q.under A) ≃+* (A ⧸ R.under A) :=
        Ideal.quotientEquiv (Q.under A) (R.under A) (RingEquiv.refl A) (by simpa using hpq.symm)
      let e₂ : ((integralClosure A L) ⧸ Q) ≃ₐ[A ⧸ R.under A]
          ((integralClosure A L) ⧸ R) :=
        Ideal.Quotient.algEquivOfEqMap (R.under A)
          (MulSemiringAction.toAlgEquiv A (integralClosure A L) σ) (by
            show R = σ • Q
            exact hσ)
      exact Algebra.IsSeparable.of_equiv_equiv
          (A₁ := A ⧸ Q.under A) (B₁ := (integralClosure A L) ⧸ Q)
          (A₂ := A ⧸ R.under A) (B₂ := (integralClosure A L) ⧸ R)
          e₁ e₂.toRingEquiv (by
        apply Ideal.Quotient.ringHom_ext
        ext x
        simp only [RingHom.comp_apply, e₁, e₂, Ideal.Quotient.algebraMap_mk_of_liesOver]
        exact congrArg (Ideal.Quotient.mk R)
          ((MulSemiringAction.toAlgEquiv A (integralClosure A L) σ).commutes x).symm)
    · intro h
      exact ⟨P, inferInstance, h P inferInstance⟩
  refine ⟨hn, hs, hsep, ?_⟩
  intro hex
  have hPsep := hsep.mp hex P (inferInstance : P.IsMaximal)
  let : Algebra.IsSeparable (A ⧸ P.under A) ((integralClosure A L) ⧸ P) := hPsep
  exact ⟨⟨⟩, hs⟩

section WildTameInertia

variable {R G : Type*} [CommRing R] [Group G] [MulSemiringAction G R]

/-- An action on a domain whose elements move every ring element only inside a principal prime
`P = (π)` multiplies `π` by a cocycle, whose residues assemble into a character of the acting
group with values in the units of `R ⧸ P`. -/
private theorem exists_inertiaCharacter_of_span_singleton [IsDomain R]
    (P : Ideal R) {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (x : R), g • x - x ∈ P) :
    ∃ χ : G →* (R ⧸ P)ˣ, ∀ g : G, ∃ c : R,
      g • π = π * c ∧ Ideal.Quotient.mk P c = (χ g : R ⧸ P) := by
  classical
  have hcoeff (g : G) : ∃ c : R, g • π = π * c := by
    apply Ideal.mem_span_singleton.mp
    rw [← hP]
    have hp : π ∈ P := hP ▸ Ideal.mem_span_singleton_self π
    simpa using P.add_mem (hG g π) hp
  choose c hc using hcoeff
  have hc_one : c 1 = 1 := by
    apply mul_left_cancel₀ hπ
    simpa using (hc 1).symm
  have hc_mul (g h : G) : c (g * h) = c g * (g • c h) := by
    apply mul_left_cancel₀ hπ
    rw [← hc, mul_smul, hc h, smul_mul', hc g, mul_assoc]
  let f : G →* R ⧸ P :=
    { toFun := fun g ↦ Ideal.Quotient.mk P (c g)
      map_one' := by simp [hc_one]
      map_mul' := fun g h ↦ by
        rw [hc_mul, map_mul]
        congr 1
        exact Ideal.Quotient.eq.mpr (hG g (c h)) }
  exact ⟨f.toHomUnits, fun g ↦ ⟨c g, hc g, rfl⟩⟩

/-- Two multiples of a generator of `P` are congruent modulo `P ^ 2` exactly when the
multipliers are congruent modulo `P`. -/
private theorem mul_sub_mem_pow_two_iff [IsDomain R] (P : Ideal R)
    {π a b : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π}) :
    π * a - π * b ∈ P ^ 2 ↔ a - b ∈ P := by
  rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton, ← mul_sub, pow_two]
  exact mul_dvd_mul_iff_left hπ

/-- The character of `exists_inertiaCharacter_of_span_singleton` records the action on `P / P ^ 2`:
if the residue of `a` is `χ g`, then `g • x ≡ a * x` modulo `P ^ 2` for every `x ∈ P`. -/
private theorem inertiaCharacter_spec [IsDomain R]
    (P : Ideal R) {π : R} (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (x : R), g • x - x ∈ P)
    (χ : G →* (R ⧸ P)ˣ)
    (hχ : ∀ g : G, ∃ c : R,
      g • π = π * c ∧ Ideal.Quotient.mk P c = (χ g : R ⧸ P))
    (g : G) (x a : R) (hx : x ∈ P)
    (ha : Ideal.Quotient.mk P a = (χ g : R ⧸ P)) :
    g • x - a * x ∈ P ^ 2 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp (hP ▸ hx)
  obtain ⟨c, hc, hqc⟩ := hχ g
  have hca : c - a ∈ P := Ideal.Quotient.eq.mp (hqc.trans ha.symm)
  have hp : π ∈ P := hP ▸ Ideal.mem_span_singleton_self π
  have hcb : c * (g • b) - a * b ∈ P :=
    P.mul_sub_mul_mem hca (hG g b)
  have hh := Ideal.mul_mem_mul hp hcb
  rw [pow_two]
  convert hh using 1
  rw [smul_mul', hc]
  ring

/-- An element lies in the kernel of the character exactly when it acts trivially on
`P / P ^ 2`. -/
private theorem inertiaCharacter_eq_one_iff [IsDomain R]
    (P : Ideal R) {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (x : R), g • x - x ∈ P)
    (χ : G →* (R ⧸ P)ˣ)
    (hχ : ∀ g : G, ∃ c : R,
      g • π = π * c ∧ Ideal.Quotient.mk P c = (χ g : R ⧸ P))
    (g : G) : χ g = 1 ↔ ∀ x : R, x ∈ P → g • x - x ∈ P ^ 2 := by
  constructor
  · intro hg x hx
    simpa using inertiaCharacter_spec P hP hG χ hχ g x 1 hx (by simp [hg])
  · intro hg
    obtain ⟨c, hc, hqc⟩ := hχ g
    apply Units.ext
    rw [← hqc]
    show Ideal.Quotient.mk P c = Ideal.Quotient.mk P 1
    apply Ideal.Quotient.eq.mpr
    apply (mul_sub_mem_pow_two_iff P hπ hP).mp
    simpa [hc] using hg π (hP ▸ Ideal.mem_span_singleton_self π)

/-- An element in the kernel of the character raises the filtration degree by one. -/
private theorem smul_sub_mem_pow_succ_of_inertiaCharacter_eq_one [IsDomain R]
    (P : Ideal R) {π : R} (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (x : R), g • x - x ∈ P)
    (χ : G →* (R ⧸ P)ˣ)
    (hχ : ∀ g : G, ∃ c : R,
      g • π = π * c ∧ Ideal.Quotient.mk P c = (χ g : R ⧸ P))
    (g : G) (hg : χ g = 1) (n : ℕ) (x : R) (hx : x ∈ P ^ n) :
    g • x - x ∈ P ^ (n + 1) := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp
    (show x ∈ Ideal.span {π ^ n} by simpa [hP, Ideal.span_singleton_pow] using hx)
  obtain ⟨c, hc, hqc⟩ := hχ g
  have hq : Ideal.Quotient.mk P c = 1 := by simpa [hg] using hqc
  have hb : Ideal.Quotient.mk P (g • b) = Ideal.Quotient.mk P b :=
    Ideal.Quotient.eq.mpr (hG g b)
  have hcb : c ^ n * (g • b) - b ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp [map_sub, map_mul, map_pow, hq, hb]
  have hp : π ∈ P := hP ▸ Ideal.mem_span_singleton_self π
  have hh := Ideal.mul_mem_mul (Ideal.pow_mem_pow hp n) hcb
  rw [pow_succ]
  convert hh using 1
  rw [smul_mul', smul_pow', hc, mul_pow]
  ring

/-- For an action raising the filtration degree, the order of a group element annihilates the
displacement it induces modulo one more power of `P`. -/
private theorem orderOf_smul_sub_mem_pow_succ (P : Ideal R)
    (hG : ∀ (g : G) (n : ℕ) (x : R), x ∈ P ^ n → g • x - x ∈ P ^ (n + 1))
    (g : G) (x : R) (n : ℕ) (hx : g • x - x ∈ P ^ n) :
    (orderOf g : R) * (g • x - x) ∈ P ^ (n + 1) := by
  have hsum (j : ℕ) :
      (g ^ j) • x - x - (j : R) * (g • x - x) ∈ P ^ (n + 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hh := (P ^ (n + 1)).add_mem (hG (g ^ j) n (g • x - x) hx) ih
      convert hh using 1
      rw [pow_succ, mul_smul, smul_sub, Nat.cast_add, Nat.cast_one]
      ring
  have hh := (P ^ (n + 1)).neg_mem (hsum (orderOf g))
  simpa using hh

/-- For a faithful action raising the filtration degree, the order of a nontrivial group element
lies in `P`. -/
private theorem orderOf_mem_of_trivial_on_graded [IsDomain R] [WfDvdMonoid R] [FaithfulSMul G R]
    (P : Ideal R) [P.IsPrime] {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (n : ℕ) (x : R), x ∈ P ^ n → g • x - x ∈ P ^ (n + 1))
    (g : G) (hg : g ≠ 1) : (orderOf g : R) ∈ P := by
  have hprime : Prime π := (Ideal.span_singleton_prime hπ).mp (hP ▸ inferInstance)
  obtain ⟨x, hx⟩ : ∃ x : R, g • x ≠ x := by
    by_contra! h
    exact hg (FaithfulSMul.eq_of_smul_eq_smul fun x : R ↦ by simpa using h x)
  have hd : g • x - x ≠ 0 := sub_ne_zero.mpr hx
  obtain ⟨u, hu, hnu⟩ :=
    (FiniteMultiplicity.of_prime_left hprime hd).exists_eq_pow_mul_and_not_dvd
  let n := multiplicity π (g • x - x)
  have hxpow : g • x - x ∈ P ^ n := by
    rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨u, hu⟩
  have hh := orderOf_smul_sub_mem_pow_succ P hG g x n hxpow
  rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu, pow_succ] at hh
  have hmul : π ∣ (orderOf g : R) * u := by
    apply (mul_dvd_mul_iff_left (pow_ne_zero n hπ)).mp
    convert hh using 1
    ring
  have hmem : (orderOf g : R) * u ∈ P := by
    rw [hP, Ideal.mem_span_singleton]
    exact hmul
  exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_right
    (by simpa [hP, Ideal.mem_span_singleton] using hnu)

/-- A finite group acting faithfully and raising the filtration degree is a `p`-group, where `p`
is the characteristic of `R ⧸ P`. -/
private theorem isPGroup_of_trivial_on_graded [IsDomain R] [WfDvdMonoid R] [Finite G]
    [FaithfulSMul G R]
    (P : Ideal R) [P.IsPrime] {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (n : ℕ) (x : R), x ∈ P ^ n → g • x - x ∈ P ^ (n + 1))
    (p : ℕ) [CharP (R ⧸ P) p] (hp : p.Prime) : IsPGroup p G := by
  apply (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mpr
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  let : Fact q.Prime := ⟨hqp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) q hqd
  have hgne : g ≠ 1 := by
    intro h
    simpa [h] using hg.trans_ne hqp.ne_one
  have hh := orderOf_mem_of_trivial_on_graded P hπ hP hG g hgne
  have hzero : (q : R ⧸ P) = 0 := by
    simpa [hg] using Ideal.Quotient.eq_zero_iff_mem.mpr hh
  have hpq : p ∣ q := (CharP.cast_eq_zero_iff (R ⧸ P) p q).mp hzero
  have hpq' : p = q := (Nat.dvd_prime hqp).mp hpq |>.resolve_left hp.ne_one
  simpa [← hpq'] using (Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩ : p ∈ p.primeFactors)

/-- In residue characteristic zero a finite group acting faithfully and raising the filtration
degree is trivial. -/
private theorem eq_one_of_trivial_on_graded_of_charZero [IsDomain R] [WfDvdMonoid R] [Finite G]
    [FaithfulSMul G R]
    (P : Ideal R) [P.IsPrime] [CharZero (R ⧸ P)]
    {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    (hG : ∀ (g : G) (n : ℕ) (x : R), x ∈ P ^ n → g • x - x ∈ P ^ (n + 1))
    (g : G) : g = 1 := by
  by_contra hg
  have hh := orderOf_mem_of_trivial_on_graded P hπ hP hG g hg
  have hzero : (orderOf g : R ⧸ P) = 0 := by
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hh
  exact (orderOf_pos g).ne' (Nat.cast_eq_zero.mp hzero)

/-- If some invariant element is `π ^ e` times a unit modulo `P`, the character takes values in
the `e`-th roots of unity. -/
private theorem inertiaCharacter_pow_eq_one [IsDomain R]
    (P : Ideal R) [P.IsPrime] {π : R} (hπ : π ≠ 0)
    (hG : ∀ (g : G) (x : R), g • x - x ∈ P)
    (χ : G →* (R ⧸ P)ˣ)
    (hχ : ∀ g : G, ∃ c : R,
      g • π = π * c ∧ Ideal.Quotient.mk P c = (χ g : R ⧸ P))
    (e : ℕ) (u : R) (hu : u ∉ P)
    (hfix : ∀ g : G, g • (π ^ e * u) = π ^ e * u) (g : G) : χ g ^ e = 1 := by
  obtain ⟨c, hc, hqc⟩ := hχ g
  have hce : c ^ e * (g • u) = u := by
    apply mul_left_cancel₀ (pow_ne_zero e hπ)
    simpa [smul_mul', smul_pow', hc, mul_pow, mul_assoc] using hfix g
  have hqu : Ideal.Quotient.mk P u ≠ 0 := fun h ↦ hu (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hgu : Ideal.Quotient.mk P (g • u) = Ideal.Quotient.mk P u :=
    Ideal.Quotient.eq.mpr (hG g u)
  apply Units.ext
  apply mul_right_cancel₀ hqu
  simpa [map_mul, map_pow, hgu, hqc] using congrArg (Ideal.Quotient.mk P) hce

/-- Evaluating a polynomial commutes with passing to residue rings along a lying-over pair. -/
private theorem quotient_mk_aeval
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    (P : Ideal R) (p : Ideal A) [P.LiesOver p] (b : R) (f : Polynomial A) :
    Ideal.Quotient.mk P (f.aeval b) =
      (f.map (Ideal.Quotient.mk p)).aeval (Ideal.Quotient.mk P b) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [map_add, hf, hg]
  | monomial n a => simp [Polynomial.aeval_monomial, map_mul, map_pow]

/-- When the residue extension is separable, an element acting trivially on `P / P ^ 2` acts
trivially on all of `R / P ^ 2`. -/
private theorem smul_sub_mem_pow_two_of_isSeparable
    {A R G : Type*} [CommRing A] [CommRing R] [IsDomain R] [Algebra A R]
    [Group G] [MulSemiringAction G R] [SMulCommClass G A R]
    (P : Ideal R) [P.IsMaximal] (p : Ideal A) [p.IsMaximal] [P.LiesOver p]
    {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    (g : G) (hg : ∀ b : R, g • b - b ∈ P)
    (hg' : ∀ b : R, b ∈ P → g • b - b ∈ P ^ 2)
    (hsep : letI : Field (A ⧸ p) := Ideal.Quotient.field p
      Algebra.IsSeparable (A ⧸ p) (R ⧸ P)) :
    ∀ b : R, g • b - b ∈ P ^ 2 := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let := hsep
  intro b
  let b' := Ideal.Quotient.mk P b
  let f := minpoly (A ⧸ p) b'
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (Ideal.Quotient.mk p)
    (Ideal.Quotient.mk_surjective) f
  have hf : f.aeval b' = 0 := minpoly.aeval (A ⧸ p) b'
  have hqd : q.aeval b ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, quotient_mk_aeval P p, hq]
    exact hf
  have hder : q.derivative.aeval b ∉ P := by
    intro h
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [quotient_mk_aeval P p, ← Polynomial.derivative_map, hq] at hzero
    exact (Algebra.IsSeparable.isSeparable (A ⧸ p) b').aeval_derivative_ne_zero hf hzero
  obtain ⟨t, ht⟩ := (q.map (algebraMap A R)).binomExpansion b (g • b - b)
  have hTaylor : q.aeval (g • b) = q.aeval b +
      q.derivative.aeval b * (g • b - b) + t * (g • b - b) ^ 2 := by
    simpa [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] using ht
  have hsq := (P ^ 2).mul_mem_left t (Ideal.pow_mem_pow (hg b) 2)
  have htotal := (P ^ 2).sub_mem (hg' (q.aeval b) hqd) hsq
  have hmul : q.derivative.aeval b * (g • b - b) ∈ P ^ 2 := by
    rw [← Polynomial.aeval_smul, hTaylor] at htotal
    convert htotal using 1
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hP ▸ hg b)
  have hdc : q.derivative.aeval b * c ∈ P := by
    rw [hP, Ideal.mem_span_singleton]
    apply (mul_dvd_mul_iff_left hπ).mp
    rw [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc, pow_two] at hmul
    convert hmul using 1
    ring
  have hcP := (Ideal.IsPrime.mem_or_mem inferInstance hdc).resolve_left hder
  rw [hc, pow_two]
  exact Ideal.mul_mem_mul (hP ▸ Ideal.mem_span_singleton_self π) hcP

/-- The uniformizer-ratio property determines the character uniquely. -/
private theorem inertiaCharacter_ext [IsDomain R]
    (P : Ideal R) (hPtop : P ≠ ⊤) {π : R} (hπ : π ≠ 0)
    (hP : P = Ideal.span {π}) (χ χ' : G →* (R ⧸ P)ˣ)
    (hχ : ∀ g : G, ∃ c : R,
      g • π = π * c ∧ Ideal.Quotient.mk P c = (χ g : R ⧸ P))
    (hχ' : ∀ (g : G) (x a : R), x ∈ P → x ∉ P ^ 2 →
      Ideal.Quotient.mk P a = (χ' g : R ⧸ P) → g • x - a * x ∈ P ^ 2) :
    χ' = χ := by
  have hp : π ∈ P := hP ▸ Ideal.mem_span_singleton_self π
  have hp2 : π ∉ P ^ 2 := by
    intro h
    have h1 : (1 : R) ∈ P := by
      simpa using (mul_sub_mem_pow_two_iff P (a := 1) (b := 0) hπ hP).mp (by simpa using h)
    exact hPtop (Ideal.eq_top_of_isUnit_mem P h1 isUnit_one)
  ext g
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (χ' g : R ⧸ P)
  obtain ⟨c, hc, hqc⟩ := hχ g
  rw [← ha, ← hqc]
  apply Eq.symm
  apply Ideal.Quotient.eq.mpr
  apply (mul_sub_mem_pow_two_iff P hπ hP).mp
  simpa [hc, mul_comm] using hχ' g π a hp hp2 ha

/-- An element of the decomposition group preserves every power of `P`. -/
private theorem smul_mem_pow_of_mem_stabilizer
    (P : Ideal R) (g : MulAction.stabilizer G P) (n : ℕ) {x : R} (hx : x ∈ P ^ n) :
    g • x ∈ P ^ n := by
  have hh := Ideal.smul_mem_pointwise_smul (g : G) x (P ^ n) hx
  have hg : (g : G) • P = P := g.property
  show (g : G) • x ∈ P ^ n
  simpa only [smul_pow', hg] using hh

/-- The subgroup of inertia acting trivially on `P / P ^ 2`, pushed into the decomposition
group, is described by that same condition and is normal there. -/
private theorem normal_map_of_inertiaCharacter_ker
    (P : Ideal R) (W : Subgroup (P.inertia G))
    (hW : ∀ g : P.inertia G, g ∈ W ↔ ∀ x : R, x ∈ P → (g : G) • x - x ∈ P ^ 2) :
    let inclusion : P.inertia G →* MulAction.stabilizer G P :=
      (P.inertia G).subtype.codRestrict _ (fun g ↦ Ideal.inertia_le_stabilizer P g.property)
    (∀ g : MulAction.stabilizer G P, g ∈ W.map inclusion ↔
      (g : G) ∈ P.inertia G ∧ ∀ x : R, x ∈ P → g • x - x ∈ P ^ 2) ∧
    (W.map inclusion).Normal := by
  intro inclusion
  have hmem (g : MulAction.stabilizer G P) : g ∈ W.map inclusion ↔
      (g : G) ∈ P.inertia G ∧ ∀ x : R, x ∈ P → g • x - x ∈ P ^ 2 := by
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ.property, (hW σ).mp hσ⟩
    · rintro ⟨hg, hx⟩
      exact ⟨⟨g, hg⟩, (hW _).mpr hx, Subtype.ext rfl⟩
  refine ⟨hmem, ⟨?_⟩⟩
  intro n hn g
  obtain ⟨hnI, hnP⟩ := (hmem n).mp hn
  apply (hmem _).mpr
  constructor
  · show g * n * g⁻¹ ∈ P.inertia (MulAction.stabilizer G P)
    exact Subgroup.Normal.conj_mem inferInstance n hnI g
  · intro x hx
    have hginv : g⁻¹ • x ∈ P := by
      simpa using smul_mem_pow_of_mem_stabilizer P g⁻¹ 1 (by simpa using hx)
    have hh := smul_mem_pow_of_mem_stabilizer P g 2 (hnP _ hginv)
    simpa [mul_smul, smul_sub] using hh

end WildTameInertia

/-- A generator of a prime lying over a principal prime of the base factors that generator as its
`e`-th power, with `e` the ramification index, times an element outside the prime. -/
theorem exists_eq_pow_ramificationIdx_mul
    {A R : Type*} [CommRing A] [IsDomain A] [CommRing R]
    [IsDedekindDomain R] [IsPrincipalIdealRing R] [Algebra A R] [FaithfulSMul A R]
    (P : Ideal R) [P.IsPrime] (p : Ideal A) [P.LiesOver p]
    {π : R} (hπ : π ≠ 0) (hP : P = Ideal.span {π})
    {ρ : A} (hρ : ρ ≠ 0) (hp : p = Ideal.span {ρ}) :
    ∃ u : R, algebraMap A R ρ = π ^ P.ramificationIdx A * u ∧ u ∉ P := by
  have hprime : Prime π := (Ideal.span_singleton_prime hπ).mp (hP ▸ inferInstance)
  have hρR : algebraMap A R ρ ≠ 0 :=
    fun h ↦ hρ (FaithfulSMul.algebraMap_injective A R (by simpa using h))
  have hfin := FiniteMultiplicity.of_prime_left hprime hρR
  have he : P.ramificationIdx A = multiplicity π (algebraMap A R ρ) := by
    have hp0 : p ≠ ⊥ := by simpa [hp, Ideal.span_singleton_eq_bot] using hρ
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx p P hp0]
    apply Ideal.ramificationIdx'_spec
    · simp [hp, Ideal.map_span, Set.image_singleton, hP, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
    · simpa [hp, Ideal.map_span, Set.image_singleton, hP, Ideal.span_singleton_pow,
        Ideal.span_singleton_le_span_singleton, Ideal.mem_span_singleton] using
        hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  obtain ⟨u, hu, hnu⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨u, he ▸ hu, by simpa [hP, Ideal.mem_span_singleton] using hnu⟩

/-- For a normal extension of fields the finite separable degree is the number of relative
automorphisms. -/
theorem finSepDegree_eq_card_aut_of_normal
    (k F : Type*) [Field k] [Field F] [Algebra k F] [Normal k F] :
    Field.finSepDegree k F = Nat.card Gal(F/k) := by
  rw [Field.finSepDegree_eq_of_adjoin_splits k F F (IntermediateField.adjoin_univ k F)
    (fun x _ ↦ ⟨Algebra.IsIntegral.isIntegral x, Normal.splits inferInstance x⟩)]
  exact (Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom k F).toEquiv).symm

section InertiaCardinality

attribute [local instance] Ideal.Quotient.field

/-- The inertia group at a maximal ideal has order the ramification index times the inseparable
degree of the residue extension. -/
private theorem card_inertia_eq_ramificationIdx_mul_finInsepDegree
    {A R G : Type*} [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    [Algebra A R] [Module.Finite A R] [Module.Flat A R]
    [Group G] [Finite G] [MulSemiringAction G R] [IsGaloisGroup G A R]
    (P : Ideal R) [P.IsMaximal] (p : Ideal A) [p.IsMaximal] [P.LiesOver p] :
    Nat.card (P.inertia G) = P.ramificationIdx A * Field.finInsepDegree (A ⧸ p) (R ⧸ P) := by
  have hnormal : Normal (A ⧸ p) (R ⧸ P) := Ideal.Quotient.normal G p P
  have htotal := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p R G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    Ideal.inertiaDegIn_eq_inertiaDeg p P G] at htotal
  have horbit : (p.primesOver R).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A R G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hn : (p.primesOver R).ncard ≠ 0 := by
    intro h
    have hz : Nat.card G = 0 := by simpa [h] using horbit.symm
    exact (Nat.card_pos (α := G)).ne' hz
  have hD := mul_left_cancel₀ hn (htotal.trans horbit.symm)
  have hindex : (P.inertia (MulAction.stabilizer G P)).index = Nat.card Gal((R ⧸ P)/(A ⧸ p)) :=
    Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  have hI : Nat.card (P.inertia (MulAction.stabilizer G P)) = Nat.card (P.inertia G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv
  have hprod := (P.inertia (MulAction.stabilizer G P)).card_mul_index
  rw [hindex, hI, ← hD, Ideal.inertiaDeg_eq_of_isMaximal p P,
    ← Field.finSepDegree_mul_finInsepDegree,
    finSepDegree_eq_card_aut_of_normal] at hprod
  apply mul_right_cancel₀ (Nat.card_pos (α := Gal((R ⧸ P)/(A ⧸ p)))).ne'
  rw [hprod]
  ring

end InertiaCardinality

/-- A character onto `e`-th roots of unity whose kernel is a `p`-group, on a group of order `e`
times a power of `p`, is surjective, and the roots of unity number the prime-to-`p` part
of `e`. -/
private theorem surjective_and_card_rootsOfUnity_of_isPGroup_ker
    {F G : Type*} [Field F] [Group G] [Finite G]
    (e p : ℕ) [NeZero e] [CharP F p] (hp : p.Prime)
    (θ : G →* rootsOfUnity e F) (hker : IsPGroup p θ.ker)
    (hcard : ∃ n : ℕ, Nat.card G = e * p ^ n) :
    Function.Surjective θ ∧ Nat.card (rootsOfUnity e F) = e / p ^ e.factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  have hroots : rootsOfUnity e F = rootsOfUnity (e / p ^ e.factorization p) F := by
    have he : p ^ e.factorization p * (e / p ^ e.factorization p) = e :=
      Nat.ordProj_mul_ordCompl_eq_self e p
    conv_lhs => rw [← he]
    ext ζ
    exact mem_rootsOfUnity_prime_pow_mul_iff F p (e.factorization p) _
  have hbound : Nat.card (rootsOfUnity e F) ≤ e / p ^ e.factorization p := by
    have : NeZero (e / p ^ e.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne e)).ne'⟩
    rw [hroots]
    exact card_rootsOfUnity F _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hker)
  obtain ⟨n, hn⟩ := hcard
  have hmul := θ.ker.card_mul_index
  rw [Subgroup.index_ker, hk, hn] at hmul
  have hcomp := congrArg (fun m ↦ m / p ^ m.factorization p) hmul
  rw [Nat.ordCompl_mul, Nat.ordCompl_self_pow hp, one_mul,
    Nat.ordCompl_mul, Nat.ordCompl_self_pow hp, mul_one] at hcomp
  have hle : e / p ^ e.factorization p ≤ Nat.card θ.range := by
    rw [← hcomp]
    exact Nat.ordCompl_le _ _
  have hrange : Nat.card θ.range ≤ Nat.card (rootsOfUnity e F) :=
    Nat.card_le_card_of_injective θ.range.subtype Subtype.val_injective
  have heq : Nat.card (rootsOfUnity e F) = e / p ^ e.factorization p :=
    le_antisymm hbound (hle.trans hrange)
  exact ⟨MonoidHom.range_eq_top.mp (θ.range.eq_top_of_le_card (heq.le.trans hle)), heq⟩

/-- An injective character from a group of order `e` onto `e`-th roots of unity is surjective,
and there are exactly `e` roots of unity. -/
private theorem surjective_and_card_rootsOfUnity_of_ker_eq_bot
    {F G : Type*} [Field F] [Group G] [Finite G]
    (e : ℕ) [NeZero e] (θ : G →* rootsOfUnity e F)
    (hker : θ.ker = ⊥) (hcard : Nat.card G = e) :
    Function.Surjective θ ∧ Nat.card (rootsOfUnity e F) = e := by
  have hle : e ≤ Nat.card (rootsOfUnity e F) := by
    calc
      e = Nat.card G := hcard.symm
      _ ≤ _ := Nat.card_le_card_of_injective θ ((MonoidHom.ker_eq_bot_iff θ).mp hker)
  have heq := le_antisymm (card_rootsOfUnity F e) hle
  have hrange : Nat.card θ.range = e := by
    have hh := θ.ker.card_mul_index
    have hwcard : Nat.card θ.ker = 1 := by rw [hker]; simp
    rw [Subgroup.index_ker, hwcard, one_mul] at hh
    exact hh.trans hcard
  exact ⟨MonoidHom.range_eq_top.mp (θ.range.eq_top_of_card_eq (hrange.trans heq.symm)), heq⟩

/-- The inertia group at a maximal ideal of the integral closure in a finite Galois extension
has a canonical wild–tame exact sequence. Wild inertia consists precisely of the elements of
inertia acting trivially on the maximal ideal modulo its square; it is normal in the decomposition
group and is a `p`-group in positive residue characteristic (and trivial in characteristic zero).
The tame quotient is cyclic of prime-to-`p` order and is canonically isomorphic to the
corresponding roots of unity in the residue field. If the residue extension is separable, wild
inertia is also the kernel of the action on `B / P²`. -/
@[stacks 09EE, sga "1 XIII 2.0" "inertia structure", sga "7 I 0.3" "finite Galois case"]
theorem exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    let D := MulAction.stabilizer Gal(L/K) P
    let I := P.inertia Gal(L/K)
    let inclusion : I →* D := I.subtype.codRestrict D
      (fun σ ↦ Ideal.inertia_le_stabilizer (M := Gal(L/K)) P σ.property)
    let e := P.ramificationIdx A
    let p := ringChar (IsLocalRing.ResidueField A)
    ∃ W : Subgroup I, ∃ _hW : W.Normal,
      (W.map inclusion).Normal ∧
      (∀ σ : I, σ ∈ W ↔ ∀ b : B, b ∈ P → (σ : Gal(L/K)) • b - b ∈ P ^ 2) ∧
      (∀ σ : D, σ ∈ W.map inclusion ↔
        (σ : Gal(L/K)) ∈ I ∧ ∀ b : B, b ∈ P → σ • b - b ∈ P ^ 2) ∧
      (0 < p → IsPGroup p W) ∧
      (p = 0 → W = ⊥) ∧
      (letI : Field (A ⧸ P.under A) := Ideal.Quotient.field (P.under A)
       Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P) →
         ∀ σ : D, σ ∈ W.map inclusion ↔ ∀ b : B, σ • b - b ∈ P ^ 2) ∧
      ∃ θ : I →* rootsOfUnity e (B ⧸ P),
        Function.Injective W.subtype ∧
        Function.MulExact W.subtype θ ∧
        Function.Surjective θ ∧
        IsCyclic (rootsOfUnity e (B ⧸ P)) ∧
        Nat.card (rootsOfUnity e (B ⧸ P)) = e / p ^ e.factorization p ∧
        (∀ (σ : I) (x a : B), x ∈ P → x ∉ P ^ 2 →
            Ideal.Quotient.mk P a = (θ σ).1.1 →
            (σ : Gal(L/K)) • x - a * x ∈ P ^ 2) ∧
        ∀ θ' : I →* rootsOfUnity e (B ⧸ P),
          (∀ (σ : I) (x a : B), x ∈ P → x ∉ P ^ 2 →
            Ideal.Quotient.mk P a = (θ' σ).1.1 →
            (σ : Gal(L/K)) • x - a * x ∈ P ^ 2) →
          θ' = θ := by
  classical
  dsimp only
  let B := integralClosure A L
  have := faithfulSMul_integralClosure A K L
  let : MulSemiringAction Gal(L/K) B := IsIntegralClosure.MulSemiringAction A K L B
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  let : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have := isGaloisGroup_integralClosure A K L
  have : FaithfulSMul Gal(L/K) B := IsGaloisGroup.faithful A
  let p₀ := P.under A
  let : Field (A ⧸ p₀) := Ideal.Quotient.field p₀
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  have hp₀ : p₀ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  let : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_finite_maximals (by
    apply (Algebra.QuasiFinite.finite_primesOver (S := B) (IsLocalRing.maximalIdeal A)).subset
    intro Q hQ
    let : Q.IsMaximal := hQ
    have hQunder : Q.under A = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal inferInstance
    exact ⟨inferInstance, ⟨hQunder.symm⟩⟩)
  have hp₀ne : p₀ ≠ ⊥ := hp₀ ▸ IsDiscreteValuationRing.not_a_field A
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp₀ne P
  let π := Submodule.IsPrincipal.generator P
  have hπ : π ≠ 0 := (Submodule.IsPrincipal.prime_generator_of_isPrime P hPne).ne_zero
  have hP : P = Ideal.span {π} := (Ideal.span_singleton_generator P).symm
  let I := P.inertia Gal(L/K)
  let D := MulAction.stabilizer Gal(L/K) P
  let inclusion : I →* D := I.subtype.codRestrict D
    (fun σ ↦ Ideal.inertia_le_stabilizer P σ.property)
  let e := P.ramificationIdx A
  let p := ringChar (IsLocalRing.ResidueField A)
  have hG (g : I) (x : B) : g • x - x ∈ P := g.property x
  obtain ⟨χ, hχ⟩ := exists_inertiaCharacter_of_span_singleton P hπ hP hG
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨u, hu, hun⟩ := exists_eq_pow_ramificationIdx_mul P p₀ hπ hP hρ.ne_zero
    (hp₀.trans hρ.maximalIdeal_eq)
  have hfix (g : I) : g • (π ^ e * u) = π ^ e * u := by
    rw [← hu]
    exact smul_algebraMap g ρ
  let θ : I →* rootsOfUnity e (B ⧸ P) := χ.codRestrict _
    (fun g ↦ (mem_rootsOfUnity e (χ g)).mpr
      (inertiaCharacter_pow_eq_one P hπ hG χ hχ e u hun hfix g))
  let W := θ.ker
  have hW (g : I) : g ∈ W ↔ ∀ x : B, x ∈ P → (g : Gal(L/K)) • x - x ∈ P ^ 2 := by
    show θ g = 1 ↔ _
    rw [Subtype.ext_iff]
    exact inertiaCharacter_eq_one_iff P hπ hP hG χ hχ g
  obtain ⟨hmem, hnormal⟩ := normal_map_of_inertiaCharacter_ker P W hW
  have hraise (g : W) (n : ℕ) (x : B) (hx : x ∈ P ^ n) : g • x - x ∈ P ^ (n + 1) :=
    smul_sub_mem_pow_succ_of_inertiaCharacter_eq_one P hP hG χ hχ g.val
      (congrArg Subtype.val g.property) n x hx
  have hchar₀ : ringChar (A ⧸ p₀) = p := by rw [hp₀]; rfl
  let : CharP (A ⧸ p₀) p := ringChar.of_eq hchar₀
  let : CharP (B ⧸ P) p := ringChar.of_eq
    ((Algebra.ringChar_eq (A ⧸ p₀) (B ⧸ P)).symm.trans hchar₀)
  have hwild (hp : 0 < p) : IsPGroup p W :=
    isPGroup_of_trivial_on_graded P hπ hP hraise p
      ((CharP.char_is_prime_or_zero (B ⧸ P) p).resolve_right hp.ne')
  have hzero (hp : p = 0) : W = ⊥ := by
    have : CharP (B ⧸ P) 0 := hp ▸ inferInstance
    have : CharZero (B ⧸ P) := CharP.charP_to_charZero (B ⧸ P)
    refine le_antisymm (fun g hg ↦ ?_) bot_le
    show g = 1
    exact congrArg Subtype.val
      (eq_one_of_trivial_on_graded_of_charZero P hπ hP hraise (⟨g, hg⟩ : W))
  have hcardI := card_inertia_eq_ramificationIdx_mul_finInsepDegree (G := Gal(L/K)) P p₀
  change Nat.card I = e * Field.finInsepDegree (A ⧸ p₀) (B ⧸ P) at hcardI
  let : NeZero e := ⟨(P.ramificationIdx_pos A).ne'⟩
  have htame : Function.Surjective θ ∧
      Nat.card (rootsOfUnity e (B ⧸ P)) = e / p ^ e.factorization p := by
    by_cases hp : p = 0
    · have : CharP (A ⧸ p₀) 0 := hp ▸ inferInstance
      have : CharZero (A ⧸ p₀) := CharP.charP_to_charZero (A ⧸ p₀)
      have : Algebra.IsSeparable (A ⧸ p₀) (B ⧸ P) :=
        Algebra.IsSeparable.of_integral (A ⧸ p₀) (B ⧸ P)
      have hI : Nat.card I = e := by
        simpa only [Algebra.IsSeparable.finInsepDegree_eq, mul_one] using hcardI
      simpa [hp] using surjective_and_card_rootsOfUnity_of_ker_eq_bot e θ (hzero hp) hI
    · have hprime := (CharP.char_is_prime_or_zero (B ⧸ P) p).resolve_right hp
      let : Fact p.Prime := ⟨hprime⟩
      obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (A ⧸ p₀) (B ⧸ P) p
      exact surjective_and_card_rootsOfUnity_of_isPGroup_ker e p hprime θ
        (hwild (Nat.pos_of_ne_zero hp)) ⟨n, by simpa only [hn] using hcardI⟩
  refine ⟨W, inferInstance, hnormal, hW, hmem, hwild, hzero, ?_, θ,
    Subtype.val_injective, ?_, htame.1, inferInstance, htame.2, ?_, ?_⟩
  · intro hsep g
    rw [hmem]
    constructor
    · rintro ⟨hg, hg'⟩
      exact smul_sub_mem_pow_two_of_isSeparable P p₀ hπ hP g hg hg' hsep
    · intro hg
      exact ⟨fun b ↦ Ideal.pow_le_self (by decide : 2 ≠ 0) (hg b), fun b _ ↦ hg b⟩
  · apply MonoidHom.mulExact_iff.mpr
    simp [W]
  · intro g x a hx _ ha
    exact inertiaCharacter_spec P hP hG χ hχ g x a hx ha
  · intro θ' hθ'
    have huniq := inertiaCharacter_ext P (Ideal.IsMaximal.ne_top inferInstance) hπ hP χ
      ((rootsOfUnity e (B ⧸ P)).subtype.comp θ') hχ hθ'
    exact MonoidHom.ext fun g ↦ Subtype.ext (congrArg (fun f : I →* (B ⧸ P)ˣ ↦ f g) huniq)

/-- Let a group act on a discrete valuation ring, trivially on its residue field. Suppose an
invariant element is a unit times the `e`-th power of a uniformizer. For every group element, its
action on the uniformizer differs from the uniformizer by a unit; the residues of these units are
`e`-th roots of unity and hence define a map to the group of such roots. -/
@[stacks 0BU3]
theorem exists_uniformizerRatioMap_to_rootsOfUnity
    (C : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (I : Type v) [Group I] [MulSemiringAction I C]
    (e : ℕ) (π a : C) (u : Cˣ)
    (hπ : Irreducible π)
    (ha : a = (u : C) * π ^ e)
    (ha_fixed : ∀ σ : I, σ • a = a)
    (hres : ∀ (σ : I) (x : C),
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal C) (σ • x) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal C) x) :
    ∃ (θ : I → rootsOfUnity e (C ⧸ IsLocalRing.maximalIdeal C))
      (θunit : I → Cˣ),
      (∀ σ : I, (θunit σ : C) * π = σ • π) ∧
        ∀ σ : I,
          (θ σ : (C ⧸ IsLocalRing.maximalIdeal C)ˣ) =
            Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal C)) (θunit σ) := by
  let q : C →+* C ⧸ IsLocalRing.maximalIdeal C :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal C)
  have hirr (σ : I) : Irreducible (σ • π) := hπ.map ((MulSemiringAction.toRingEquiv I C) σ)
  let θunit : I → Cˣ := fun σ ↦ Classical.choose
    (IsDiscreteValuationRing.associated_of_irreducible C hπ (hirr σ))
  have hθunit (σ : I) : (θunit σ : C) * π = σ • π := by
    simpa [θunit, mul_comm] using Classical.choose_spec
      (IsDiscreteValuationRing.associated_of_irreducible C hπ (hirr σ))
  let qunit : I → (C ⧸ IsLocalRing.maximalIdeal C)ˣ := fun σ ↦ Units.map q (θunit σ)
  have hpow (σ : I) : (qunit σ) ^ e = 1 := by
    apply Units.ext
    have hcalc : (σ • (u : C)) * (θunit σ : C) ^ e = (u : C) := by
      apply mul_right_cancel₀ (pow_ne_zero e hπ.ne_zero)
      rw [mul_assoc, ← mul_pow, hθunit]
      show ((MulSemiringAction.toRingEquiv I C) σ) (u : C) *
        (((MulSemiringAction.toRingEquiv I C) σ) π) ^ e = (u : C) * π ^ e
      rw [← map_pow ((MulSemiringAction.toRingEquiv I C) σ),
        ← map_mul ((MulSemiringAction.toRingEquiv I C) σ), ← ha]
      exact ha_fixed σ
    have hqcalc := congrArg q hcalc
    simp only [map_mul, map_pow] at hqcalc
    rw [hres σ (u : C)] at hqcalc
    apply mul_left_cancel₀ (Units.ne_zero (Units.map q u))
    simpa [q, qunit] using hqcalc
  let θ : I → rootsOfUnity e (C ⧸ IsLocalRing.maximalIdeal C) := fun σ ↦
    ⟨qunit σ, (mem_rootsOfUnity e (qunit σ)).2 (hpow σ)⟩
  exact ⟨θ, θunit, hθunit, fun σ ↦ by rfl⟩

end IsDiscreteValuationRing
