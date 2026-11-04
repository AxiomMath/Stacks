module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced

/-!
# Automorphisms inducing the identity on the underlying space

Let `X` be a reduced scheme locally of finite type over a field `k` and let `f : X → X` be an
endomorphism over `k` which fixes every point of the underlying topological space. If every
irreducible component of `X` has positive dimension then `f` is the identity.

Over an infinite field this is proved unconditionally. Over a finite field the argument needs a
bound on the order of the automorphism induced on the residue field of a closed point, so the
order of `f` is carried as an explicit hypothesis: the `n`-fold composite of `f` is asked to be
the identity. The source obtains such a bound from the finiteness of the automorphism group of a
curve over a finite field, which is not available here. The two cases are combined into the
single disjunctive hypothesis `Infinite k ∨ ∃ n, 0 < n ∧ (· ≫ f)^[n] (𝟙 X) = 𝟙 X`, whose first
alternative holds whenever `k` is infinite and whose second holds for every automorphism of
finite order. For an endomorphism that is not an automorphism the hypothesis cannot be removed at
all: over a finite field the `p`-power Frobenius fixes every point of the affine line and is not
the identity, which is `AlgHom.exists_comap_eq_ne_id_of_finite_field`. So an unconditional
statement over a finite field has to ask for an automorphism, and the source's bound on its order
is what is missing.

## Main results

* `AlgHom.eq_id_of_comap_eq_of_forall_minimalPrimes_of_iterate`: the algebraic statement for a
  reduced algebra of finite type over a field, the quotient by every minimal prime of which has
  positive dimension.
* `AlgHom.eq_id_of_comap_eq_of_ringKrullDim_pos` and
  `AlgHom.eq_id_of_comap_eq_of_forall_minimalPrimes`: the unconditional statements over an
  infinite field, for a domain and for a reduced algebra.
* `AlgEquiv.toAlgHom_eq_id_of_comap_eq_of_pow_eq_one`: the statement for a domain over a finite
  field and an automorphism of finite order.
* `AlgHom.exists_comap_eq_ne_id_of_finite_field`: over a finite field no such hypothesis can be
  dispensed with for an endomorphism, the `p`-power Frobenius of `(ZMod p)[X]` being a
  counterexample; it is not surjective, so the statement for an automorphism is untouched.
* `AlgebraicGeometry.eq_id_of_eq_on_points`: the geometric statement, for a reduced scheme
  locally of finite type over a field all of whose irreducible components have positive
  dimension.
* `AlgebraicGeometry.eq_id_of_isAffine_of_eq_on_points` and
  `AlgebraicGeometry.eq_id_of_isIntegral_of_eq_on_points`: the affine and the integral cases.

## Implementation notes

Finite type over a field is `Algebra.FiniteType` in the algebraic statements and
`LocallyOfFiniteType` for the structure morphism in the geometric ones; the geometric statements
assume neither that the structure morphism is quasi-compact nor that the endomorphism is
invertible, neither of which the argument needs. Inducing the identity on the spectrum is
`PrimeSpectrum.comap · = id` pointwise, and inducing the identity on the space of a scheme is the
pointwise equality `∀ x, f x = x`. The dimension of an irreducible component is the Krull
dimension of that component as a subspace of `X`.

## References

* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

/-- A ring of positive Krull dimension is not a field. -/
private lemma not_isField_of_ringKrullDim_pos {A : Type v} [CommRing A]
    (hdim : 0 < ringKrullDim A) : ¬ IsField A :=
  fun hA ↦ lt_irrefl _ (hdim.trans_eq (ringKrullDim_eq_zero_of_isField hA))

/-- A `k`-algebra endomorphism fixing every transcendental element of `A` is the identity, as
soon as one transcendental element exists. -/
private lemma eq_id_of_forall_transcendental_apply_eq {k : Type u} {A : Type v} [Field k]
    [CommRing A] [Algebra k A] (φ : A →ₐ[k] A) {t : A} (ht : Transcendental k t)
    (hfix : ∀ a : A, Transcendental k a → φ a = a) : φ = AlgHom.id k A := by
  ext a
  by_cases ha : Transcendental k a
  · exact hfix a ha
  · have hsum : Transcendental k (t + a) := by
      intro hsum
      refine ht (isAlgebraic_iff_isIntegral.mpr ?_)
      simpa using (isAlgebraic_iff_isIntegral.mp hsum).sub
        (isAlgebraic_iff_isIntegral.mp (Classical.not_not.mp ha))
    have heq := hfix (t + a) hsum
    rw [map_add, hfix t ht] at heq
    exact add_left_cancel heq

/-- For a transcendental element `a` of a domain `A` of finite type over a field `k`, the morphism
`Spec A → Spec k[X]` given by evaluation at `a` is open. -/
private lemma isOpenMap_comap_aeval_of_transcendental {k : Type u} {A : Type v} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {a : A}
    (ha : Transcendental k a) :
    IsOpenMap (PrimeSpectrum.comap (Polynomial.aeval (R := k) a).toRingHom) := by
  let : Algebra (Polynomial k) A := (Polynomial.aeval (R := k) a).toRingHom.toAlgebra
  have : IsScalarTower k (Polynomial k) A := IsScalarTower.of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have : Module.IsTorsionFree (Polynomial k) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (transcendental_iff_injective.mp ha)
  have : Algebra.FiniteType (Polynomial k) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation (Polynomial k) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

/-- A set of primes is dense once every element lying in all of them is zero. -/
private lemma dense_of_forall_mem_asIdeal_imp_eq_zero {R : Type*} [CommRing R]
    {S : Set (PrimeSpectrum R)} (h : ∀ f : R, (∀ P ∈ S, f ∈ P.asIdeal) → f = 0) : Dense S := by
  rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  suffices PrimeSpectrum.vanishingIdeal S = ⊥ by
    rw [this, PrimeSpectrum.zeroLocus_bot]
  exact (Submodule.eq_bot_iff _).mpr fun f hf ↦
    h f fun P hP ↦ (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf P hP

/-- Over an infinite field the rational points of the affine line are dense. -/
@[sga "3 XIV 6.4" "special case"]
private lemma dense_range_ker_evalRingHom (k : Type u) [Field k] [Infinite k] :
    Dense (Set.range fun c : k ↦
      (⟨RingHom.ker (Polynomial.evalRingHom c), RingHom.ker_isPrime _⟩ :
        PrimeSpectrum (Polynomial k))) := by
  refine dense_of_forall_mem_asIdeal_imp_eq_zero fun P hP ↦ ?_
  refine Polynomial.eq_of_infinite_eval_eq P 0 ?_
  have hzero : ∀ c : k, P.eval c = 0 := fun c ↦ hP _ ⟨c, rfl⟩
  simpa [hzero] using Set.infinite_univ (α := k)

/-- If the primes of a domain `A` of finite type over `k` lying over a dense subset of the affine
line via a transcendental `a` all contain `b - c`, then `b = c`. -/
private lemma eq_of_forall_comap_aeval_mem_dense {k : Type u} {A : Type v} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {a : A}
    (ha : Transcendental k a) {S : Set (PrimeSpectrum (Polynomial k))} (hS : Dense S) {b c : A}
    (h : ∀ P : PrimeSpectrum A,
      PrimeSpectrum.comap (Polynomial.aeval (R := k) a).toRingHom P ∈ S → b - c ∈ P.asIdeal) :
    b = c := by
  have hzero : PrimeSpectrum.zeroLocus {b - c} = Set.univ :=
    Set.eq_univ_of_univ_subset <| by
      rw [← (hS.preimage (isOpenMap_comap_aeval_of_transcendental ha)).closure_eq]
      exact closure_minimal (fun P hP ↦ by rintro _ rfl; exact h P hP)
        (PrimeSpectrum.isClosed_zeroLocus _)
  have hnil : IsNilpotent (b - c) :=
    (PrimeSpectrum.zeroLocus_eq_univ_iff _).mp hzero (Set.mem_singleton _)
  exact sub_eq_zero.mp hnil.eq_zero

/-- A `k`-algebra endomorphism of a domain of finite type over an infinite field which induces
the identity on the spectrum fixes every transcendental element. -/
private lemma apply_eq_of_transcendental_of_comap_eq {k : Type u} {A : Type v} [Field k]
    [Infinite k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P)
    {a : A} (ha : Transcendental k a) : φ a = a := by
  let S : Set (PrimeSpectrum (Polynomial k)) := Set.range fun c : k ↦
    (⟨RingHom.ker (Polynomial.evalRingHom c), RingHom.ker_isPrime _⟩ :
      PrimeSpectrum (Polynomial k))
  have hdense : Dense S := dense_range_ker_evalRingHom k
  refine eq_of_forall_comap_aeval_mem_dense ha hdense fun P ⟨c, hc⟩ ↦ ?_
  have hmem : a - algebraMap k A c ∈ P.asIdeal := by
    have hpoly : Polynomial.X - Polynomial.C c ∈ RingHom.ker (Polynomial.evalRingHom c) := by
      simp
    have hideal := congrArg PrimeSpectrum.asIdeal hc
    change RingHom.ker (Polynomial.evalRingHom c) =
      (PrimeSpectrum.comap (Polynomial.aeval (R := k) a).toRingHom P).asIdeal at hideal
    rw [hideal] at hpoly
    change Polynomial.aeval (R := k) a (Polynomial.X - Polynomial.C c) ∈ P.asIdeal at hpoly
    simpa using hpoly
  have hmap : φ a - algebraMap k A c ∈ P.asIdeal := by
    have hmem' : a - algebraMap k A c ∈
        (PrimeSpectrum.comap φ.toRingHom P).asIdeal := by rwa [hpoints]
    simpa using hmem'
  have h := P.asIdeal.sub_mem hmap hmem
  rwa [sub_sub_sub_cancel_right] at h

/-- A domain of finite type over a field which is not itself a field contains a transcendental
element. -/
private lemma exists_transcendental_of_not_isField {k : Type u} {A : Type v} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] (hA : ¬ IsField A) :
    ∃ a : A, Transcendental k a := by
  by_contra htrans
  have : Algebra.IsAlgebraic k A := ⟨fun a ↦ by
    by_contra ha
    exact htrans ⟨a, ha⟩⟩
  exact hA (isField_of_isIntegral_of_isField' (R := k) (S := A) (Field.toIsField k))

/-- A `k`-algebra endomorphism of a domain of finite type and positive Krull dimension over an
infinite field `k` which induces the identity on the prime spectrum is the identity. -/
theorem AlgHom.eq_id_of_comap_eq_of_ringKrullDim_pos {k : Type u} {A : Type v} [Field k]
    [Infinite k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P)
    (hdim : 0 < ringKrullDim A) : φ = AlgHom.id k A := by
  obtain ⟨a, ha⟩ :=
    exists_transcendental_of_not_isField (k := k) (not_isField_of_ringKrullDim_pos hdim)
  exact eq_id_of_forall_transcendental_apply_eq φ ha
    fun _ hb ↦ apply_eq_of_transcendental_of_comap_eq φ hpoints hb

/-- An automorphism of a finite field over `k` whose order divides `n` acts trivially on an
element lying in the subfield with `(#k) ^ m` elements when `m` is prime to `n`. -/
private lemma apply_eq_of_pow_card_of_coprime {k : Type u} {L : Type v} [Field k] [Finite k]
    [Field L] [Finite L] [Algebra k L] (σ : L ≃ₐ[k] L) {n m : ℕ} (horder : σ ^ n = 1)
    (hmn : m.Coprime n) {a : L} (ha : a ^ (Nat.card k ^ m) = a) : σ a = a := by
  obtain ⟨p, hp⟩ := CharP.exists k
  have : CharP k p := hp
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow k p L σ
  have hpow (j : ℕ) : (σ ^ j) a = a ^ (Nat.card k ^ (i * j)) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, hi, ih, ← pow_mul, ← pow_add]
      congr 2
  have hn : Function.IsPeriodicPt (⇑σ) n a := by
    simp only [Function.IsPeriodicPt, Function.IsFixedPt, ← AlgEquiv.coe_pow, horder,
      AlgEquiv.one_apply]
  have hm : Function.IsPeriodicPt (⇑σ) m a := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← AlgEquiv.coe_pow, hpow, Nat.mul_comm i m,
      pow_mul]
    simpa only [Function.IsFixedPt, pow_iterate] using
      (show Function.IsFixedPt (fun z : L ↦ z ^ (Nat.card k ^ m)) a from ha).iterate i
  simpa only [hmn.gcd_eq_one, Function.IsPeriodicPt, Function.IsFixedPt,
    Function.iterate_one] using hm.gcd hn

/-- For a `k`-algebra automorphism of finite order inducing the identity on the spectrum, the
displacement of any element lies in the radical of the ideal generated by `a ^ (#k) ^ m - a`
whenever `m` is prime to the order. -/
private lemma sub_mem_radical_of_pow_eq_one {k : Type u} {A : Type v} [Field k] [Finite k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (σ : A ≃ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap σ.toRingHom P = P)
    {n m : ℕ} (horder : σ ^ n = 1) (hmn : m.Coprime n) (a : A) :
    σ a - a ∈ (Ideal.span {a ^ (Nat.card k ^ m) - a}).radical := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson]
  refine Ideal.mem_sInf.mpr fun M hM ↦ ?_
  have : M.IsMaximal := hM.2
  let : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite k (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ M)
  have : Finite (A ⧸ M) := Module.finite_of_finite k
  have hmap : M = Ideal.map σ.toRingHom M :=
    (Ideal.map_comap_of_surjective σ.toRingHom σ.surjective M).symm.trans
      (congrArg (Ideal.map σ.toRingHom)
        (congrArg PrimeSpectrum.asIdeal (hpoints ⟨M, inferInstance⟩)))
  let τ := Ideal.quotientEquivAlg M M σ hmap
  have hpow (j : ℕ) (b : A) :
      (τ ^ j) (Ideal.Quotient.mk M b) = Ideal.Quotient.mk M ((σ ^ j) b) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply]
      exact Ideal.quotientEquivAlg_mk M σ hmap _
  have hτ : τ ^ n = 1 := by
    ext b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hpow, horder, AlgEquiv.one_apply, AlgEquiv.one_apply]
  have ha : (Ideal.Quotient.mk M a) ^ (Nat.card k ^ m) = Ideal.Quotient.mk M a := by
    rw [← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hM.1 (Ideal.subset_span (Set.mem_singleton _))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact (Ideal.quotientEquivAlg_mk M σ hmap a).symm.trans
    (apply_eq_of_pow_card_of_coprime τ hτ hmn ha)

/-- Over a finite field, the closed points of the affine line whose residue degree is prime to a
given positive integer are dense. -/
private lemma dense_coprime_power_loci (k : Type u) [Field k] [Finite k] (n : ℕ) (hn : 0 < n) :
    Dense {P : PrimeSpectrum (Polynomial k) | ∃ m : ℕ,
      m.Coprime n ∧ Polynomial.X ^ (Nat.card k ^ m) - Polynomial.X ∈ P.asIdeal} := by
  set S : Set (PrimeSpectrum (Polynomial k)) := {P | ∃ m : ℕ,
    m.Coprime n ∧ Polynomial.X ^ (Nat.card k ^ m) - Polynomial.X ∈ P.asIdeal}
  refine dense_of_forall_mem_asIdeal_imp_eq_zero fun P hP ↦ ?_
  obtain ⟨p, hp⟩ := CharP.exists k
  have : CharP k p := hp
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  set m := n * (P.natDegree + 1) + 1 with hm
  have : NeZero m := ⟨by rw [hm]; omega⟩
  have hmn : m.Coprime n := by
    rw [hm, Nat.add_comm, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left n
  let L := FiniteField.Extension k p m
  let : Fintype L := Fintype.ofFinite L
  have hmap : P.map (algebraMap k L) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ ?_ ?_
    · intro b _
      have hb := hP
        ⟨RingHom.ker (Polynomial.aeval (R := k) b).toRingHom, RingHom.ker_isPrime _⟩ ?_
      · change Polynomial.aeval (R := k) b P = 0 at hb
        simpa only [Polynomial.eval_map, Polynomial.aeval_def] using hb
      · refine ⟨m, hmn, ?_⟩
        show Polynomial.aeval (R := k) b (Polynomial.X ^ (Nat.card k ^ m) - Polynomial.X) = 0
        simp only [map_sub, map_pow, Polynomial.aeval_X]
        rw [← FiniteField.natCard_extension k p m, ← Fintype.card_eq_nat_card]
        exact sub_eq_zero.mpr (FiniteField.pow_card b)
    · rw [Finset.card_univ, Fintype.card_eq_nat_card]
      show (P.map (algebraMap k L)).natDegree < Nat.card (FiniteField.Extension k p m)
      rw [Polynomial.natDegree_map, FiniteField.natCard_extension]
      have hdm : P.natDegree < m := by
        rw [hm]
        nlinarith
      exact hdm.trans (Nat.lt_pow_self Finite.one_lt_card)
  simpa only [Polynomial.map_eq_zero] using hmap

/-- A `k`-algebra automorphism of finite order of a domain of finite type over a finite field
which induces the identity on the spectrum fixes every transcendental element. -/
private lemma apply_eq_of_transcendental_of_pow_eq_one {k : Type u} {A : Type v} [Field k]
    [Finite k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (σ : A ≃ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap σ.toRingHom P = P)
    {n : ℕ} (hn : 0 < n) (horder : σ ^ n = 1) {a : A} (ha : Transcendental k a) : σ a = a := by
  set S : Set (PrimeSpectrum (Polynomial k)) := {P | ∃ m : ℕ,
    m.Coprime n ∧ Polynomial.X ^ (Nat.card k ^ m) - Polynomial.X ∈ P.asIdeal}
  have hdense : Dense S := dense_coprime_power_loci k n hn
  refine eq_of_forall_comap_aeval_mem_dense ha hdense fun P ⟨m, hmn, hm⟩ ↦ ?_
  have hmem : a ^ (Nat.card k ^ m) - a ∈ P.asIdeal := by
    change Polynomial.aeval (R := k) a
      (Polynomial.X ^ (Nat.card k ^ m) - Polynomial.X) ∈ P.asIdeal at hm
    simpa only [map_sub, map_pow, Polynomial.aeval_X] using hm
  have hle : (Ideal.span {a ^ (Nat.card k ^ m) - a}).radical ≤ P.asIdeal :=
    (Ideal.radical_mono (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))).trans_eq
      P.isPrime.isRadical.radical
  exact hle (sub_mem_radical_of_pow_eq_one σ hpoints horder hmn a)

/-- A `k`-algebra automorphism of finite order of a domain of finite type and positive Krull
dimension over a finite field `k` which induces the identity on the prime spectrum is the
identity. -/
theorem AlgEquiv.toAlgHom_eq_id_of_comap_eq_of_pow_eq_one {k : Type u} {A : Type v} [Field k]
    [Finite k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (σ : A ≃ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap σ.toRingHom P = P)
    {n : ℕ} (hn : 0 < n) (horder : σ ^ n = 1) (hdim : 0 < ringKrullDim A) :
    σ.toAlgHom = AlgHom.id k A := by
  obtain ⟨a, ha⟩ :=
    exists_transcendental_of_not_isField (k := k) (not_isField_of_ringKrullDim_pos hdim)
  exact eq_id_of_forall_transcendental_apply_eq σ.toAlgHom ha
    fun _ hb ↦ apply_eq_of_transcendental_of_pow_eq_one σ hpoints hn horder hb

/-- A `k`-algebra endomorphism of a domain of finite type over a field which induces the identity
on the prime spectrum is the identity, provided the domain is not a field and either the field is
infinite or some iterate of the endomorphism is the identity. -/
private lemma eq_id_of_comap_eq_of_not_isField {k : Type u} {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P)
    (hA : ¬ IsField A)
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ ∀ a : A, (φ : A → A)^[n] a = a) :
    φ = AlgHom.id k A := by
  obtain ⟨t, ht⟩ := exists_transcendental_of_not_isField (k := k) hA
  refine eq_id_of_forall_transcendental_apply_eq φ ht fun b hb ↦ ?_
  rcases finite_or_infinite k with hfin | hinf
  · obtain ⟨n, hn, hiter⟩ := hk.resolve_left (not_infinite_iff_finite.mpr hfin)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hinj : Function.Injective (φ : A → A) :=
      Function.LeftInverse.injective (g := (φ : A → A)^[m]) fun x ↦
        (Function.iterate_succ_apply _ m x).symm.trans (hiter x)
    have hsurj : Function.Surjective (φ : A → A) := fun x ↦
      ⟨(φ : A → A)^[m] x, (Function.iterate_succ_apply' (φ : A → A) m x).symm.trans (hiter x)⟩
    have hcoe : ((AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩ : A ≃ₐ[k] A) : A → A) = (φ : A → A) :=
      AlgEquiv.coe_ofBijective φ ⟨hinj, hsurj⟩
    have hring : (AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).toRingHom = φ.toRingHom :=
      RingHom.ext fun a ↦ congrFun hcoe a
    have hσpoints : ∀ P : PrimeSpectrum A,
        PrimeSpectrum.comap (AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).toRingHom P = P := by
      simpa only [hring] using hpoints
    have hσ : (AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩) ^ (m + 1) = 1 := by
      refine AlgEquiv.ext fun a ↦ ?_
      rw [AlgEquiv.one_apply, AlgEquiv.coe_pow, hcoe]
      exact hiter a
    exact (congrFun hcoe b).symm.trans
      (apply_eq_of_transcendental_of_pow_eq_one _ hσpoints hn hσ hb)
  · exact apply_eq_of_transcendental_of_comap_eq φ hpoints hb

/-- A `k`-algebra endomorphism inducing the identity on the spectrum descends to the quotient by
any prime ideal and still induces the identity on its spectrum. -/
private lemma comap_quotientMapₐ_eq {k : Type u} {A : Type v} [Field k] [CommRing A]
    [Algebra k A] (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P) (p : Ideal A)
    [p.IsPrime] (hp : p ≤ Ideal.comap (φ : A →+* A) p) (Q : PrimeSpectrum (A ⧸ p)) :
    PrimeSpectrum.comap (Ideal.quotientMapₐ p φ hp).toRingHom Q = Q := by
  have hQ : (Ideal.comap (Ideal.Quotient.mk p) Q.asIdeal).IsPrime := Ideal.comap_isPrime _ _
  have key : Ideal.comap φ.toRingHom (Ideal.comap (Ideal.Quotient.mk p) Q.asIdeal)
      = Ideal.comap (Ideal.Quotient.mk p) Q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (hpoints ⟨_, hQ⟩)
  refine PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_)
  ext b
  show b ∈ Ideal.comap φ.toRingHom (Ideal.comap (Ideal.Quotient.mk p) Q.asIdeal) ↔ _
  rw [key]

/-- The iterate of the endomorphism induced on the quotient by an invariant prime ideal is
induced by the iterate of the endomorphism. -/
private lemma iterate_quotientMapₐ {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (φ : A →ₐ[k] A) (p : Ideal A) [p.IsPrime] (hp : p ≤ Ideal.comap (φ : A →+* A) p) (n : ℕ)
    (b : A) :
    ((Ideal.quotientMapₐ p φ hp : A ⧸ p → A ⧸ p))^[n] (Ideal.Quotient.mk p b)
      = Ideal.Quotient.mk p ((φ : A → A)^[n] b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show (Ideal.quotientMapₐ p φ hp) (Ideal.Quotient.mk p b)
        = Ideal.Quotient.mk p (φ b) from rfl, ih]

/-- A `k`-algebra endomorphism of a reduced algebra of finite type over a field which induces the
identity on the prime spectrum is the identity, provided the quotient by no minimal prime is a
field and either the field is infinite or some iterate of the endomorphism is the identity. -/
private lemma eq_id_of_comap_eq_of_forall_not_isField {k : Type u} {A : Type v} [Field k]
    [CommRing A] [IsReduced A] [Algebra k A] [Algebra.FiniteType k A] (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P)
    (hdim : ∀ p ∈ minimalPrimes A, ¬ IsField (A ⧸ p))
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ ∀ a : A, (φ : A → A)^[n] a = a) :
    φ = AlgHom.id k A := by
  ext a
  rw [AlgHom.id_apply, ← sub_eq_zero, eq_zero_iff_mem_all_minimalPrimes]
  intro p hp
  have : p.IsPrime := hp.1.1
  have hle : p ≤ Ideal.comap (φ : A →+* A) p :=
    (congrArg PrimeSpectrum.asIdeal (hpoints ⟨p, ‹p.IsPrime›⟩)).ge
  have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  have : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.trans (inferInstanceAs (Algebra.FiniteType k A))
      (Algebra.FiniteType.of_surjective (Algebra.ofId A (A ⧸ p)) Ideal.Quotient.mk_surjective)
  have hk' : Infinite k ∨ ∃ n, 0 < n ∧ ∀ b : A ⧸ p,
      ((Ideal.quotientMapₐ p φ hle : A ⧸ p → A ⧸ p))^[n] b = b := by
    rcases hk with hinf | ⟨n, hn, hiter⟩
    · exact Or.inl hinf
    · refine Or.inr ⟨n, hn, fun b ↦ ?_⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [iterate_quotientMapₐ, hiter]
  have hid := eq_id_of_comap_eq_of_not_isField (Ideal.quotientMapₐ p φ hle)
    (comap_quotientMapₐ_eq φ hpoints p hle) (hdim p hp) hk'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact DFunLike.congr_fun hid (Ideal.Quotient.mk p a)

/-- A `k`-algebra endomorphism of a reduced algebra of finite type over a field which induces the
identity on the prime spectrum is the identity, provided the quotient by every minimal prime has
positive Krull dimension and either the field is infinite or some iterate of the endomorphism is
the identity. -/
theorem AlgHom.eq_id_of_comap_eq_of_forall_minimalPrimes_of_iterate {k : Type u} {A : Type v}
    [Field k] [CommRing A] [IsReduced A] [Algebra k A] [Algebra.FiniteType k A] (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P)
    (hdim : ∀ p ∈ minimalPrimes A, 0 < ringKrullDim (A ⧸ p))
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ ∀ a : A, (φ : A → A)^[n] a = a) :
    φ = AlgHom.id k A :=
  eq_id_of_comap_eq_of_forall_not_isField φ hpoints
    (fun p hp ↦ not_isField_of_ringKrullDim_pos (hdim p hp)) hk

/-- A `k`-algebra endomorphism of a reduced algebra of finite type over an infinite field `k`
which induces the identity on the prime spectrum is the identity, provided the quotient by every
minimal prime has positive Krull dimension. -/
theorem AlgHom.eq_id_of_comap_eq_of_forall_minimalPrimes {k : Type u} {A : Type v} [Field k]
    [Infinite k] [CommRing A] [IsReduced A] [Algebra k A] [Algebra.FiniteType k A]
    (φ : A →ₐ[k] A)
    (hpoints : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap φ.toRingHom P = P)
    (hdim : ∀ p ∈ minimalPrimes A, 0 < ringKrullDim (A ⧸ p)) : φ = AlgHom.id k A :=
  AlgHom.eq_id_of_comap_eq_of_forall_minimalPrimes_of_iterate φ hpoints hdim
    (Or.inl inferInstance)

/-- Over a finite field the hypotheses on the base field cannot be dropped for an *endomorphism*:
the `p`-power Frobenius of `(ZMod p)[X]` is a `ZMod p`-algebra endomorphism of a reduced domain of
finite type and positive Krull dimension which induces the identity on the prime spectrum and is
not the identity. It is not surjective, so it is neither an automorphism of finite order, which is
what `AlgEquiv.toAlgHom_eq_id_of_comap_eq_of_pow_eq_one` asks for, nor a counterexample to the
statement for automorphisms; but it does satisfy every hypothesis of
`AlgHom.eq_id_of_comap_eq_of_ringKrullDim_pos` apart from `Infinite k`, and every hypothesis of
`AlgHom.eq_id_of_comap_eq_of_forall_minimalPrimes_of_iterate` apart from `hk`. -/
theorem AlgHom.exists_comap_eq_ne_id_of_finite_field (p : ℕ) [hp : Fact p.Prime] :
    ∃ φ : Polynomial (ZMod p) →ₐ[ZMod p] Polynomial (ZMod p),
      (∀ P : PrimeSpectrum (Polynomial (ZMod p)),
          PrimeSpectrum.comap φ.toRingHom P = P) ∧
        0 < ringKrullDim (Polynomial (ZMod p)) ∧
        φ ≠ AlgHom.id (ZMod p) (Polynomial (ZMod p)) ∧
        ¬ Function.Surjective (φ : Polynomial (ZMod p) → Polynomial (ZMod p)) := by
  let φ : Polynomial (ZMod p) →ₐ[ZMod p] Polynomial (ZMod p) :=
    { toRingHom := frobenius (Polynomial (ZMod p)) p
      commutes' := fun c ↦ by
        show (algebraMap (ZMod p) (Polynomial (ZMod p)) c) ^ p
          = algebraMap (ZMod p) (Polynomial (ZMod p)) c
        rw [← map_pow, ZMod.pow_card] }
  have hφ : ∀ g : Polynomial (ZMod p), φ g = g ^ p := fun _ ↦ rfl
  refine ⟨φ, fun P ↦ ?_, ?_, ?_, ?_⟩
  · refine PrimeSpectrum.ext (Ideal.ext fun g ↦ ?_)
    show g ^ p ∈ P.asIdeal ↔ g ∈ P.asIdeal
    exact P.isPrime.pow_mem_iff_mem p hp.out.pos
  · have hone := ringKrullDim_succ_le_ringKrullDim_polynomial (R := ZMod p)
    rw [ringKrullDim_eq_zero_of_isField (Field.toIsField _), zero_add] at hone
    exact zero_lt_one.trans_le hone
  · intro hid
    have hX : (Polynomial.X : Polynomial (ZMod p)) ^ p = Polynomial.X :=
      DFunLike.congr_fun hid Polynomial.X
    have hdeg := congrArg Polynomial.natDegree hX
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at hdeg
    exact hp.out.one_lt.ne' hdeg
  · intro hsurj
    obtain ⟨g, hg⟩ := hsurj Polynomial.X
    rw [hφ] at hg
    have hdeg := congrArg Polynomial.natDegree hg
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hdeg
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp ⟨g.natDegree, hdeg.symm⟩)

namespace AlgebraicGeometry

/-- An endomorphism of a scheme fixing every point preserves every open subset. -/
lemma preimage_eq_of_apply_eq {X : Scheme.{u}} (f : X ⟶ X)
    (hpoints : ∀ x : X, f x = x) (U : X.Opens) : f ⁻¹ᵁ U = U := by
  ext x
  show f x ∈ U ↔ x ∈ U
  rw [hpoints x]

/-- The restriction of a point-fixing endomorphism to an open subset fixes every point. -/
lemma resLE_apply_eq_of_apply_eq {X : Scheme.{u}} (f : X ⟶ X)
    (hpoints : ∀ x : X, f x = x) (U : X.Opens) (x : U) :
    f.resLE U U (by rw [preimage_eq_of_apply_eq f hpoints]) x = x := by
  apply Subtype.ext
  rw [Scheme.Hom.coe_resLE_apply, hpoints]

/-- An endomorphism fixing every point is the identity as soon as its restriction to every
affine open subset is. -/
lemma eq_id_of_resLE_eq_id {X : Scheme.{u}} (f : X ⟶ X) (hpoints : ∀ x : X, f x = x)
    (hlocal : ∀ U : X.affineOpens,
      f.resLE U.1 U.1 (by rw [preimage_eq_of_apply_eq f hpoints]) = 𝟙 U.1.toScheme) :
    f = 𝟙 X := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨U, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f
    (show U ≤ f ⁻¹ᵁ U by rw [preimage_eq_of_apply_eq f hpoints]), hlocal ⟨U, hU⟩]
  simp

/-- On an affine scheme, an endomorphism fixing every point induces the identity on the prime
spectrum of the ring of global sections. -/
private lemma comap_appTop_eq_of_apply_eq {X : Scheme.{u}} [IsAffine X] (f : X ⟶ X)
    (hpoints : ∀ x : X, f x = x) (P : PrimeSpectrum Γ(X, ⊤)) :
    PrimeSpectrum.comap f.appTop.hom P = P := by
  obtain ⟨x, rfl⟩ := X.isoSpec.hom.homeomorph.surjective P
  have heq := congrArg (fun g : X ⟶ Spec Γ(X, ⊤) ↦ g x) (Scheme.isoSpec_hom_naturality f)
  simp only [Scheme.Hom.comp_apply, Spec.map_apply, hpoints] at heq
  exact heq

/-- The `k`-algebra structure on the global sections of a scheme over `Spec k`. -/
@[instance_reducible]
private noncomputable def algebraΓOfOver {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) : Algebra k Γ(X, ⊤) :=
  (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra

/-- Global sections of an affine scheme locally of finite type over a field form an algebra of
finite type. -/
private lemma finiteType_algebraΓ {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    letI := algebraΓOfOver p
    Algebra.FiniteType k Γ(X, ⊤) := by
  let := algebraΓOfOver p
  have hfinite : p.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (@LocallyOfFiniteType) p ‹LocallyOfFiniteType p›
  exact RingHom.finiteType_algebraMap.mp (hfinite.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective))

/-- An endomorphism over `Spec k` of an affine scheme is a `k`-algebra endomorphism of its
global sections. -/
private noncomputable def algHomAppTopOfOver {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (f : X ⟶ X) (hf : f ≫ p = p) :
    letI := algebraΓOfOver p
    Γ(X, ⊤) →ₐ[k] Γ(X, ⊤) :=
  letI := algebraΓOfOver p
  { f.appTop.hom with
    commutes' := fun c ↦ by
      have h := congrArg (fun g : X ⟶ Spec (.of k) ↦ g.appTop) hf
      exact congrArg (fun g : Γ(Spec (.of k), ⊤) ⟶ Γ(X, ⊤) ↦
        g ((Scheme.ΓSpecIso (.of k)).inv c)) h }

/-- The `n`-fold composite of a point-fixing endomorphism fixes every point. -/
private lemma iterate_apply_eq {X : Scheme.{u}} (f : X ⟶ X) (hpoints : ∀ x : X, f x = x) (n : ℕ)
    (x : X) : ((fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X)) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', Scheme.Hom.comp_apply, ih, hpoints]

/-- The `n`-fold composite of an endomorphism acts on global sections by the `n`-fold iterate. -/
private lemma iterate_appTop {X : Scheme.{u}} (f : X ⟶ X) (n : ℕ) (a : Γ(X, ⊤)) :
    ((fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X)).appTop.hom a = (fun b ↦ f.appTop.hom b)^[n] a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih,
      Function.iterate_succ_apply]

/-- Positive dimension of every irreducible component gives positive local dimension at every
point. -/
private lemma pos_topologicalKrullDimAt (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) (x : X) :
    0 < topologicalKrullDimAt X x := by
  obtain ⟨Z, hZ, -, hdimZ⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X p x
  exact hdimZ ▸ hdim Z hZ

/-- On an affine scheme locally of finite type over a field whose local dimension is positive at
every point, the quotient of the ring of global sections by a minimal prime is not a field. -/
private lemma not_isField_quotient_of_mem_minimalPrimes {k : Type u} [Field k] {X : Scheme.{u}}
    [IsAffine X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : ∀ x : X, 0 < topologicalKrullDimAt X x)
    {q : Ideal Γ(X, ⊤)} (hq : q ∈ minimalPrimes Γ(X, ⊤)) : ¬ IsField (Γ(X, ⊤) ⧸ q) := by
  intro hfield
  let := algebraΓOfOver p
  let := finiteType_algebraΓ p
  have hqp : q.IsPrime := hq.1.1
  have hmax : q.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient q).mpr hfield
  obtain ⟨x, hx⟩ := X.isoSpec.hom.homeomorph.surjective (⟨q, hqp⟩ : PrimeSpectrum Γ(X, ⊤))
  have hzero : localKrullDim (PrimeSpectrum Γ(X, ⊤)) ⟨q, hqp⟩ = 0 := by
    rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k
      (⟨q, hqp⟩ : PrimeSpectrum Γ(X, ⊤))).2]
    have hset : {𝔪 : Ideal Γ(X, ⊤) |
        𝔪.IsMaximal ∧ (⟨q, hqp⟩ : PrimeSpectrum Γ(X, ⊤)).asIdeal ≤ 𝔪} = {q} := by
      ext 𝔪
      refine ⟨fun h ↦ (hmax.eq_of_le h.1.ne_top h.2).symm, fun h ↦ ?_⟩
      subst h
      exact ⟨hmax, le_rfl⟩
    rw [hset]
    simp [Ideal.height_eq_zero_iff.mpr hq]
  have hposx : 0 < topologicalKrullDimAt (PrimeSpectrum Γ(X, ⊤)) ⟨q, hqp⟩ := by
    have h := hdim x
    rwa [topologicalKrullDimAt_eq_of_homeomorph X.isoSpec.hom.homeomorph x, hx] at h
  rw [topologicalKrullDimAt_eq_localKrullDim, hzero] at hposx
  exact lt_irrefl _ hposx

/-- An endomorphism over `k` of an affine reduced scheme locally of finite type over `k` which
fixes every point is the identity, provided the local dimension is positive at every point and
either `k` is infinite or the `n`-fold composite of the endomorphism is the identity. -/
private lemma eq_id_of_isAffine_core {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X]
    [IsReduced X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x) (hdim : ∀ x : X, 0 < topologicalKrullDimAt X x)
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ (fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X) = 𝟙 X) :
    f = 𝟙 X := by
  let := algebraΓOfOver p
  let := finiteType_algebraΓ p
  have hiter : Infinite k ∨ ∃ n, 0 < n ∧ ∀ a : Γ(X, ⊤),
      ((algHomAppTopOfOver p f hf : Γ(X, ⊤) → Γ(X, ⊤)))^[n] a = a := by
    rcases hk with hinf | ⟨n, hn, hfn⟩
    · exact Or.inl hinf
    · refine Or.inr ⟨n, hn, fun a ↦ ?_⟩
      have hcoe : ((algHomAppTopOfOver p f hf : Γ(X, ⊤) → Γ(X, ⊤)))
          = fun b ↦ f.appTop.hom b := rfl
      have h := iterate_appTop f n a
      rw [hfn] at h
      simp only [Scheme.Hom.id_appTop] at h
      rw [hcoe, ← h]
      rfl
  have hidentity := eq_id_of_comap_eq_of_forall_not_isField (algHomAppTopOfOver p f hf)
    (comap_appTop_eq_of_apply_eq f hpoints)
    (fun q hq ↦ not_isField_quotient_of_mem_minimalPrimes p hdim hq) hiter
  exact ext_of_isAffine (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hidentity))

/-- An endomorphism over `k` of an affine reduced scheme locally of finite type over `k` which
fixes every point is the identity, provided every irreducible component has positive dimension
and either `k` is infinite or the `n`-fold composite of the endomorphism is the identity. -/
theorem eq_id_of_isAffine_of_eq_on_points {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X]
    [IsReduced X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ (fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X) = 𝟙 X) :
    f = 𝟙 X :=
  eq_id_of_isAffine_core p f hf hpoints (pos_topologicalKrullDimAt k X p hdim) hk

/-- Restrictions of equal endomorphisms to a stable open subset agree. -/
private lemma resLE_eq_resLE {X : Scheme.{u}} {U : X.Opens} {g h : X ⟶ X} (hgh : g = h)
    (eg : U ≤ g ⁻¹ᵁ U) (eh : U ≤ h ⁻¹ᵁ U) : g.resLE U U eg = h.resLE U U eh := by
  subst hgh
  rfl

/-- The restriction of the identity to an open subset is the identity. -/
private lemma resLE_id_eq_id {X : Scheme.{u}} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) :
    Scheme.Hom.resLE (𝟙 X) U U e = 𝟙 U.toScheme := by
  rw [← cancel_mono U.ι, Scheme.Hom.resLE_comp_ι]
  simp

/-- Restricting the `n`-fold composite of a point-fixing endomorphism to an open subset is the
`n`-fold composite of the restriction. -/
private lemma iterate_resLE {X : Scheme.{u}} (f : X ⟶ X) (hpoints : ∀ x : X, f x = x)
    (U : X.Opens) (n : ℕ) :
    ∀ (g : X ⟶ X) (_ : (fun h : X ⟶ X ↦ h ≫ f)^[n] (𝟙 X) = g) (eg : U ≤ g ⁻¹ᵁ U),
      (fun h : U.toScheme ⟶ U.toScheme ↦
          h ≫ f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge)^[n] (𝟙 U.toScheme)
        = g.resLE U U eg := by
  induction n with
  | zero =>
    rintro g rfl eg
    exact (resLE_id_eq_id U eg).symm
  | succ n ih =>
    intro g hg eg
    have en : U ≤ ((fun h : X ⟶ X ↦ h ≫ f)^[n] (𝟙 X)) ⁻¹ᵁ U :=
      (preimage_eq_of_apply_eq _ (iterate_apply_eq f hpoints n) U).ge
    rw [Function.iterate_succ_apply', ih _ rfl en]
    exact (Scheme.Hom.resLE_comp_resLE _ en f _).trans
      (resLE_eq_resLE
        ((Function.iterate_succ_apply' (fun h : X ⟶ X ↦ h ≫ f) n (𝟙 X)).symm.trans hg) _ _)

/-- **Stacks 0G05 (2)**: an endomorphism over `k` of a reduced scheme locally of finite type over
`k` which fixes every point of the underlying topological space is the identity, provided every
irreducible component has positive dimension. Over an infinite field this is unconditional; over
a finite field the order of the endomorphism is carried as an explicit hypothesis. -/
-- The `@[stacks 0G05]` registration is deliberately absent here: this statement assumes its
-- own input, and eq_id_of_isIso_of_eq_on_points (PointwiseTrivialAut.lean) assumes nothing about
-- the base field.
-- A tag does not go on a declaration proved under hypotheses the source does not make.
theorem eq_id_of_eq_on_points {k : Type u} [Field k] {X : Scheme.{u}} [IsReduced X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ (fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X) = 𝟙 X) :
    f = 𝟙 X := by
  refine eq_id_of_resLE_eq_id f hpoints fun U ↦ ?_
  have : IsAffine U.1.toScheme := U.2
  have : IsReduced U.1.toScheme := isReduced_of_isOpenImmersion U.1.ι
  have hdimU : ∀ y : U.1.toScheme, 0 < topologicalKrullDimAt U.1.toScheme y := by
    intro y
    have h := pos_topologicalKrullDimAt k X p hdim y.1
    rwa [U.1.isOpen.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq y] at h
  have hkU : Infinite k ∨ ∃ n, 0 < n ∧
      (fun g : U.1.toScheme ⟶ U.1.toScheme ↦
        g ≫ f.resLE U.1 U.1 (preimage_eq_of_apply_eq f hpoints U.1).ge)^[n] (𝟙 U.1.toScheme)
        = 𝟙 U.1.toScheme := by
    rcases hk with hinf | ⟨n, hn, hfn⟩
    · exact Or.inl hinf
    · refine Or.inr ⟨n, hn, ?_⟩
      rw [iterate_resLE f hpoints U.1 n (𝟙 X) hfn (le_of_eq (by simp))]
      exact resLE_id_eq_id U.1 _
  refine eq_id_of_isAffine_core (U.1.ι ≫ p) _ ?_
    (resLE_apply_eq_of_apply_eq f hpoints U.1) hdimU hkU
  rw [Scheme.Hom.resLE_comp_ι_assoc, hf]

/-- An endomorphism over `k` of an integral scheme of positive dimension, locally of finite type
over `k`, which fixes every point of the underlying topological space is the identity. -/
theorem eq_id_of_isIntegral_of_eq_on_points {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x) (hdim : 0 < topologicalKrullDim X)
    (hk : Infinite k ∨ ∃ n, 0 < n ∧ (fun g : X ⟶ X ↦ g ≫ f)^[n] (𝟙 X) = 𝟙 X) :
    f = 𝟙 X := by
  refine eq_id_of_eq_on_points p f hf hpoints (fun Z hZ ↦ ?_) hk
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
  subst hZ
  rwa [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph]

end AlgebraicGeometry

end
