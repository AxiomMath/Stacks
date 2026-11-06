module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.DedekindPlaces
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.PolynomialSubring

/-!
# The places of a function field containing a given element

Let `k` be a finite field, `K` a field extension of `k` and `x ∈ K` such that `K` is a finite
extension of `k(x)`. Every place of `K` contains `k`. A place containing `x` contains the integral
closure `B` of `k[x]` in `K`, so it is the place at a height-one prime of the Dedekind domain `B`.
Hence it is discrete, with finite residue field.

For a nonzero polynomial `f ∈ k[X]`, the *fundamental inequality* bounds the zeros of `f(x)` at
the places containing `x`: `∏_v q_v ^ ord_v (f(x)) ≤ #k ^ ([K : k(x)] · deg f)`, the product over
any finite set of places containing `x`, where `q_v` is the cardinality of the residue field.

## Main definitions

* `Stacks.Adeles.Place.ord` — the order `-log v(y)` of `y` for the normalized valuation of `v`.
* `Stacks.Adeles.Place.resCard` — the cardinality of the residue field of `v`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.algebraMap_mem_place` — every place contains `k`.
* `Stacks.Adeles.GlobalFunctionField.exists_eq_ofHeightOneSpectrum_intClosure` — a place
  containing `x` is the place at a height-one prime of the integral closure of `k[x]`.
* `Stacks.Adeles.GlobalFunctionField.prod_resCard_pow_ord_le` — the fundamental inequality.
-/

@[expose] public noncomputable section

open Polynomial IsDedekindDomain IntermediateField IntermediateField.algebraAdjoinAdjoin WithZero

universe u

namespace Stacks.Adeles

namespace Place

variable {K : Type u} [Field K]

/-- The order of `y` at a place `v`: minus the logarithm of its normalized valuation. -/
public def ord (v : Place K) (y : K) : ℤ := -log (v.normVal y)

/-- The cardinality of the residue field of a place. -/
public def resCard (v : Place K) : ℕ := Nat.card (IsLocalRing.ResidueField v.1)

/-- For a discrete place, `v(y) ≤ 1` exactly when `y ∈ v`. -/
public theorem normVal_le_one_iff {v : Place K} (hv : v.IsDiscrete) {y : K} :
    v.normVal y ≤ 1 ↔ y ∈ v.1 := by
  rw [← Valuation.mem_valuationSubring_iff, (normVal_spec hv).1]

/-- The order at a place is additive on products of nonzero elements. -/
public theorem ord_mul (v : Place K) {y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    v.ord (y * z) = v.ord y + v.ord z := by
  rw [ord, ord, ord, map_mul, log_mul (by simpa using hy) (by simpa using hz), neg_add]

/-- The order of `y ^ n` at a place is `n` times the order of `y`. -/
public theorem ord_pow (v : Place K) (y : K) (n : ℕ) : v.ord (y ^ n) = n * v.ord y := by
  rw [ord, ord, map_pow, log_pow, nsmul_eq_mul, mul_neg]

/-- At a discrete place `v`, a nonzero `y` has nonnegative order exactly when `y ∈ v`. -/
public theorem ord_nonneg_iff {v : Place K} (hv : v.IsDiscrete) {y : K} (hy : y ≠ 0) :
    0 ≤ v.ord y ↔ y ∈ v.1 := by
  rw [ord, neg_nonneg, ← normVal_le_one_iff hv, log_le_iff_le_exp (by simpa using hy), exp_zero]

variable {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]

/-- `B ⧸ P` is equivalent to the residue field of the place at a height-one prime `P`. -/
private theorem nonempty_equiv_residueField_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    Nonempty (B ⧸ P.asIdeal ≃ IsLocalRing.ResidueField (ofHeightOneSpectrum (K := K) P).1) := by
  have := P.isMaximal
  rw [ofHeightOneSpectrum_val, ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact ⟨(IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal
    (HeightOneSpectrum.valuationSubringAtPrime K P)).toEquiv⟩

/-- The residue field of the place at a height-one prime `P` of `B` is `B ⧸ P`. -/
public theorem resCard_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum (K := K) P).resCard = Nat.card (B ⧸ P.asIdeal) :=
  (Nat.card_congr (nonempty_equiv_residueField_ofHeightOneSpectrum (K := K) P).some).symm

/-- The order of `b ∈ B` at the place of a height-one prime `P` is the multiplicity of `P` in
`(b)`. -/
public theorem ord_ofHeightOneSpectrum (P : HeightOneSpectrum B) {b : B} (hb : b ≠ 0) :
    (ofHeightOneSpectrum (K := K) P).ord (algebraMap B K b) =
      multiplicity P.asIdeal (Ideal.span {b}) := by
  rw [ord, normVal_ofHeightOneSpectrum, HeightOneSpectrum.valuation_of_algebraMap,
    P.intValuation_eq_exp_neg_multiplicity hb, log_exp, neg_neg]

/-- The fundamental inequality over a Dedekind extension `A ⊆ B`, `B` finite and flat over `A`
with fraction field `K`: for a prime `a ∈ A` and a finite set `s` of places of `K` containing `B`,
`∏_{v ∈ s} q_v ^ ord_v (a) ≤ #(A ⧸ (a)) ^ rank_A B`. -/
public theorem prod_resCard_pow_ord_le_of_prime {A : Type u} [CommRing A] [IsDedekindDomain A]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B] [FaithfulSMul A B] {a : A} (ha : Prime a)
    [Finite (A ⧸ Ideal.span {a})] (s : Finset (Place K))
    (hs : ∀ v ∈ s, ∀ b : B, algebraMap B K b ∈ v.1) :
    ∏ v ∈ s, v.resCard ^ (v.ord (algebraMap B K (algebraMap A B a))).toNat ≤
      Nat.card (A ⧸ Ideal.span {a}) ^ Module.finrank A B := by
  classical
  set p : Ideal A := Ideal.span {a}
  have hpmax : p.IsMaximal := by
    have : p.IsPrime := (Ideal.span_singleton_prime ha.ne_zero).2 ha
    exact this.isMaximal (by simpa [p] using ha.ne_zero)
  set b : B := algebraMap A B a
  have hb0 : b ≠ 0 := fun h => ha.ne_zero
    (FaithfulSMul.algebraMap_injective A B (h.trans (map_zero _).symm))
  have hP : ∀ v ∈ s, ∃ P : HeightOneSpectrum B, v = ofHeightOneSpectrum P :=
    fun v hv => (exists_eq_ofHeightOneSpectrum v (hs v hv)).imp fun _ h => h.1
  rcases s.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · simpa using Nat.one_le_pow _ _ Nat.card_pos
  have : Nonempty (HeightOneSpectrum B) := ⟨(hP v₀ hv₀).choose⟩
  choose! Q hQ using hP
  have hord : ∀ v ∈ s, v.ord (algebraMap B K b) = multiplicity (Q v).asIdeal (Ideal.span {b}) := by
    intro v hv
    have := ord_ofHeightOneSpectrum (K := K) (Q v) hb0
    rwa [← hQ v hv] at this
  have hcard : ∀ v ∈ s, v.resCard = Nat.card (B ⧸ (Q v).asIdeal) := by
    intro v hv
    have := resCard_ofHeightOneSpectrum (K := K) (Q v)
    rwa [← hQ v hv] at this
  set s₁ := s.filter fun v => b ∈ (Q v).asIdeal
  have hmul0 : ∀ v ∈ s, b ∉ (Q v).asIdeal → multiplicity (Q v).asIdeal (Ideal.span {b}) = 0 := by
    intro v _ hb
    exact multiplicity_eq_zero_of_not_dvd (by rwa [Ideal.dvd_span_singleton])
  have hprod : ∏ v ∈ s, v.resCard ^ (v.ord (algebraMap B K b)).toNat =
      ∏ v ∈ s₁, v.resCard ^ (v.ord (algebraMap B K b)).toNat := by
    refine (Finset.prod_filter_of_ne fun v hv hne => ?_).symm
    by_contra hb
    rw [hord v hv, hmul0 v hv hb] at hne
    simp at hne
  have hover : ∀ v ∈ s₁, (Q v).asIdeal ∈ p.primesOver B := by
    intro v hv
    rw [Finset.mem_filter] at hv
    refine ⟨(Q v).isPrime, ⟨?_⟩⟩
    have hle : p ≤ (Q v).asIdeal.under A := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hv.2
    exact hpmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  have hinj : Set.InjOn (fun v => (Q v).asIdeal) s₁ := by
    intro v hv w hw h
    have hv' := (Finset.mem_filter.1 hv).1
    have hw' := (Finset.mem_filter.1 hw).1
    calc v = ofHeightOneSpectrum (Q v) := hQ v hv'
      _ = ofHeightOneSpectrum (Q w) := by rw [HeightOneSpectrum.ext h]
      _ = w := (hQ w hw').symm
  have hmapne : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    rwa [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  have he : ∀ v ∈ s₁, (v.ord (algebraMap B K b)).toNat = (Q v).asIdeal.ramificationIdx A := by
    intro v hv
    have hv' := (Finset.mem_filter.1 hv).1
    have : (Q v).asIdeal.LiesOver p := (hover v hv).2
    rw [hord v hv', Int.toNat_natCast,
      Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p _ hmapne,
      Ideal.map_span, Set.image_singleton,
      UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
        (Ideal.prime_of_isPrime (Q v).ne_bot (Q v).isPrime).irreducible
        (by simpa using hb0), normalize_eq]
  have hf' : ∀ v ∈ s₁, v.resCard = Nat.card (A ⧸ p) ^ (Q v).asIdeal.inertiaDeg A := by
    intro v hv
    have hv' := (Finset.mem_filter.1 hv).1
    have : (Q v).asIdeal.LiesOver p := (hover v hv).2
    have := (Q v).isMaximal
    have : Module.Finite (A ⧸ p) (B ⧸ (Q v).asIdeal) := module_finite_of_liesOver _ p
    rw [hcard v hv', Ideal.inertiaDeg_eq_of_isMaximal p, Module.natCard_eq_pow_finrank (K := A ⧸ p)]
  have hsum : ∑ v ∈ s₁, (Q v).asIdeal.ramificationIdx A * (Q v).asIdeal.inertiaDeg A ≤
      Module.finrank A B := by
    rw [← Ideal.sum_ramification_inertia_eq_finrank p B]
    calc ∑ v ∈ s₁, (Q v).asIdeal.ramificationIdx A * (Q v).asIdeal.inertiaDeg A
        = ∑ q ∈ s₁.image (fun v => (Q v).asIdeal), q.ramificationIdx A * q.inertiaDeg A :=
          (Finset.sum_image (f := fun q : Ideal B => q.ramificationIdx A * q.inertiaDeg A)
            hinj).symm
      _ ≤ ∑ q ∈ (p.primesOver B).toFinset, q.ramificationIdx A * q.inertiaDeg A := by
          refine Finset.sum_le_sum_of_subset ?_
          intro q hq
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
          exact Set.mem_toFinset.2 (hover v hv)
      _ = ∑ q : p.primesOver B, (q.1).ramificationIdx A * (q.1).inertiaDeg A :=
          Finset.sum_subtype _ (fun q => Set.mem_toFinset) _
  calc ∏ v ∈ s, v.resCard ^ (v.ord (algebraMap B K b)).toNat
      = ∏ v ∈ s₁, (Nat.card (A ⧸ p)) ^
          ((Q v).asIdeal.ramificationIdx A * (Q v).asIdeal.inertiaDeg A) := by
        rw [hprod]
        refine Finset.prod_congr rfl fun v hv => ?_
        rw [hf' v hv, he v hv, ← pow_mul, mul_comm]
    _ = Nat.card (A ⧸ p) ^
          ∑ v ∈ s₁, (Q v).asIdeal.ramificationIdx A * (Q v).asIdeal.inertiaDeg A :=
        Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ Nat.card (A ⧸ p) ^ Module.finrank A B :=
        Nat.pow_le_pow_right Nat.card_pos hsum

end Place

namespace GlobalFunctionField

/-- If `B` is a finite `A`-algebra and `A ⧸ (P ∩ A)` is finite, then `B ⧸ P` is finite. -/
public theorem finite_quotient_of_finite_under {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (P : Ideal B) [Finite (A ⧸ P.under A)] : Finite (B ⧸ P) :=
  Module.finite_of_finite (A ⧸ P.under A)

variable {k : Type u} [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]

/-- An element of `K` integral over a place `v` lies in `v`. -/
private theorem mem_place_of_isIntegral (v : Place K) {z : K} (h : IsIntegral v.1 z) : z ∈ v.1 := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

/-- Every place of `K` contains the finite field `k`: its elements are integral over `ℤ`. -/
public theorem algebraMap_mem_place (v : Place K) (c : k) : algebraMap k K c ∈ v.1 := by
  classical
  let := Fintype.ofFinite k
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hc : IsIntegral ℤ c := ⟨X ^ Fintype.card k - X,
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hq), by simp [FiniteField.pow_card]⟩
  exact mem_place_of_isIntegral v (hc.map ((algebraMap k K).toIntAlgHom)).tower_top

/-- `k[x]` is contained in every place containing `x`. -/
public theorem polySubalg_le_place (v : Place K) {x : K} (hx : x ∈ v.1) :
    ∀ a : polySubalg k x, (a : K) ∈ v.1 := by
  let vk : Subalgebra k K := { v.1.toSubring with algebraMap_mem' := algebraMap_mem_place v }
  have : polySubalg k x ≤ vk := Algebra.adjoin_le (Set.singleton_subset_iff.2 hx)
  exact fun a => this a.2

/-- The integral closure of `k[x]` is contained in every place containing `x`. -/
public theorem intClosure_le_place (v : Place K) {x : K} (hx : x ∈ v.1) (b : intClosure k x) :
    (b : K) ∈ v.1 := by
  obtain ⟨p, hpm, hp⟩ := (mem_integralClosure_iff _ _).1 b.2
  have hle : (polySubalg k x).toSubring ≤ v.1.toSubring := fun a ha =>
    polySubalg_le_place v hx ⟨a, ha⟩
  let φ : polySubalg k x →+* v.1 := Subring.inclusion hle
  exact mem_place_of_isIntegral v ⟨p.map φ, hpm.map φ, by rw [eval₂_map]; exact hp⟩

variable (k) (x : K) [FiniteDimensional k⟮x⟯ K]

include k

/-- A place containing `x` is the place at a height-one prime of the integral closure of `k[x]`,
namely the prime of elements of positive order. -/
public theorem exists_eq_ofHeightOneSpectrum_intClosure (v : Place K) (hx : x ∈ v.1) :
    ∃ P : HeightOneSpectrum (intClosure k x), v = Place.ofHeightOneSpectrum P ∧
      ∀ b : intClosure k x, b ∈ P.asIdeal ↔ v.1.valuation (b : K) < 1 :=
  Place.exists_eq_ofHeightOneSpectrum v (intClosure_le_place v hx)

/-- A place containing `x` is discrete. -/
public theorem isDiscrete_of_mem (v : Place K) (hx : x ∈ v.1) : v.IsDiscrete :=
  Place.isDiscrete_of_forall_mem (B := intClosure k x) v (intClosure_le_place v hx)

omit [FiniteDimensional k⟮x⟯ K] in
/-- The quotients of `k[x]` by nonzero ideals are finite. -/
public theorem finite_quotient_polySubalg (q : Ideal (polySubalg k x)) (hq : q ≠ ⊥) :
    Finite (polySubalg k x ⧸ q) := by
  let g : k[X] →+* polySubalg k x := (polySubalgMap (k := k) x).toRingHom
  let I := q.comap g
  have hI : I ≠ ⊥ := by
    intro h
    apply hq
    rw [← Ideal.map_comap_of_surjective g (polySubalgMap_surjective (k := k) x) q]
    show Ideal.map g I = ⊥
    rw [h, Ideal.map_bot]
  obtain ⟨f, hf⟩ := (Submodule.IsPrincipal.principal I)
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hI
    rw [hf]
    simp
  have : Finite (AdjoinRoot f) := by
    have := (AdjoinRoot.powerBasis hf0).finite
    exact Module.finite_of_finite k
  have hsurj : Function.Surjective (Ideal.quotientMap q g le_rfl) :=
    Ideal.quotientMap_surjective (polySubalgMap_surjective x)
  have : Finite (k[X] ⧸ I) := by
    rw [show I = Ideal.span {f} from hf]
    exact this
  exact Finite.of_surjective _ hsurj

/-- The quotients of the integral closure of `k[x]` by nonzero primes are finite. -/
public theorem finite_quotient_intClosure (P : Ideal (intClosure k x)) [P.IsPrime]
    (hP : P ≠ ⊥) : Finite (intClosure k x ⧸ P) := by
  let p := P.under (polySubalg k x)
  have hp : p ≠ ⊥ := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact Ideal.comap_ne_bot_of_integral_mem hb0 hb (Algebra.IsIntegral.isIntegral b)
  have := finite_quotient_polySubalg k x p hp
  exact finite_quotient_of_finite_under (A := polySubalg k x) P

/-- The residue field of a place containing `x` is finite. -/
public theorem finite_residueField_of_mem (v : Place K) (hx : x ∈ v.1) :
    Finite (IsLocalRing.ResidueField v.1) := by
  obtain ⟨P, rfl, -⟩ := exists_eq_ofHeightOneSpectrum_intClosure k x v hx
  have := P.isMaximal
  have := finite_quotient_intClosure k x P.asIdeal P.ne_bot
  exact Finite.of_equiv _ (Place.nonempty_equiv_residueField_ofHeightOneSpectrum (K := K) P).some

section FundamentalInequality

set_option synthInstance.maxHeartbeats 100000 in
/-- The rank of the integral closure of `k[x]` over `k[x]` is `[K : k(x)]`. -/
public theorem finrank_intClosure :
    Module.finrank (polySubalg k x) (intClosure k x) = Module.finrank k⟮x⟯ K := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (intClosure k x)
      (nonZeroDivisors (polySubalg k x))) K :=
    IsIntegralClosure.isLocalization (polySubalg k x) k⟮x⟯ K (intClosure k x)
  let b := Module.Free.chooseBasis (polySubalg k x) (intClosure k x)
  let b' := Module.Basis.localizationLocalization k⟮x⟯ (nonZeroDivisors (polySubalg k x)) K b
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b']

omit [Finite k] [FiniteDimensional k⟮x⟯ K] in
/-- For transcendental `x` and `f ≠ 0`, the quotient `k[x] ⧸ (f(x))` has `#k ^ deg f`
elements. -/
public theorem card_quotient_span_polySubalgMap (hx : Transcendental k x) {f : k[X]} (hf : f ≠ 0) :
    Nat.card (polySubalg k x ⧸ Ideal.span {polySubalgMap (k := k) x f}) =
      Nat.card k ^ f.natDegree := by
  let e : k[X] ≃+* polySubalg k x := (polySubalgEquiv hx).toRingEquiv
  have hmap : Ideal.span {polySubalgMap (k := k) x f} = (Ideal.span {f}).map e := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e hmap).toEquiv.symm]
  have := (AdjoinRoot.powerBasis hf).finite
  show Nat.card (AdjoinRoot f) = _
  rw [Module.natCard_eq_pow_finrank (K := k), (AdjoinRoot.powerBasis hf).finrank,
    AdjoinRoot.powerBasis_dim]

set_option synthInstance.maxHeartbeats 100000 in
/-- The fundamental inequality at a prime polynomial: for any finite set `s` of places containing
`x`, `∏_{v ∈ s} q_v ^ ord_v (f(x)) ≤ #k ^ ([K : k(x)] · deg f)`. -/
public theorem prod_resCard_pow_ord_le_of_prime (hx : Transcendental k x) {f : k[X]}
    (hf : Prime f) (s : Finset (Place K)) (hs : ∀ v ∈ s, x ∈ v.1) :
    ∏ v ∈ s, v.resCard ^ (v.ord (aeval x f)).toNat ≤
      Nat.card k ^ (Module.finrank k⟮x⟯ K * f.natDegree) := by
  set a : polySubalg k x := polySubalgMap (k := k) x f
  have haprime : Prime a := by
    simpa [a] using (MulEquiv.prime_iff (polySubalgEquiv hx).toMulEquiv).2 hf
  have : FaithfulSMul (polySubalg k x) (intClosure k x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun c d h => Subtype.ext
      (congrArg (algebraMap (intClosure k x) K) h)
  have : Finite (polySubalg k x ⧸ Ideal.span {a}) :=
    finite_quotient_polySubalg k x _ (by simpa using haprime.ne_zero)
  have key := Place.prod_resCard_pow_ord_le_of_prime (K := K) (B := intClosure k x) haprime s
    fun v hv => intClosure_le_place v (hs v hv)
  rwa [card_quotient_span_polySubalgMap k x hx hf.ne_zero, ← pow_mul, finrank_intClosure k x,
    mul_comm] at key

/-- The order of a nonzero element of `k[x]` at a place containing `x` is nonnegative. -/
public theorem ord_aeval_nonneg {v : Place K} (hv : x ∈ v.1) {f : k[X]} (hf : aeval x f ≠ 0) :
    0 ≤ v.ord (aeval x f) :=
  (Place.ord_nonneg_iff (isDiscrete_of_mem k x v hv) hf).2
    (polySubalg_le_place v hv (polySubalgMap (k := k) x f))

/-- The fundamental inequality: for a nonzero polynomial `f` and any finite set `s` of places
containing `x`, `∏_{v ∈ s} q_v ^ ord_v (f(x)) ≤ #k ^ ([K : k(x)] · deg f)`. -/
public theorem prod_resCard_pow_ord_le (hx : Transcendental k x) {f : k[X]} (hf : f ≠ 0)
    (s : Finset (Place K)) (hs : ∀ v ∈ s, x ∈ v.1) :
    ∏ v ∈ s, v.resCard ^ (v.ord (aeval x f)).toNat ≤
      Nat.card k ^ (Module.finrank k⟮x⟯ K * f.natDegree) := by
  have hne : ∀ g : k[X], g ≠ 0 → aeval x g ≠ 0 := fun g hg h =>
    hg (transcendental_iff_injective.1 hx (h.trans (map_zero _).symm))
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hf
  | h₂ u hu =>
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hu
    have h0 : ∀ v ∈ s, v.ord (aeval x (C c)) = 0 := by
      intro v hv
      have hc0 : algebraMap k K c ≠ 0 := by simpa using hc.ne_zero
      have hvd := isDiscrete_of_mem k x v (hs v hv)
      have h1 := (Place.ord_nonneg_iff hvd hc0).2 (algebraMap_mem_place v c)
      have h2 := (Place.ord_nonneg_iff hvd (inv_ne_zero hc0)).2
        (by simpa using algebraMap_mem_place v c⁻¹)
      have h3 := Place.ord_mul v hc0 (inv_ne_zero hc0)
      rw [mul_inv_cancel₀ hc0, Place.ord, map_one, log_one, neg_zero] at h3
      rw [aeval_C]
      omega
    rw [Finset.prod_congr rfl fun v hv => by rw [h0 v hv]]
    simp
  | h₃ a q ha hq ih =>
    have hqa : aeval x q ≠ 0 := hne q hq.ne_zero
    have haa : aeval x a ≠ 0 := hne a ha
    have hsplit : ∀ v ∈ s, (v.ord (aeval x (q * a))).toNat =
        (v.ord (aeval x q)).toNat + (v.ord (aeval x a)).toNat := by
      intro v hv
      rw [map_mul, Place.ord_mul v hqa haa]
      exact Int.toNat_add (ord_aeval_nonneg k x (hs v hv) hqa)
        (ord_aeval_nonneg k x (hs v hv) haa)
    rw [Finset.prod_congr rfl fun v hv => by rw [hsplit v hv, pow_add], Finset.prod_mul_distrib,
      natDegree_mul hq.ne_zero ha, mul_add, pow_add]
    exact Nat.mul_le_mul (prod_resCard_pow_ord_le_of_prime k x hx hq s hs) (ih ha)

end FundamentalInequality

end GlobalFunctionField

end Stacks.Adeles

end
