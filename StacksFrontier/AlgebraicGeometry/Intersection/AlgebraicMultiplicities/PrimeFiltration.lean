module

public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.Additivity
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Length.Additivity
public import StacksFrontier.RingTheory.KrullDimension.Module
import StacksFrontier.RingTheory.Dualizing.Depth

/-!
# Multiplicity as a sum of multiplicities of prime quotients

The Hilbert–Samuel multiplicity of a finite module in a degree at least its support dimension
is the sum of the multiplicities of the prime quotients of that dimension, each weighted by
the length of the corresponding localization of the module. The proof filters the module by a
chain whose successive factors are prime quotients, uses additivity of multiplicity along
that chain, and discards the factors whose prime has smaller quotient dimension.

## Main results

* `Ideal.hilbertSamuelMultiplicity_eq_finsum_localizedLength_mul` expresses Hilbert–Samuel
  multiplicity as a sum over primes of the specified dimension.

## Implementation notes

The sum in the source is represented by `finsum`. Its coefficient at a prime `p` is the
natural-number length of `M_p`, cast to `ℚ`; under the hypotheses the localizations occurring
with nonzero coefficient have finite length. Prime ideals are represented by
`PrimeSpectrum R`, and `dim(R / p) = d` is expressed using `ringKrullDim`.

## References

* [Stacks Project, Tag 0AZX](https://stacks.math.columbia.edu/tag/0AZX)
-/

@[expose] public section

open Filter Polynomial

namespace Ideal

/-- The Hilbert–Samuel degree of a finite module for an ideal of definition does not depend on
the ideal: it is the degree taken at the maximal ideal. -/
private lemma hilbertSamuelDegree_eq_module_hilbertSamuelDegree
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Ideal R) (hI : IsIdealOfDefinition I) :
    I.hilbertSamuelDegree N = Module.hilbertSamuelDegree R N := by
  obtain ⟨_de, e, he⟩ :=
    Ideal.exists_degree_eq_of_eventually_eval_eq_length_quotient_smul_pow (R := R) N
  obtain ⟨P, hP⟩ := exists_computesHilbertSamuelPoly I hI N
  obtain ⟨Q, hQ⟩ := exists_computesHilbertSamuelPoly (IsLocalRing.maximalIdeal R)
    ((IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical) N
  rw [hilbertSamuelDegree_eq_degree_of_computes hP,
    show Module.hilbertSamuelDegree R N = (IsLocalRing.maximalIdeal R).hilbertSamuelDegree N
      from rfl,
    hilbertSamuelDegree_eq_degree_of_computes hQ, (he I hI P).2 hP,
    (he (IsLocalRing.maximalIdeal R)
      ((IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical) Q).2 hQ]

/-- Mapping `WithBot ℕ` into `WithBot ℕ∞` reflects strict inequalities. -/
private lemma withBot_map_natCast_lt_iff {x y : WithBot ℕ} :
    WithBot.map (Nat.cast : ℕ → ℕ∞) x < WithBot.map (Nat.cast : ℕ → ℕ∞) y ↔ x < y := by
  cases x <;> cases y <;> simp

/-- A module whose support has dimension strictly below `d` has multiplicity zero in degree
`d`: its computing polynomial has degree below `d`, so the coefficient vanishes. -/
private lemma hilbertSamuelMultiplicity_eq_zero_of_supportDim_lt
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ)
    (hd : Module.supportDim R N < d) : I.hilbertSamuelMultiplicity N d = 0 := by
  obtain ⟨P, hP⟩ := exists_computesHilbertSamuelPoly I hI N
  rw [hilbertSamuelMultiplicity_eq_factorial_mul_coeff I N hP d,
    Polynomial.coeff_eq_zero_of_degree_lt, mul_zero]
  apply withBot_map_natCast_lt_iff.mp
  rw [← hilbertSamuelDegree_eq_degree_of_computes hP,
    hilbertSamuelDegree_eq_module_hilbertSamuelDegree I hI,
    Module.hilbertSamuelDegree_eq_supportDim]
  simpa using hd

/-- The multiplicity of a zero module vanishes in every degree. -/
private lemma hilbertSamuelMultiplicity_eq_zero_of_subsingleton
    {R N : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Subsingleton N]
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ) :
    I.hilbertSamuelMultiplicity N d = 0 :=
  hilbertSamuelMultiplicity_eq_zero_of_supportDim_lt I hI d (by
    simp [Module.supportDim, Module.support_eq_empty_iff.mpr ‹_›, Order.krullDim_eq_bot])

/-- A telescoping identity: if each successive value of `w` adds the corresponding value of
`c`, the last value is the first plus the total. -/
private lemma eq_add_sum_of_forall_succ_eq_add {A : Type*} [AddCommMonoid A] {n : ℕ}
    (w : Fin (n + 1) → A) (c : Fin n → A)
    (hstep : ∀ i : Fin n, w i.succ = w i.castSucc + c i) :
    w (Fin.last n) = w 0 + ∑ i, c i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fin.succ_last, hstep (Fin.last n), ih (fun j => w j.castSucc)
      (fun i => c i.castSucc) (fun i => by rw [← Fin.succ_castSucc]; exact hstep i.castSucc),
      Fin.castSucc_zero, Fin.sum_univ_castSucc, add_assoc]

/-- The support dimension of a submodule is at most that of the ambient module. -/
private lemma supportDim_submodule_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Module.supportDim R N ≤ Module.supportDim R M :=
  Module.supportDim_le_of_injective N.subtype N.subtype_injective

/-- Multiplicity is invariant under a linear equivalence, in a degree at least the support
dimension. -/
private lemma multiplicity_congr
    {R A B : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ) (e : A ≃ₗ[R] B)
    (hd : Module.supportDim R B ≤ d) :
    I.hilbertSamuelMultiplicity A d = I.hilbertSamuelMultiplicity B d := by
  have h := hilbertSamuelMultiplicity_additive_of_exact I hI d
    (f := e.toLinearMap) (g := (0 : B →ₗ[R] (⊥ : Submodule R B))) e.injective
    (fun x => ⟨fun _ => ⟨e.symm x, by simp⟩, by rintro ⟨y, rfl⟩; simp⟩)
    (fun x => ⟨0, Subsingleton.elim _ _⟩) hd
  simpa [hilbertSamuelMultiplicity_eq_zero_of_subsingleton (N := (⊥ : Submodule R B)) I hI d]
    using h.symm

/-- Multiplicity in a degree at least the support dimension is the sum of the multiplicities
of the successive factors of any filtration of the module. -/
private lemma multiplicity_eq_sum_filtration
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ)
    (hd : Module.supportDim R M ≤ d) {n : ℕ}
    (N : Fin (n + 1) → Submodule R M)
    (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) :
    I.hilbertSamuelMultiplicity M d =
      ∑ i : Fin n, I.hilbertSamuelMultiplicity
        (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) d := by
  have hstep : ∀ i : Fin n,
      I.hilbertSamuelMultiplicity (N i.succ) d =
        I.hilbertSamuelMultiplicity (N i.castSucc) d +
          I.hilbertSamuelMultiplicity
            (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) d := by
    intro i
    apply hilbertSamuelMultiplicity_additive_of_exact I hI d
      (Submodule.inclusion_injective (hle i))
      (by
        rw [LinearMap.exact_iff]
        ext x
        constructor
        · intro hx
          rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
          exact ⟨⟨x, hx⟩, by ext; rfl⟩
        · rintro ⟨y, rfl⟩
          rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact y.property)
      (Submodule.mkQ_surjective _)
    exact (supportDim_submodule_le _).trans hd
  have key := eq_add_sum_of_forall_succ_eq_add
    (fun j => I.hilbertSamuelMultiplicity (N j) d)
    (fun i => I.hilbertSamuelMultiplicity
      (↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) d) hstep
  rw [hbot, htop] at key
  simpa [hilbertSamuelMultiplicity_eq_zero_of_subsingleton (N := (⊥ : Submodule R M)) I hI d,
    multiplicity_congr I hI d (Submodule.topEquiv (R := R) (M := M)) hd] using key

/-- Alias of `Dualizing.coheight_le_supportDim_of_mem_support`. -/
private alias coheight_le_supportDim := Dualizing.coheight_le_supportDim_of_mem_support

/-- A prime `q` with `dim(R / q) = d` is minimal among the primes below it of coheight at
most `d`. -/
private lemma le_of_ringKrullDim_quotient_eq {R : Type*} [CommRing R] {d : ℕ}
    {q r : PrimeSpectrum R} (hqd : ringKrullDim (R ⧸ q.asIdeal) = d)
    (hrd : (Order.coheight r : WithBot ℕ∞) ≤ d) (hrq : r ≤ q) : q ≤ r := by
  have hq : (Order.coheight q : WithBot ℕ∞) = d := (coheight_eq_ringKrullDim_quotient q).trans hqd
  have hce : Order.coheight q = (d : ℕ∞) := WithBot.coe_injective hq
  by_contra hne
  have hc := Order.coheight_strictAnti (lt_of_le_of_ne hrq fun h => hne h.ge)
    (by rw [hce]; exact ENat.natCast_lt_top d)
  exact not_lt_of_ge (hrd.trans hq.ge) (WithBot.coe_lt_coe.mpr hc)

/-- The dimension of a prime quotient occurring as a subquotient of `M` is at most the
dimension of the support of `M`. -/
private lemma ringKrullDim_quotient_le_supportDim {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {N N' : Submodule R M} {q : PrimeSpectrum R}
    (e : (↥N' ⧸ N.submoduleOf N') ≃ₗ[R] R ⧸ q.asIdeal) :
    ringKrullDim (R ⧸ q.asIdeal) ≤ Module.supportDim R M :=
  calc
    ringKrullDim (R ⧸ q.asIdeal) = Module.supportDim R (R ⧸ q.asIdeal) :=
      (Module.supportDim_quotient_eq_ringKrullDim _).symm
    _ = Module.supportDim R (↥N' ⧸ N.submoduleOf N') := (Module.supportDim_eq_of_equiv e).symm
    _ ≤ Module.supportDim R N' :=
      Module.supportDim_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
    _ ≤ Module.supportDim R M := supportDim_submodule_le N'

/-- A prime of quotient dimension `d ≥ dim Supp(M)` at which `M` has nonzero length occurs
among the primes of a prime filtration of `M`. -/
private lemma mem_range_of_length_ne_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (d : ℕ) (hd : Module.supportDim R M ≤ d) {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (p : Fin n → PrimeSpectrum R)
    (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hquot : ∀ i : Fin n,
      Nonempty ((↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) {q : PrimeSpectrum R}
    (hqd : ringKrullDim (R ⧸ q.asIdeal) = d)
    (hl : Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ 0) :
    q ∈ Set.range p := by
  by_contra hn
  have hmem : q ∈ Module.support R M := by
    by_contra hnmem
    exact hl (Module.length_eq_zero_iff.mpr (Module.notMem_support_iff.mp hnmem))
  have hcq := (Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length
    N p hle hquot hbot htop).2 q ⟨hmem, fun r hr hrq =>
      le_of_ringKrullDim_quotient_eq hqd ((coheight_le_supportDim hr).trans hd) hrq⟩
  rw [show {i | p i = q} = ∅ from Set.eq_empty_of_forall_notMem fun i hi => hn ⟨i, hi⟩] at hcq
  exact hl (by simpa using hcq.symm)

/-- For a prime `q` of the filtration with `dim(R / q) = d`, the factors at `q` contribute
`length(M_q)` copies of the multiplicity of `R / q`. -/
private lemma sum_filter_eq_length_mul {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [DecidableEq (PrimeSpectrum R)]
    (I : Ideal R) (d : ℕ) {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (p : Fin n → PrimeSpectrum R)
    (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hquot : ∀ i : Fin n,
      Nonempty ((↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤)
    (hpdim : ∀ i, ringKrullDim (R ⧸ (p i).asIdeal) ≤ d) {q : PrimeSpectrum R}
    (hq : q ∈ Set.range p) (hqd : ringKrullDim (R ⧸ q.asIdeal) = d) :
    ∑ i with p i = q, I.hilbertSamuelMultiplicity (R ⧸ (p i).asIdeal) d =
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℚ) *
        I.hilbertSamuelMultiplicity (R ⧸ q.asIdeal) d := by
  have hX := Module.setOf_minimal_range_eq_setOf_minimal_support_and_ncard_eq_length
    N p hle hquot hbot htop
  have hqmin : Minimal (· ∈ Module.support R M) q := by
    refine (Set.ext_iff.mp hX.1 q).mp ⟨hq, fun r hr hrq => ?_⟩
    obtain ⟨i, rfl⟩ := hr
    exact le_of_ringKrullDim_quotient_eq hqd
      ((coheight_eq_ringKrullDim_quotient _).trans_le (hpdim i)) hrq
  have hl := congrArg ENat.toNat (hX.2 q hqmin)
  rw [ENat.toNat_natCast] at hl
  rw [← hl]
  calc
    _ = ∑ _i ∈ Finset.univ.filter (fun i => p i = q),
        I.hilbertSamuelMultiplicity (R ⧸ q.asIdeal) d :=
      Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by
      rw [Finset.sum_const]
      congr 1
      simp [Set.ncard_eq_toFinset_card']

/-- The multiplicity formula, for a given filtration of `M` with prime quotients. -/
private lemma multiplicity_eq_finsum_of_filtration
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ)
    (hd : Module.supportDim R M ≤ d) {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (p : Fin n → PrimeSpectrum R)
    (hle : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hquot : ∀ i : Fin n,
      Nonempty ((↥(N i.succ) ⧸ (N i.castSucc).submoduleOf (N i.succ)) ≃ₗ[R] R ⧸ (p i).asIdeal))
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) :
    I.hilbertSamuelMultiplicity M d =
      ∑ᶠ q : {q : PrimeSpectrum R // ringKrullDim (R ⧸ q.asIdeal) = d},
        ((Module.length (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl M)).toNat : ℚ) *
          I.hilbertSamuelMultiplicity (R ⧸ q.1.asIdeal) d := by
  classical
  have hpdim i : ringKrullDim (R ⧸ (p i).asIdeal) ≤ d :=
    (ringKrullDim_quotient_le_supportDim (hquot i).some).trans hd
  rw [multiplicity_eq_sum_filtration I hI d hd N hle hbot htop]
  conv_lhs =>
    enter [2, i]
    rw [multiplicity_congr I hI d (hquot i).some
      ((Module.supportDim_quotient_eq_ringKrullDim _).trans_le (hpdim i))]
  let S : Finset (PrimeSpectrum R) := Finset.univ.image p
  rw [finsum_eq_finsetSum_of_support_subset _
      (s := S.subtype fun q => ringKrullDim (R ⧸ q.asIdeal) = d) ?_,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S)
      fun i _ => Finset.mem_image_of_mem p (Finset.mem_univ i)]
  · calc
      _ = ∑ q ∈ S with ringKrullDim (R ⧸ q.asIdeal) = d,
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℚ) *
            I.hilbertSamuelMultiplicity (R ⧸ q.asIdeal) d := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun q hq => ?_
        by_cases hqd : ringKrullDim (R ⧸ q.asIdeal) = d
        · simp [hqd, sum_filter_eq_length_mul I d N p hle hquot hbot htop hpdim
            (by simpa [S] using hq) hqd]
        · simp only [hqd, ↓reduceIte]
          refine Finset.sum_eq_zero fun i hi =>
            hilbertSamuelMultiplicity_eq_zero_of_supportDim_lt I hI d ?_
          simpa [Module.supportDim_quotient_eq_ringKrullDim] using
            lt_of_le_of_ne (hpdim i) fun h => hqd ((Finset.mem_filter.mp hi).2 ▸ h)
      _ = _ := (Finset.sum_subtype_eq_sum_filter _).symm
  · intro q hq
    obtain ⟨i, hi⟩ := mem_range_of_length_ne_zero d hd N p hle hquot hbot htop q.2
      fun h => Function.mem_support.mp hq (by simp [h])
    exact Finset.mem_coe.mpr
      (Finset.mem_subtype.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))

/-- Let `I` be an ideal of definition in a Noetherian local ring `R`, and let `M` be a
finite `R`-module. In every degree at least the dimension of the support of `M`, its
Hilbert–Samuel multiplicity is the sum, over primes `p` with `dim(R / p)` equal to that
degree, of the multiplicity of `R / p` weighted by `length_{R_p}(M_p)`. -/
@[stacks 0AZX]
theorem hilbertSamuelMultiplicity_eq_finsum_localizedLength_mul
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : IsIdealOfDefinition I) (d : ℕ)
    (hd : Module.supportDim R M ≤ d) :
    I.hilbertSamuelMultiplicity M d =
      ∑ᶠ p : {p : PrimeSpectrum R // ringKrullDim (R ⧸ p.asIdeal) = d},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule p.1.asIdeal.primeCompl M)).toNat : ℚ) *
          I.hilbertSamuelMultiplicity (R ⧸ p.1.asIdeal) d := by
  obtain ⟨X, hbot, htop⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  exact multiplicity_eq_finsum_of_filtration I hI d hd X.toFun (fun i => (X.step i).2.choose)
    (fun i => (X.step i).1) (fun i => (X.step i).2.choose_spec) hbot htop

end Ideal
