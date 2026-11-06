module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Trace.Basic
import StacksCore.Algebra.CharP.LinearMaps
public import StacksCore.Algebra.Polynomial.Roots
public import StacksCore.FieldTheory.Galois.Basic
public import StacksCore.RingTheory.AdjoinRoot
import StacksCore.RingTheory.Trace.Basic

/-! # Artin-Schreier Extensions

## Main Results

-/

@[expose] public section

open Polynomial IntermediateField Finset

namespace Polynomial

/-- For a prime `p`, the Artin–Schreier polynomial `X^p - X - C r` is monic. -/
@[simp]
theorem monic_X_pow_sub_X_sub_C {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {r : R} :
    (X ^ p - X - C r).Monic := by
  nontriviality R
  rw [← sub_add_eq_sub_sub]
  refine monic_X_pow_sub ?_
  compute_degree
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- For a prime `p`, the degree of `X^p - X` is `p`. -/
@[simp]
theorem degree_X_pow_sub_X {R : Type*} [Nontrivial R] [Ring R] {p : ℕ} [Fact p.Prime] :
    (X ^ p - X : R[X]).degree = p := by
  have hp : p.Prime := Fact.out
  rw [degree_sub_eq_left_of_degree_lt (by simpa using hp.one_lt), degree_X_pow]

/-- For a prime `p`, the `natDegree` of `X^p - X` is `p`. -/
@[simp]
theorem natDegree_X_pow_sub_X {R : Type*} [Nontrivial R] [Ring R] {p : ℕ} [Fact p.Prime] :
    (X ^ p - X : R[X]).natDegree = p := by
  simp [natDegree_eq_of_degree_eq_some]

/-- For a prime `p`, the degree of the Artin–Schreier polynomial `X^p - X - C r` is `p`. -/
@[simp]
theorem degree_X_pow_sub_X_sub_C {R : Type*} [Nontrivial R] [Ring R] {p : ℕ} [Fact p.Prime]
    {r : R} : (X ^ p - X - C r).degree = ↑p := by
  have hp : p.Prime := Fact.out
  rw [degree_sub_C (by simp [hp.pos]), degree_X_pow_sub_X]

/-- For a prime `p`, the `natDegree` of the Artin–Schreier polynomial `X^p - X - C r` is `p`. -/
theorem natDegree_X_pow_sub_X_sub_C {R : Type*} [Nontrivial R] [Ring R] {p : ℕ} [Fact p.Prime]
    {r : R} : (X ^ p - X - C r).natDegree = p := by simp

/-- Over `(ZMod p)[X]`, the polynomial `Y^p - Y - C (X^p - X)` in the variable `Y` factors as
`∏ i ∈ range p, (Y - C (X + i))`. This is the universal form of the Artin–Schreier factorisation
from which the version over an arbitrary characteristic-`p` ring is obtained by base change. -/
theorem X_pow_sub_X_sub_C_polynomial_eq_prod (p : ℕ) [Fact p.Prime] :
    (X ^ p - X - C (X ^ p - X) : (ZMod p)[X][X]) = ∏ i ∈ range p, (X - C (X + i)) := by
  refine monic_X_pow_sub_X_sub_C.eq_prod_X_sub_C_of_card' ?_ (by simp [- map_sub]) ?_
  · refine (add_right_injective _).comp_injOn ?_
    simpa using CharP.natCast_injOn_Iio (ZMod p)[X] p
  · simp only [mem_range, map_sub, map_pow, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C]
    rintro i hi
    rw [sub_sub_sub_comm, ← sub_pow_char, add_sub_cancel_left, sub_eq_zero, ← C_eq_natCast,
      ← map_pow, ZMod.pow_card]

/-- In a commutative ring `R` of characteristic `p`, for every `a : R` the polynomial
`X^p - X - C (a^p - a)` factors as `∏ i ∈ range p, (X - C (a + i))`. -/
theorem X_pow_sub_X_sub_C_eq_prod {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a : R) : X ^ p - X - C (a ^ p - a) = ∏ i ∈ range p, (X - C (a + i)) := by
  let := ZMod.algebra R p
  simpa [Polynomial.map_prod]
    using congr($(X_pow_sub_X_sub_C_polynomial_eq_prod p).map (aeval a).toRingHom)

/-- If `f * g` is associated to a finite product of primes `∏ i ∈ s, r i`, then `s` splits into a
subset `t ⊆ s` such that `f` is associated to `∏ i ∈ t, r i` and `g` is associated to
`∏ i ∈ s \ t, r i`. -/
theorem _root_.Associated.of_mul_prod
    {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {r : ι → M} (hp : ∀ i ∈ s, Prime (r i))
    {f g : M} (hfg : Associated (f * g) (∏ i ∈ s, r i)) :
    ∃ t ⊆ s, Associated f (∏ i ∈ t, r i) ∧ Associated g (∏ i ∈ s \ t, r i) := by
  induction s using Finset.induction generalizing f g with
  | empty => simpa using hfg
  | insert i s his ih =>
    rw [forall_mem_insert] at hp
    have hifg : r i ∣ f * g := .trans (dvd_prod_of_mem _ <| by simp) hfg.dvd'
    replace hifg := hp.1.dvd_mul.mp hifg
    wlog hrif : r i ∣ f
    · obtain ⟨t, hts, hft, hgt⟩ := this i s his ih hp (by rwa [mul_comm]) hifg.symm
        (hifg.resolve_left hrif)
      exact ⟨insert i s \ t, by simp, hgt, by simpa [hts]⟩
    · obtain ⟨f, rfl⟩ := hrif
      nth_rw 1 [prod_insert his, mul_assoc] at hfg
      replace hfg := hfg.of_mul_left (.refl _) hp.1.ne_zero
      obtain ⟨t, hts, hft, hgt⟩ := ih hp.2 hfg
      refine ⟨insert i t, by simp [insert_subset_iff, hts.trans], ?_, ?_⟩
      · rw [prod_insert (by grind)]
        exact .mul_left _ hft
      · rwa [insert_sdiff_insert, sdiff_insert_of_notMem his]

/-- In a commutative ring of characteristic `p`, the Artin–Schreier polynomial
`X^p - X - C (a^p - a)` splits, since it factors as a product of linear factors `X - C (a + i)`. -/
theorem splits_X_pow_sub_X_sub_C {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {a : R} : Splits (X ^ p - X - C (a ^ p - a)) := by
  rw [X_pow_sub_X_sub_C_eq_prod]
  exact .prod fun _ _ ↦ .X_sub_C _

/-- Over a field `F` of characteristic `p`, the Artin–Schreier polynomial `X^p - X - C a` is
irreducible whenever `a` is not of the form `x^p - x` for any `x : F`. -/
theorem irreducible_X_pow_sub_X_sub_C {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {a : F} (ha : ∀ x, x ^ p ≠ x + a) : Irreducible (X ^ p - X - C a) := by
  have hp : p.Prime := Fact.out
  refine (monic_X_pow_sub_X_sub_C.irreducible_iff_lt_natDegree_lt ?_).mpr ?_
  · exact ne_of_apply_ne natDegree (by simp [hp.ne_zero])
  rintro f hfm hfd ⟨g, hfg⟩
  let K := (X ^ p - X - C a).SplittingField
  have hs : ((X ^ p - X - C a).map (algebraMap F K)).Splits := IsSplittingField.splits _ _
  let b : K := rootOfSplits hs (by simp [hp.ne_zero])
  have hab : algebraMap F K a = b ^ p - b := by
    have : (X ^ p - X - C (algebraMap F K a)).eval b = 0 := by
      convert eval_rootOfSplits _ _
      simp
    simpa [sub_eq_zero, eq_comm (a := algebraMap F K a)]
  replace hfg := congr(($hfg).map (algebraMap F K))
  simp_rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, hab,
    X_pow_sub_X_sub_C_eq_prod] at hfg
  obtain ⟨t, hts, hft, hgt⟩ := (Associated.of_eq hfg).symm.of_mul_prod fun _ _ ↦ prime_X_sub_C _
  replace hft := eq_of_monic_of_associated (hfm.map _) (monic_prod_X_sub_C _ _) hft
  have hpt : ¬p ∣ #t := by
    have hfdt := congr(($hft).natDegree)
    rw [natDegree_map, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _] at hfdt
    simp_rw [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one] at hfdt
    rw [← hfdt]
    rw [mem_Ioc, natDegree_X_pow_sub_X_sub_C] at hfd
    exact Nat.not_dvd_of_pos_of_lt hfd.1 (by omega)
  have htk : (#t : K) ≠ 0 := (CharP.cast_eq_zero_iff K p _).not.mpr hpt
  obtain ⟨b, hba⟩ : b ∈ Set.range (algebraMap F K) := by
    have hfnt := congr(($hft.symm).nextCoeff)
    rw [prod_X_sub_C_nextCoeff, nextCoeff_map_eq, sum_add_distrib, sum_const, ← Nat.cast_sum,
      neg_eq_iff_eq_neg, ← eq_sub_iff_add_eq, nsmul_eq_mul, ← eq_inv_mul_iff_mul_eq₀ htk] at hfnt
    exact ⟨(#t : F)⁻¹ * (-f.nextCoeff - (∑ x ∈ t, x)), by simp [hfnt]⟩
  exact ha b <| (algebraMap F K).injective <| by simp [hba, hab]

/-- Registers irreducibility of the Artin–Schreier polynomial as a `Fact`, drawing the
non-surjectivity hypothesis `∀ x, x^p ≠ x + a` from the ambient `Fact` instance. -/
instance (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (a : F)
    [Fact (∀ x, x ^ p ≠ x + a)] : Fact (Irreducible (X ^ p - X - C a)) where
  out := irreducible_X_pow_sub_X_sub_C Fact.out

/-- In a commutative ring of characteristic `p`, the Artin–Schreier polynomial `X^p - X - C a`
is separable: its derivative is `-1`, which is coprime to every polynomial. -/
theorem separable_X_pow_sub_X_sub_C {R : Type*} [CommRing R] {p : ℕ} [CharP R p]
    {a : R} : Separable (X ^ p - X - C a) := by
  simpa [Separable, derivative_X_pow] using isCoprime_one_right.neg_right

end Polynomial

/-- The element-level Artin–Schreier factorisation in characteristic `p`:
`a^p - a - (b^p - b) = ∏ i ∈ range p, (a - (b + i))`. -/
theorem pow_sub_sub_pow_sub_eq_prod {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a b : R) : a ^ p - a - (b ^ p - b) = ∏ i ∈ range p, (a - (b + i)) := by
  let := ZMod.algebra R p
  simpa using congr($(X_pow_sub_X_sub_C_eq_prod p b).aeval a)

/-- In a characteristic-`p` integral domain, if `a^p - a = b^p - b` then `a = b + i` for some
natural number `i < p`. -/
theorem exists_eq_add_of_pow_sub_eq_pow_sub {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} [Fact p.Prime] [CharP R p] {a b : R} (hab : a ^ p - a = b ^ p - b) :
    ∃ i < p, a = b + i := by
  rw [← sub_eq_zero, pow_sub_sub_pow_sub_eq_prod, prod_eq_zero_iff] at hab
  simpa [sub_eq_zero] using hab

/-- In `AdjoinRoot (X^p - X - C a)` over a characteristic-`p` ring, the image of `a` under the
canonical map equals `root^p - root`, where `root` is the formal adjoined root. -/
theorem AdjoinRoot.of_eq_root_pow_sub_root {F : Type*} [CommRing F] {p : ℕ}
    {a : F} : of (X ^ p - X - C a) a = .root _ ^ p - .root _ := .symm <| by
  have := isRoot_root (X ^ p - X - C a)
  simpa [sub_eq_zero]

/-- Over a field `F` of characteristic `p`, if `X^p - X - C a` has no root in `F`, then the
quotient `AdjoinRoot (X^p - X - C a)` is its splitting field. -/
instance (F : Type*) [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] (a : F)
    [Fact (∀ x, x ^ p ≠ x + a)] :
    IsSplittingField F (AdjoinRoot (X ^ p - X - C a)) (X ^ p - X - C a) where
  splits' := by
    have := charP_of_injective_algebraMap' (A := AdjoinRoot (X ^ p - X - C a)) F p
    simpa [AdjoinRoot.of_eq_root_pow_sub_root, -map_sub] using splits_X_pow_sub_X_sub_C
  adjoin_rootSet' := by
    rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    refine Algebra.subset_adjoin <| mem_rootSet.mpr ⟨monic_X_pow_sub_X_sub_C.ne_zero, ?_⟩
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

/-- The Artin–Schreier extension `AdjoinRoot (X^p - X - C a)` of a characteristic-`p` field `F`
is Galois, since `X^p - X - C a` is separable. -/
instance (F : Type*) [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] (a : F)
    [Fact (∀ x, x ^ p ≠ x + a)] : IsGalois F (AdjoinRoot (X ^ p - X - C a)) :=
  .of_separable_splitting_field (p := X ^ p - X - C a) separable_X_pow_sub_X_sub_C

/-- `AdjoinRoot (X^p - X - C a)` is a finite module over `R`, since `X^p - X - C a` is monic. -/
instance (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] (a : R) :
    let := (AdjoinRoot.instAlgebra (X ^ p - X - C a) (S := R)).toModule -- temp
    Module.Finite R (AdjoinRoot (X ^ p - X - C a)) :=
  monic_X_pow_sub_X_sub_C.finite_adjoinRoot

/-- The Galois group of the Artin–Schreier extension `AdjoinRoot (X^p - X - C a)/F` is cyclic:
it has prime order `p` since `[AdjoinRoot (X^p - X - C a) : F] = p`. -/
instance (F : Type*) [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] (a : F)
    [Fact (∀ x, x ^ p ≠ x + a)] : IsCyclic Gal(AdjoinRoot (X ^ p - X - C a)/F) :=
  isCyclic_of_prime_card (p := p) <| by
    rw [IsGalois.card_aut_eq_finrank, monic_X_pow_sub_X_sub_C.finrank_adjoinRoot,
      natDegree_X_pow_sub_X_sub_C]

/-- If `b` is an Artin–Schreier root of `a`, i.e. `b^p = b + a`, and the polynomial
`X^p - X - C a` has no root in `F`, then the minimal polynomial of `b` over `F` is
`X^p - X - C a`. -/
theorem minpoly_eq_X_pow_sub_X_sub_C {F K : Type*} [Field F] [Field K] [Algebra F K]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {a : F} {b : K} (hab : b ^ p = b + algebraMap F K a) (ha : ∀ x, x ^ p ≠ x + a) :
    minpoly F b = X ^ p - X - C a := .symm <|
  minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_X_sub_C ha) (by simp [hab])
    monic_X_pow_sub_X_sub_C

/-- Variant of `minpoly_eq_X_pow_sub_X_sub_C` where the hypothesis is replaced by the equivalent
condition that `b` is not in the image of `algebraMap F K`. -/
theorem minpoly_eq_X_pow_sub_X_sub_C' {F K : Type*} [Field F] [Field K] [Algebra F K]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {a : F} {b : K} (hab : b ^ p = b + algebraMap F K a) (hb : b ∉ Set.range (algebraMap F K)) :
    minpoly F b = X ^ p - X - C a :=
  have := charP_of_injective_algebraMap' (A := K) F p
  minpoly_eq_X_pow_sub_X_sub_C hab fun c hc ↦
    have h : b ^ p - b = algebraMap F K c ^ p - algebraMap F K c := by
      simp [← map_pow, hc, hab]
    let ⟨i, _, hi⟩ := exists_eq_add_of_pow_sub_eq_pow_sub h
    hb ⟨c + i, by simp [hi]⟩

/-- If `σ : Gal(K/F)` shifts `b ∈ K` by one (`σ b = b + 1`) and the fixed field of the cyclic
subgroup generated by `σ` is `F`, then the minimal polynomial of `b` over `F` is an
Artin–Schreier polynomial `X^p - X - C a` for some `a : F`. -/
theorem exists_minpoly_eq_X_pow_sub_X_sub_C_of_apply_eq_add_one
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {p : ℕ} [Fact p.Prime] [CharP F p] {σ : Gal(K/F)} {b : K} (hσb : σ b = b + 1)
    (hσ : fixedField (.zpowers σ) = ⊥) :
    ∃ a, minpoly F b = X ^ p - X - C a :=
  have := charP_of_injective_algebraMap' (A := K) F p
  have hp : p.Prime := Fact.out
  have hσbp : σ (b ^ p - b) = b ^ p - b := by
    rw [map_sub, map_pow, hσb, ← sub_eq_zero, pow_sub_sub_pow_sub_eq_prod]
    exact prod_eq_zero (i := 1) (by simp [hp.one_lt]) (by simp)
  let ⟨a, ha⟩ : b ^ p - b ∈ (⊥ : IntermediateField F K) := by
    rw [← hσ, mem_fixedField_zpowers_iff, hσbp]
  have hb : b ∉ (⊥ : IntermediateField F K) := fun ⟨a, ha⟩ ↦ by simp [← ha] at hσb
  ⟨a, minpoly_eq_X_pow_sub_X_sub_C' (by simp [← sub_eq_iff_eq_add', ← ha]) hb⟩

/-- In a ring of characteristic `p`, the identity `(a - 1)^(p - 1) = ∑ i ∈ range p, a^i` holds.
This is obtained from the geometric series factorisation `aᵖ - 1 = (a - 1) · ∑ aⁱ` together with
`aᵖ - 1 = (a - 1)ᵖ` in characteristic `p`. -/
theorem sub_one_pow_char_sub_one {R : Type*} [Ring R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (a : R) : (a - 1) ^ (p - 1) = ∑ i ∈ range p, a ^ i := by
  let := ZMod.algebra R p
  suffices (X - 1 : (ZMod p)[X]) ^ (p - 1) = ∑ i ∈ range p, X ^ i by
    have := congr(($this).aeval a)
    simpa [eval₂_pow, eval₂_finsetSum]
  refine mul_right_cancel₀ (monic_X_sub_C 1).ne_zero ?_
  have hp : p.Prime := Fact.out
  simp_rw [map_one, ← pow_succ, geom_sum_mul, Nat.sub_add_cancel hp.one_le, sub_pow_char, one_pow]

/-- **Stacks 09DY**.
Let `F` be a field of characteristic `p > 0` and let `K/F` be a Galois extension of degree `p`.
Then `K = F(b)` for some `b ∈ K` whose Artin–Schreier expression `b^p - b` lies in `F`. -/
@[stacks 09DY]
theorem IsGalois.exists_artinSchreier_of_finrank_eq_char
    {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp : Module.finrank F K = p) :
    ∃ b : K, F⟮b⟯ = ⊤ ∧ b ^ p - b ∈ Set.range (algebraMap F K) := by
  obtain ⟨w, hw⟩ := Algebra.trace_surjective F K 1
  have hwk := congr(algebraMap F K $hw)
  have : IsCyclic Gal(K/F) := isCyclic_of_prime_card (p := p) <| by
    rw [IsGalois.card_aut_eq_finrank, hp]
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(K/F))
  rw [map_one, IsGalois.trace_eq_of_zpowers_eq_top hσ, IsGalois.card_aut_eq_finrank, hp] at hwk
  replace hwk : (∑ i ∈ range p, σ.toLinearMap ^ i) w = 1 := by simpa [Module.End.coe_pow] using hwk
  have hp' : p.Prime := Fact.out
  have h2p := hp'.two_le
  rw [← sub_one_pow_char_sub_one, show p - 1 = p - 2 + 1 by omega, pow_succ',
    Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add'] at hwk
  obtain ⟨a, ha⟩ := exists_minpoly_eq_X_pow_sub_X_sub_C_of_apply_eq_add_one hwk <| by
    convert IsGalois.fixedField_top (F := F) (E := K)
    rwa [Subgroup.eq_top_iff']
  refine ⟨((σ.toLinearMap - 1) ^ (p - 2)) w, ?_, a, .symm ?_⟩
  · rw [Field.primitive_element_iff_minpoly_natDegree_eq, ha, natDegree_X_pow_sub_X_sub_C, hp]
  · have := minpoly.aeval F (((σ.toLinearMap - 1) ^ (p - 2)) w)
    simpa [-minpoly.aeval, ha, sub_eq_zero]
