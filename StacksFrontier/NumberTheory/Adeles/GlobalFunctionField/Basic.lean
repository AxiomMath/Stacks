module

public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.PlacesOver

/-!
# Places of a global function field

Let `k` be a finite field and `K` a function field over `k`, that is, a finite extension of the
rational function field `k(t)`. This covers the function field `K = k(X)` of a geometrically
irreducible smooth projective curve `X` over `k`, the setting of the Stacks project's section on
automorphic forms (Tag 03VR).

Every place of `K` contains `t` or `t⁻¹`, so it is discrete with finite residue field. We prove:
every nonzero element of `K` has finite support; there are finitely many places with residue
field of bounded cardinality; the places not containing `t` (the places at infinity) are finitely
many; a polynomial in `t` of degree `d` has order `d · ord_v(t)` at a place at infinity; and the
elements of `K` lying in every place are finitely many.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.gen` — the element `t ∈ K`, the image of `X ∈ k(X)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.isDiscrete` — every place is discrete.
* `Stacks.Adeles.GlobalFunctionField.finite_residueField` — every residue field is finite.
* `Stacks.Adeles.GlobalFunctionField.finite_setOf_ord_ne_zero` — finiteness of supports.
* `Stacks.Adeles.GlobalFunctionField.finite_setOf_resCard_le` — finitely many places of bounded
  residue cardinality.
* `Stacks.Adeles.GlobalFunctionField.finite_setOf_forall_mem` — the elements lying in every place
  are finitely many.
-/

@[expose] public noncomputable section

open Polynomial IsDedekindDomain IntermediateField IntermediateField.algebraAdjoinAdjoin WithZero

universe u

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] (K : Type u) [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The element `t ∈ K`, the image of the variable of `k(t)`. -/
public def gen : K := algebraMap (RatFunc k) K RatFunc.X

omit [Finite k] [FunctionField k K] in
/-- The element `t` is transcendental over `k`. -/
public theorem gen_transcendental : Transcendental k (gen k K) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc k) K).injective).2 RatFunc.transcendental_X

omit [Finite k] [FunctionField k K] in
/-- The element `t` is nonzero. -/
public theorem gen_ne_zero : gen k K ≠ 0 := (gen_transcendental k K).ne_zero

omit [Finite k] [FunctionField k K] in
/-- The element `t⁻¹` is transcendental over `k`. -/
public theorem gen_inv_transcendental : Transcendental k (gen k K)⁻¹ := fun h =>
  gen_transcendental k K (IsAlgebraic.inv_iff.1 h)

/-- `K` is a finite extension of `k(t)`. -/
public instance : FiniteDimensional k⟮gen k K⟯ K :=
  FunctionField.finiteDimensional_of_adjoin_transcendental (gen_transcendental k K)

/-- `K` is a finite extension of `k(t⁻¹)`. -/
public instance : FiniteDimensional k⟮(gen k K)⁻¹⟯ K :=
  FunctionField.finiteDimensional_of_adjoin_transcendental (gen_inv_transcendental k K)

omit [Finite k] [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
/-- `k(t⁻¹) = k(t)` as intermediate fields of `K / k`. -/
public theorem adjoin_gen_inv : k⟮(gen k K)⁻¹⟯ = k⟮gen k K⟯ :=
  le_antisymm (adjoin_simple_le_iff.2 (inv_mem (mem_adjoin_simple_self k _)))
    (adjoin_simple_le_iff.2 (by simpa using inv_mem (mem_adjoin_simple_self k (gen k K)⁻¹)))

/-- The degree `[K : k(t)]`. -/
public abbrev degree : ℕ := Module.finrank k⟮gen k K⟯ K

omit [Finite k] [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
/-- `[K : k(t⁻¹)] = [K : k(t)]`. -/
public theorem finrank_adjoin_gen_inv : Module.finrank k⟮(gen k K)⁻¹⟯ K = degree k K :=
  congrArg (fun F : IntermediateField k K => Module.finrank F K) (adjoin_gen_inv k K)

variable {K}

/-- `t ^ j - t ^ i` is nonzero for `i ≠ j` when `t` is transcendental. -/
private theorem pow_sub_pow_ne_zero {F E : Type*} [Field F] [Field E] [Algebra F E] {t : E}
    (ht : Transcendental F t) {i j : ℕ} (hij : i ≠ j) : t ^ j - t ^ i ≠ 0 := by
  intro h
  have : (X ^ j - X ^ i : F[X]) = 0 :=
    transcendental_iff_injective.1 ht (by simpa using h)
  rw [sub_eq_zero] at this
  exact hij (by simpa using (congrArg natDegree this).symm)

/-- The places of `K` at a height-one prime with a nontrivial valuation of `y` are finitely
many. -/
private theorem finite_of_dedekind {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra B K]
    [IsFractionRing B K] {y : K} (hy : y ≠ 0) :
    {v : Place K | ∃ P : HeightOneSpectrum B, v = Place.ofHeightOneSpectrum P ∧
      P.valuation K y ≠ 1}.Finite := by
  refine (((HeightOneSpectrum.Support.finite B y).union
    (HeightOneSpectrum.Support.finite B y⁻¹)).image
    (fun P => Place.ofHeightOneSpectrum (K := K) P)).subset ?_
  rintro v ⟨P, rfl, hP⟩
  refine ⟨P, ?_, rfl⟩
  rcases lt_or_gt_of_ne hP with h | h
  · right
    change 1 < P.valuation K y⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy), h⟩
  · exact Or.inl h

include k

/-- Every place of `K` is discrete. -/
public theorem isDiscrete (v : Place K) : v.IsDiscrete := by
  rcases v.1.mem_or_inv_mem (gen k K) with h | h
  · exact isDiscrete_of_mem k _ v h
  · exact isDiscrete_of_mem k _ v h

/-- Every residue field of `K` is finite. -/
public theorem finite_residueField (v : Place K) : Finite (IsLocalRing.ResidueField v.1) := by
  rcases v.1.mem_or_inv_mem (gen k K) with h | h
  · exact finite_residueField_of_mem k _ v h
  · exact finite_residueField_of_mem k _ v h

/-- The residue field of a place of `K` has positive cardinality. -/
public theorem resCard_pos (v : Place K) : 0 < v.resCard := by
  have := finite_residueField k v
  exact Nat.card_pos

/-- The residue field of a place of `K` has at least two elements. -/
public theorem one_lt_resCard (v : Place K) : 1 < v.resCard := by
  have := finite_residueField k v
  exact Finite.one_lt_card

/-- A place does not contain `t` exactly when `t⁻¹` has positive order. -/
public theorem gen_notMem_iff (v : Place K) :
    gen k K ∉ v.1 ↔ (gen k K)⁻¹ ∈ v.1 ∧ v.normVal (gen k K)⁻¹ < 1 := by
  have hd := isDiscrete k v
  have h0 := gen_ne_zero k K
  rw [← Place.normVal_le_one_iff hd, ← Place.normVal_le_one_iff hd, map_inv₀, not_le]
  constructor
  · intro h
    exact ⟨(inv_lt_one_of_one_lt₀ h).le, inv_lt_one_of_one_lt₀ h⟩
  · rintro ⟨-, h⟩
    have hpos : 0 < v.normVal (gen k K) := zero_lt_iff.2 ((_root_.map_ne_zero _).2 h0)
    exact (inv_lt_one₀ hpos).1 h

/-- The places of `K` not containing `t` are finitely many. -/
public theorem finite_setOf_gen_notMem : {v : Place K | gen k K ∉ v.1}.Finite := by
  refine (finite_of_dedekind (B := intClosure k (gen k K)⁻¹)
    (inv_ne_zero (gen_ne_zero k K))).subset ?_
  intro v hv
  obtain ⟨hmem, hlt⟩ := (gen_notMem_iff k v).1 hv
  obtain ⟨P, rfl, -⟩ := exists_eq_ofHeightOneSpectrum_intClosure k _ v hmem
  refine ⟨P, rfl, ?_⟩
  rw [Place.normVal_ofHeightOneSpectrum] at hlt
  exact hlt.ne

/-- A nonzero element of `K` has nonzero order at only finitely many places. -/
public theorem finite_setOf_ord_ne_zero {y : K} (hy : y ≠ 0) :
    {v : Place K | v.ord y ≠ 0}.Finite := by
  refine ((finite_of_dedekind (B := intClosure k (gen k K)) hy).union
    (finite_setOf_gen_notMem k)).subset ?_
  intro v hv
  by_cases ht : gen k K ∈ v.1
  · left
    obtain ⟨P, rfl, -⟩ := exists_eq_ofHeightOneSpectrum_intClosure k _ v ht
    refine ⟨P, rfl, fun h => hv ?_⟩
    simp [Place.ord, Place.normVal_ofHeightOneSpectrum, h]
  · exact Or.inr ht

/-- At a place not containing `t`, a nonzero polynomial `f` in `t` has order `deg f · ord_v t`. -/
public theorem ord_aeval_gen_of_notMem {v : Place K} (hv : gen k K ∉ v.1) {f : k[X]} (hf : f ≠ 0) :
    v.ord (aeval (gen k K) f) = f.natDegree * v.ord (gen k K) := by
  have hd := isDiscrete k v
  set t := gen k K
  have ht1 : 1 < v.normVal t := by
    rw [← not_le, Place.normVal_le_one_iff hd]; exact hv
  have hc : ∀ c : k, c ≠ 0 → v.normVal (algebraMap k K c) = 1 := by
    intro c hc
    have h1 := (Place.normVal_le_one_iff hd).2 (algebraMap_mem_place v c)
    have h2 := (Place.normVal_le_one_iff hd).2 (algebraMap_mem_place v c⁻¹)
    rw [map_inv₀, map_inv₀] at h2
    have hpos : 0 < v.normVal (algebraMap k K c) :=
      zero_lt_iff.2 ((_root_.map_ne_zero _).2 (by simpa using hc))
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  have hle : ∀ i, v.normVal (algebraMap k K (f.coeff i) * t ^ i) ≤ v.normVal t ^ i := by
    intro i
    rw [map_mul, map_pow]
    by_cases hci : f.coeff i = 0
    · simp [hci]
    · rw [hc _ hci, one_mul]
  have hval : v.normVal (aeval t f) = v.normVal t ^ f.natDegree := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ]
    have hlead : v.normVal (f.coeff f.natDegree • t ^ f.natDegree) = v.normVal t ^ f.natDegree := by
      rw [Algebra.smul_def, map_mul, map_pow, hc (f.coeff f.natDegree) (leadingCoeff_ne_zero.2 hf),
        one_mul]
    rw [add_comm, Valuation.map_add_eq_of_lt_left _ ?_, hlead]
    rw [hlead]
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
    · simp [h0]
    · refine Valuation.map_sum_lt _ (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans ht1))) ?_
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Algebra.smul_def]
      exact (hle i).trans_lt (pow_lt_pow_right₀ ht1 hi)
  rw [Place.ord, hval, Place.ord, log_pow, nsmul_eq_mul, mul_neg]

/-- A nonzero constant has order `0` at every place. -/
public theorem ord_algebraMap (v : Place K) {c : k} (hc : c ≠ 0) :
    v.ord (algebraMap k K c) = 0 := by
  have hd := isDiscrete k v
  have hc0 : algebraMap k K c ≠ 0 := by simpa using hc
  have h1 := (Place.ord_nonneg_iff hd hc0).2 (algebraMap_mem_place v c)
  have h2 := (Place.ord_nonneg_iff hd (inv_ne_zero hc0)).2
    (by simpa using algebraMap_mem_place v c⁻¹)
  have h3 := Place.ord_mul v hc0 (inv_ne_zero hc0)
  rw [mul_inv_cancel₀ hc0, Place.ord, map_one, log_one, neg_zero] at h3
  omega

/-- At a place containing `t` with residue field of size at most `N`, some `t ^ j - t ^ i` with
`i ≠ j` in `Fin (N + 1)` has positive order. -/
private theorem exists_ord_pos_gen_pow_sub_gen_pow {v : Place K} (ht : gen k K ∈ v.1) (N : ℕ)
    (hv : v.resCard ≤ N) :
    ∃ i j : Fin (N + 1), i ≠ j ∧ 1 ≤ v.ord (gen k K ^ (j : ℕ) - gen k K ^ (i : ℕ)) := by
  set t := gen k K
  have hd := isDiscrete k v
  have := finite_residueField k v
  let := Fintype.ofFinite (IsLocalRing.ResidueField v.1)
  let r : Fin (N + 1) → IsLocalRing.ResidueField v.1 := fun i =>
    IsLocalRing.residue v.1 ⟨t, ht⟩ ^ (i : ℕ)
  obtain ⟨i, j, hij, hr⟩ := Fintype.exists_ne_map_eq_of_card_lt r (by
    simpa [Place.resCard, Nat.card_eq_fintype_card] using Nat.lt_succ_of_le hv)
  refine ⟨i, j, hij, ?_⟩
  have hmem : (⟨t, ht⟩ : v.1) ^ (j : ℕ) - (⟨t, ht⟩ : v.1) ^ (i : ℕ) ∈
      IsLocalRing.maximalIdeal v.1 := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow]
    exact sub_eq_zero.2 hr.symm
  rw [ValuationSubring.valuation_lt_one_iff] at hmem
  have he : v.normVal.IsEquiv v.1.valuation :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2
      ((Place.normVal_spec hd).1.trans v.1.valuationSubring_valuation.symm)
  have hlt : v.normVal (t ^ (j : ℕ) - t ^ (i : ℕ)) < 1 :=
    he.lt_one_iff_lt_one.2 (by simpa using hmem)
  have hne : v.normVal (t ^ (j : ℕ) - t ^ (i : ℕ)) ≠ 0 :=
    (_root_.map_ne_zero _).2 (pow_sub_pow_ne_zero (gen_transcendental k K) fun h => hij (Fin.ext h))
  rw [← exp_log hne, ← exp_zero, exp_lt_exp] at hlt
  simp only [Place.ord]
  omega

/-- At a place containing `t` some nonzero polynomial in `t` has positive order. -/
public theorem exists_poly_ord_pos {v : Place K} (ht : gen k K ∈ v.1) :
    ∃ P : k[X], P ≠ 0 ∧ 1 ≤ v.ord (aeval (gen k K) P) := by
  obtain ⟨i, j, hij, h⟩ := exists_ord_pos_gen_pow_sub_gen_pow k ht v.resCard le_rfl
  have h' : 1 ≤ v.ord (aeval (gen k K) (X ^ (j : ℕ) - X ^ (i : ℕ) : k[X])) := by simpa using h
  exact ⟨_, fun h0 => by simp [h0, Place.ord] at h', h'⟩

/-- There are only finitely many places whose residue field has at most `N` elements. -/
public theorem finite_setOf_resCard_le (N : ℕ) : {v : Place K | v.resCard ≤ N}.Finite := by
  classical
  refine ((Set.finite_iUnion fun i : Fin (N + 1) => Set.finite_iUnion fun j : Fin (N + 1) =>
    Set.finite_iUnion fun h : i ≠ j => finite_setOf_ord_ne_zero k
      (pow_sub_pow_ne_zero (gen_transcendental k K) fun h' => h (Fin.ext h'))).union
    (finite_setOf_gen_notMem k)).subset ?_
  intro v hv
  by_cases ht : gen k K ∈ v.1
  · left
    obtain ⟨i, j, hij, h⟩ := exists_ord_pos_gen_pow_sub_gen_pow k ht N hv
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨i, j, hij, by omega⟩
  · exact Or.inr ht

omit [Finite k] in
/-- A global function field has a place. -/
public theorem nonempty_place : Nonempty (Place K) := by
  set t := gen k K
  have hx := gen_transcendental k K
  set a : polySubalg k t := polySubalgMap (k := k) t X
  have haprime : Prime a := by
    simpa [a] using (MulEquiv.prime_iff (polySubalgEquiv hx).toMulEquiv).2 prime_X
  have hmax : (Ideal.span {a}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible haprime.irreducible
  have hinj : Function.Injective (algebraMap (polySubalg k t) (intClosure k t)) := fun c d h =>
    Subtype.ext (congrArg (algebraMap (intClosure k t) K) h)
  have hker : RingHom.ker (algebraMap (polySubalg k t) (intClosure k t)) ≤ Ideal.span {a} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := intClosure k t) _ hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have h0 : Ideal.span {a} = ⊥ := by
      rw [← hQ]
      exact Ideal.comap_bot_of_injective _ hinj
    rw [Ideal.span_singleton_eq_bot] at h0
    exact haprime.ne_zero h0
  exact ⟨Place.ofHeightOneSpectrum (K := K) ⟨Q, hQmax.isPrime, hQ0⟩⟩

omit [Finite k] [FunctionField k K] in
/-- `k[t] ∩ k[t⁻¹] = k`. -/
public theorem mem_polySubalg_gen_inter {z : K} (h₁ : z ∈ polySubalg k (gen k K))
    (h₂ : z ∈ polySubalg k (gen k K)⁻¹) : ∃ c : k, algebraMap k K c = z := by
  set t := gen k K
  have ht0 : t ≠ 0 := gen_ne_zero k K
  rw [polySubalg, Algebra.adjoin_singleton_eq_range_aeval] at h₁ h₂
  obtain ⟨f, rfl⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  let : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
  have hrefl := eval₂_reflect_mul_pow (algebraMap k K) t⁻¹ g.natDegree g le_rfl
  rw [invOf_eq_inv, inv_inv] at hrefl
  have hfX : aeval t (reflect g.natDegree g) = aeval t (f * X ^ g.natDegree) := by
    have hpow : t⁻¹ ^ g.natDegree * t ^ g.natDegree = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ ht0, one_pow]
    have := congrArg (· * t ^ g.natDegree) hrefl
    simp only [mul_assoc, hpow, mul_one] at this
    rw [map_mul, map_pow, aeval_X, aeval_def, this, ← aeval_def]
    exact congrArg (· * t ^ g.natDegree) hg
  have heq := transcendental_iff_injective.1 (gen_transcendental k K) hfX
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf]⟩
  have hdeg : f.natDegree + g.natDegree ≤ g.natDegree := by
    have h1 := natDegree_reflect_le (N := g.natDegree) (p := g)
    rw [heq, natDegree_mul hf (pow_ne_zero _ X_ne_zero), natDegree_X_pow, max_self] at h1
    exact h1
  have hf0 : f.natDegree = 0 := by omega
  refine ⟨f.coeff 0, ?_⟩
  change _ = aeval t f
  conv_rhs => rw [eq_C_of_natDegree_eq_zero hf0]
  rw [aeval_C]

/-- The elements of `K` lying in every place are finitely many: they are the roots of nonzero
polynomials over `k` of degree at most `[K : k(t)]`. -/
public theorem finite_setOf_forall_mem : {y : K | ∀ v : Place K, y ∈ v.1}.Finite := by
  classical
  set t := gen k K
  set n := degree k K
  -- the nonzero polynomials over `k` of degree at most `n`
  have hG : {g : k[X] | g.natDegree ≤ n}.Finite := by
    refine (Set.finite_range fun c : Fin (n + 1) → k => ∑ i, C (c i) * X ^ (i : ℕ)).subset ?_
    intro g hg
    refine ⟨fun i => g.coeff i, ?_⟩
    simp only
    rw [Fin.sum_univ_eq_sum_range (fun i => C (g.coeff i) * X ^ i) (n + 1)]
    simp_rw [C_mul_X_pow_eq_monomial]
    exact (as_sum_range' g (n + 1) (Nat.lt_succ_of_le hg)).symm
  refine (hG.biUnion fun g _ => rootSet_finite g K).subset ?_
  intro y hy
  -- `y` is integral over `k[t]` and over `k[t⁻¹]`
  have hint : ∀ (s : K) [FiniteDimensional k⟮s⟯ K], IsIntegral (polySubalg k s) y := by
    intro s _
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := intClosure k s) K y
      fun P => by
        have := hy (Place.ofHeightOneSpectrum P)
        rwa [Place.ofHeightOneSpectrum_val, Valuation.mem_valuationSubring_iff] at this
    rw [← hb]
    exact b.2
  have hcoeff : ∀ (s : K) [FiniteDimensional k⟮s⟯ K] (i : ℕ),
      (((minpoly k⟮s⟯ y).coeff i : k⟮s⟯) : K) ∈ polySubalg k s := by
    intro s _ i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' k⟮s⟯ (hint s), coeff_map]
    exact ((minpoly (polySubalg k s) y).coeff i).2
  have hsame : ∀ i, (((minpoly k⟮t⁻¹⟯ y).coeff i : k⟮t⁻¹⟯) : K) =
      (((minpoly k⟮t⟯ y).coeff i : k⟮t⟯) : K) := fun i =>
    congrArg (fun F : IntermediateField k K => (((minpoly F y).coeff i : F) : K))
      (adjoin_gen_inv k K)
  have hk : ∀ i, ∃ c : k, algebraMap k K c = (((minpoly k⟮t⟯ y).coeff i : k⟮t⟯) : K) :=
    fun i => mem_polySubalg_gen_inter k (hcoeff t i) (hsame i ▸ hcoeff t⁻¹ i)
  choose d hd using hk
  set m := (minpoly k⟮t⟯ y).natDegree
  have hm : m ≤ n := minpoly.natDegree_le y
  set g : k[X] := ∑ i ∈ Finset.range (m + 1), C (d i) * X ^ i
  have hgmap : g.map (algebraMap k K) = (minpoly k⟮t⟯ y).map (algebraMap k⟮t⟯ K) := by
    ext i
    rw [coeff_map, coeff_map]
    simp only [g, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hi
    · exact hd i
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]
  have hgdeg : g.natDegree ≤ m := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hint_t := hint t
  have hmonic : (minpoly k⟮t⟯ y).Monic :=
    minpoly.monic (isIntegral_trans (R := polySubalg k t) _ hint_t |>.tower_top)
  have hg0 : g.map (algebraMap k K) ≠ 0 := by
    rw [hgmap]
    exact (hmonic.map _).ne_zero
  refine Set.mem_biUnion (x := g) (hgdeg.trans hm) ?_
  rw [mem_rootSet']
  refine ⟨hg0, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, hgmap, ← eval₂_eq_eval_map, ← aeval_def, minpoly.aeval]

end Stacks.Adeles.GlobalFunctionField

end
