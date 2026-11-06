module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer.Ramification
public import Mathlib.RingTheory.Norm.Basic

@[expose] public section

/-!
# Kummer extensions: roots of unity and intermediate fields

Roots of unity in `K₁`, and, when `n` is prime to the residue characteristic of `A`, every
intermediate field of `K₁/K` is `K[(π')^{n/d}]` for a positive divisor `d` of `n`
(Stacks Tag 09EV (6)).
-/

open Polynomial

namespace Stacks.KummerExtension

section Statements

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (π : A) (n : ℕ)

/-- If one summand `f j` of a finite sum has strictly smaller valuation than every other summand,
then the valuation of the sum is `v (f j)`. -/
theorem val_sum_eq_of_lt {R Γ ι : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) {s : Finset ι} {f : ι → R} {j : ι} (hj : j ∈ s)
    (hmin : ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  classical
  revert j
  induction s using Finset.induction with
  | empty => intro j hj; simp at hj
  | insert a s ha ih =>
    intro j hj hmin
    rw [Finset.sum_insert ha]
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · have hgt : v (f j) < v (∑ i ∈ s, f i) := by
          have hall : ∀ i ∈ s, v (f j) < v (f i) := fun i hi ↦
            hmin i (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
          clear ih hmin hj ha
          induction s using Finset.induction with
          | empty => exact absurd rfl hne.ne_empty
          | insert b t hb ih2 =>
            rw [Finset.sum_insert hb]
            rcases t.eq_empty_or_nonempty with rfl | hnet
            · simpa using hall b (Finset.mem_insert_self b ∅)
            · have hb' : v (f j) < v (f b) := hall b (Finset.mem_insert_self b t)
              have ht' : v (f j) < v (∑ i ∈ t, f i) :=
                ih2 hnet (fun i hi ↦ hall i (Finset.mem_insert_of_mem hi))
              calc v (f j) < min (v (f b)) (v (∑ i ∈ t, f i)) := lt_min hb' ht'
                _ ≤ v (f b + ∑ i ∈ t, f i) := AddValuation.map_add v _ _
        rw [AddValuation.map_add_of_distinct_val v (ne_of_lt hgt)]
        exact min_eq_left (le_of_lt hgt)
    · have hgt : v (f j) < v (f a) :=
        hmin a (Finset.mem_insert_self a s) (by rintro rfl; exact ha hjs)
      have hsum : v (∑ i ∈ s, f i) = v (f j) :=
        ih hjs (fun i hi hij ↦ hmin i (Finset.mem_insert_of_mem hi) hij)
      rw [add_comm (f a),
        AddValuation.map_add_of_distinct_val v (by rw [hsum]; exact (ne_of_lt hgt)), hsum]
      exact min_eq_left (le_of_lt hgt)

/-- The `pi'`-adic valuation of the image in `A' = A[x]/(x^n - pi)` of a nonzero element
of `A` is a multiple of `n`, because `pi = (pi')^n`. -/
theorem exists_addVal_algebraMap_eq [IsDomain (A' π n)] [IsDiscreteValuationRing (A' π n)]
    (hn : 2 ≤ n) (hπ : Irreducible π) {a : A} (ha : a ≠ 0) :
    ∃ k : ℕ, IsDiscreteValuationRing.addVal (A' π n) (algebraMap A (A' π n) a)
      = ((n * k : ℕ) : ℕ∞) := by
  have hirr' : Irreducible (piRootA π n) := irreducible_piRootA π n hn hπ
  obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨k, ?_⟩
  have hmapa : algebraMap A (A' π n) a
      = (Units.map (algebraMap A (A' π n)).toMonoidHom u : (A' π n)) * (piRootA π n) ^ (n * k)
        := by
    rw [hku, map_mul, map_pow, ← piRootA_pow π n, ← pow_mul]
    rfl
  exact IsDiscreteValuationRing.addVal_def (algebraMap A (A' π n) a)
    (Units.map (algebraMap A (A' π n)).toMonoidHom u) hirr' (n * k) hmapa

/-- Suppose `A' = A[x]/(x^n - π)` is a domain. If `g` has degree `< n` and zero constant
coefficient, and the image of `g` in `A'` is associated to the image of an element of `A`, then
the image of `g` is zero. -/
theorem mk_eq_zero_of_associated_algebraMap [IsDomain (A' π n)] (hn : 2 ≤ n)
    (hπ : Irreducible π)
    (g : A[X]) (hdeg : g.natDegree < n) (hg0 : g.coeff 0 = 0) (c : A)
    (hassoc : Associated (AdjoinRoot.mk (kummerPolyA π n) g)
      (algebraMap A (A' π n) c)) :
    AdjoinRoot.mk (kummerPolyA π n) g = 0 := by
  classical
  have hdvr : IsDiscreteValuationRing (A' π n) := isDiscreteValuationRing_A' π n hn hπ
  have hirr' : Irreducible (piRootA π n) := irreducible_piRootA π n hn hπ
  set v := IsDiscreteValuationRing.addVal (A' π n) with hv
  have hvπ' : v (piRootA π n) = 1 := IsDiscreteValuationRing.addVal_uniformizer hirr'
  have key : ∀ a : A, a ≠ 0 → ∃ k : ℕ, v (algebraMap A (A' π n) a) = ((n * k : ℕ) : ℕ∞) :=
    fun _ ha ↦ exists_addVal_algebraMap_eq π n hn hπ ha
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero] at hassoc
    exact (associated_zero_iff_eq_zero _).mp hassoc
  by_contra hmk0
  have hval_eq : v (AdjoinRoot.mk (kummerPolyA π n) g) = v (algebraMap A (A' π n) c) := by
    obtain ⟨u, hu⟩ := hassoc
    rw [hv, ← hu, AddValuation.map_mul,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr u.isUnit, add_zero]
  obtain ⟨kc, hkc⟩ := key c hc
  set f : ℕ → A' π n := fun i ↦ algebraMap A (A' π n) (g.coeff i) * (piRootA π n) ^ i with hf
  have hmksum : AdjoinRoot.mk (kummerPolyA π n) g = ∑ i ∈ Finset.range n, f i :=
    mk_eq_sum_range π n g hdeg
  set s : Finset ℕ := (Finset.range n).filter (fun i ↦ g.coeff i ≠ 0) with hs
  have hsum_s : (∑ i ∈ Finset.range n, f i) = ∑ i ∈ s, f i := by
    rw [hs]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hx hi
    simp only [ Finset.mem_filter, not_and, not_not] at hi
    rw [hf]; simp only
    rw [hi hx, map_zero, zero_mul]
  have hsn : ∀ i ∈ s, i < n := fun i hi ↦ by
    rw [hs, Finset.mem_filter, Finset.mem_range] at hi; exact hi.1
  have hvf : ∀ i ∈ s, ∃ kk : ℕ, v (f i) = ((n * kk + i : ℕ) : ℕ∞) := by
    intro i hi
    rw [hs, Finset.mem_filter] at hi
    obtain ⟨ki, hki⟩ := key (g.coeff i) hi.2
    refine ⟨ki, ?_⟩
    rw [hf]
    simp only
    rw [AddValuation.map_mul, hki, AddValuation.map_pow, hvπ']
    rw [nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hse
    apply hmk0
    rw [hmksum, hsum_s, hse, Finset.sum_empty]
  have hdistinct : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) ≠ v (f j) := by
    intro i hi j hj hij
    obtain ⟨ki, hvi⟩ := hvf i hi
    obtain ⟨kj, hvj⟩ := hvf j hj
    rw [hvi, hvj]
    intro heq
    rw [Nat.cast_inj] at heq
    have hmod : i % n = j % n := by
      have : (n * ki + i) % n = (n * kj + j) % n := by rw [heq]
      rwa [Nat.mul_add_mod, Nat.mul_add_mod] at this
    rw [Nat.mod_eq_of_lt (hsn i hi), Nat.mod_eq_of_lt (hsn j hj)] at hmod
    exact hij hmod
  obtain ⟨j, hjs, hjmin⟩ := Finset.exists_min_image s (fun i ↦ v (f i)) hsne
  have hstrict : ∀ i ∈ s, i ≠ j → v (f j) < v (f i) := by
    intro i hi hij
    exact lt_of_le_of_ne (hjmin i hi) (hdistinct j hjs i hi (Ne.symm hij))
  have hvmkg : v (AdjoinRoot.mk (kummerPolyA π n) g) = v (f j) := by
    rw [hmksum, hsum_s]
    exact val_sum_eq_of_lt v hjs hstrict
  obtain ⟨kj, hvj⟩ := hvf j hjs
  have hjpos : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · exfalso
      rw [hj0, hs, Finset.mem_filter] at hjs
      exact hjs.2 hg0
    · exact hj0
  have hjn := hsn j hjs
  have hcast : ((n * kj + j : ℕ) : ℕ∞) = ((n * kc : ℕ) : ℕ∞) := by
    rw [← hvj, ← hvmkg, hval_eq, hkc]
  rw [Nat.cast_inj] at hcast
  have hdvd : n ∣ j := by
    have : j = n * kc - n * kj := by omega
    rw [this]
    exact Nat.dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)
  have := Nat.le_of_dvd hjpos hdvd
  omega

/-- Suppose `A' = A[x]/(x^n - π)` is a domain and `n` is prime to the residue characteristic of
`A`. Then every `n`-th root of unity in `A'` lies in the image of `A`. -/
theorem mem_algebraMap_range_of_pow_eq_one_A' [IsDomain (A' π n)] (hn : 2 ≤ n)
    (hπ : Irreducible π)
    (hcop : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A)) n)
    (w : A' π n) (hw : w ^ n = 1) :
    w ∈ (algebraMap A (A' π n)).range := by
  have hn1 : 1 ≤ n := by omega
  have hdvr : IsDiscreteValuationRing (A' π n) := isDiscreteValuationRing_A' π n hn hπ
  obtain ⟨ε, ε_of, ker_eq⟩ :
      ∃ ε : A' π n →+* A ⧸ IsLocalRing.maximalIdeal A,
        (∀ a : A, ε (algebraMap A (A' π n) a) = Ideal.Quotient.mk _ a) ∧
        RingHom.ker ε = Ideal.span {piRootA π n} :=
    ⟨residueA' π n hn1 hπ, residueA'_algebraMap π n hn1 hπ, ker_residueA' π n hn1 hπ⟩
  have hmaxeq : IsLocalRing.maximalIdeal (A' π n) = Ideal.span {piRootA π n} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (irreducible_piRootA π n hn hπ)
  have ε_zero_iff : ∀ x, ε x = 0 ↔ x ∈ IsLocalRing.maximalIdeal (A' π n) := fun x ↦ by
    rw [← RingHom.mem_ker, ker_eq, hmaxeq]
  obtain ⟨g, hgdeg, rfl⟩ := exists_natDegree_lt_mk_eq π n hn1 w
  set a₀ : A := g.coeff 0 with ha₀
  set A₀ : A' π n := algebraMap A (A' π n) a₀ with hA₀
  set b : A' π n := AdjoinRoot.mk (kummerPolyA π n) g - A₀ with hb
  set g' : A[X] := g - C a₀ with hg'
  have hbg' : b = AdjoinRoot.mk (kummerPolyA π n) g' := by
    rw [hb, hg', map_sub, hA₀, AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C, ha₀]
  have hg'0 : g'.coeff 0 = 0 := by rw [hg', coeff_sub, coeff_C_zero, ha₀, sub_self]
  have hg'deg : g'.natDegree < n := by
    rw [hg']
    have h1 : (g - C a₀).natDegree ≤ max g.natDegree (C a₀).natDegree := natDegree_sub_le _ _
    have h2 : (C a₀).natDegree = 0 := natDegree_C a₀
    rw [h2, Nat.max_eq_left (Nat.zero_le _)] at h1
    omega
  have hwsplit : (AdjoinRoot.mk (kummerPolyA π n)) g = A₀ + b := by rw [hb]; ring
  have εw : ε (AdjoinRoot.mk (kummerPolyA π n) g) = Ideal.Quotient.mk _ a₀ := by
    rw [hwsplit, map_add, hA₀, ε_of]
    have hbker : b ∈ RingHom.ker ε := by
      rw [ker_eq, hbg', hg', Ideal.mem_span_singleton]
      have hdvd : (X : A[X]) ∣ (g - C a₀) := by
        rw [X_dvd_iff, coeff_sub, coeff_C_zero, ha₀, sub_self]
      obtain ⟨h, hh⟩ := hdvd
      refine ⟨AdjoinRoot.mk (kummerPolyA π n) h, ?_⟩
      rw [hh, map_mul, AdjoinRoot.mk_X]
    rw [RingHom.mem_ker] at hbker
    rw [hbker, add_zero]
  have hwunit : IsUnit (AdjoinRoot.mk (kummerPolyA π n) g) :=
    IsUnit.of_mul_eq_one ((AdjoinRoot.mk (kummerPolyA π n) g) ^ (n - 1))
      (by rw [← pow_succ', Nat.sub_add_cancel hn1, hw])
  have hnK : IsUnit (n : A) := isUnit_natCast_of_coprime_ringChar n (by omega) hcop
  have ha₀unit : IsUnit a₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr hwunit)
      ((ε_zero_iff _).mp (by rw [εw, Ideal.Quotient.eq_zero_iff_mem]; exact hmem))
  set S : A' π n := ∑ i ∈ Finset.range n,
    (AdjoinRoot.mk (kummerPolyA π n) g) ^ i * A₀ ^ (n - 1 - i) with hS
  have hgeom : S * b = (AdjoinRoot.mk (kummerPolyA π n) g) ^ n - A₀ ^ n := by
    rw [hS, hb]
    exact geom_sum₂_mul (AdjoinRoot.mk (kummerPolyA π n) g) A₀ n
  have εS : ε S = (n : A ⧸ IsLocalRing.maximalIdeal A) * (Ideal.Quotient.mk _ a₀) ^ (n-1) := by
    rw [hS, map_sum]
    have hterm : ∀ i ∈ Finset.range n,
        ε ((AdjoinRoot.mk (kummerPolyA π n) g) ^ i * A₀ ^ (n - 1 - i))
          = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a₀) ^ (n-1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, εw, hA₀, ε_of, ← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hεSunit : IsUnit (ε S) := by
    rw [εS]
    apply IsUnit.mul
    · have : (n : A ⧸ IsLocalRing.maximalIdeal A) = Ideal.Quotient.mk _ (n : A) := by
        rw [map_natCast]
      rw [this]
      exact (RingHom.isUnit_map _ hnK)
    · exact (RingHom.isUnit_map _ ha₀unit).pow _
  have hSunit : IsUnit S := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    rw [(ε_zero_iff S).mpr hmem] at hεSunit
    exact not_isUnit_zero hεSunit
  have hceq : algebraMap A (A' π n) (1 - a₀ ^ n) = S * b := by
    rw [map_sub, map_one, map_pow, ← hA₀, hgeom, hw]
  have hassoc : Associated b (algebraMap A (A' π n) (1 - a₀ ^ n)) := by
    rw [hceq]
    exact associated_unit_mul_right b S hSunit
  have hb0 : b = 0 := by
    rw [hbg']
    exact mk_eq_zero_of_associated_algebraMap π n hn hπ g' hg'deg hg'0 (1 - a₀ ^ n)
        (by rw [← hbg']; exact hassoc)
  rw [hwsplit, hb0, add_zero, hA₀]
  exact ⟨a₀, rfl⟩

/-- If `n` is prime to the residue characteristic of `A`, then every `n`-th root of unity in
`K_1` lies in the image of `K`. -/
theorem mem_algebraMap_range_of_pow_eq_one_K1 [Fact (Irreducible (kummerPoly K π n))]
    (hn : 2 ≤ n) (hπ : Irreducible π)
    (hcop : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A)) n)
    (ζ : K1 K π n) (hζ : ζ ^ n = 1) :
    ζ ∈ (algebraMap K (K1 K π n)).range := by
  have hn1 : 1 ≤ n := by omega
  have hζint : IsIntegral A ζ := by
    refine ⟨(X : A[X]) ^ n - C (1 : A), monic_X_pow_sub_C (1 : A) (by omega), ?_⟩
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hζ, map_one, sub_self]
  have hζA1 : ζ ∈ A1 K π n := hζint
  have e : A' π n ≃ₐ[A] A1 K π n := canonAlgEquiv K π n hn hπ
  have ee : (A' π n) ≃+* (A1 K π n) := e.toRingEquiv
  have hdA' : IsDomain (A' π n) := ee.injective.isDomain ee.toRingHom
  set Z : A1 K π n := ⟨ζ, hζA1⟩ with hZ
  set w : A' π n := e.symm Z with hw
  have hew : e w = Z := by rw [hw, AlgEquiv.apply_symm_apply]
  have hwpow : w ^ n = 1 := by
    have hmain : e (w ^ n) = e 1 := by
      rw [map_pow, map_one, hew, hZ]
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζ
    exact e.injective hmain
  obtain ⟨a₀, ha₀⟩ := mem_algebraMap_range_of_pow_eq_one_A' π n hn hπ hcop w hwpow
  have hZeq : Z = algebraMap A (A1 K π n) a₀ := by
    rw [← hew, ← ha₀]
    exact e.commutes a₀
  have hζeq : ζ = algebraMap A (K1 K π n) a₀ := by
    have hcoe : (Z : K1 K π n) = ((algebraMap A (A1 K π n) a₀ : A1 K π n) : K1 K π n) := by
      rw [hZeq]
    rw [hZ] at hcoe
    simp only at hcoe
    rw [hcoe]
    rw [show ((algebraMap A (A1 K π n) a₀ : A1 K π n) : K1 K π n)
          = algebraMap (A1 K π n) (K1 K π n) (algebraMap A (A1 K π n) a₀) from rfl,
       ← IsScalarTower.algebraMap_apply A (A1 K π n) (K1 K π n)]
  rw [hζeq, IsScalarTower.algebraMap_apply A K (K1 K π n)]
  exact ⟨algebraMap A K a₀, rfl⟩

/-- For a positive divisor `d` of `n`, the subfield of `K_1` generated over `K` by the `d`-th
root `(pi')^{n/d}` of `pi` has degree `d` over `K`. -/
theorem finrank_adjoin_pow_piRoot [Fact (Irreducible (kummerPoly K π n))]
    (hπ : Irreducible π) {d : ℕ} (hdpos : 0 < d) (hdvd : d ∣ n) :
    Module.finrank K (IntermediateField.adjoin K {(piRoot K π n) ^ (n / d)}) = d := by
  have hαd := piRoot_pow_div_pow K π n hdvd
  set α : K1 K π n := (piRoot K π n) ^ (n / d) with hα
  have hαirr : Irreducible (kummerPoly K π d) := kummerPoly_irreducible K π d hdpos hπ
  have hαaeval : (Polynomial.aeval α) (kummerPoly K π d) = 0 := by
    simp only [kummerPoly]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hαd,
      ← IsScalarTower.algebraMap_apply A K (K1 K π n)]
    ring
  have hmon : (kummerPoly K π d).Monic := by
    simp only [kummerPoly]
    exact monic_X_pow_sub_C _ (by omega)
  have hαint : IsIntegral K α := ⟨kummerPoly K π d, hmon, by rw [← hαaeval]; rfl⟩
  have hminα : minpoly K α = kummerPoly K π d :=
    (minpoly.eq_of_irreducible_of_monic hαirr hαaeval hmon).symm
  rw [IntermediateField.adjoin.finrank hαint, hminα]
  simp only [kummerPoly]
  exact Polynomial.natDegree_X_pow_sub_C

/-- Let `n` be prime to the residue characteristic of `A`, let `d` be a positive divisor of `n`
and let `L` be an intermediate field of `K_1 / K` with `[K_1 : L] = n / d`. Then the `d`-th root
`(pi')^{n/d}` of `pi` lies in `L`. -/
theorem pow_piRoot_mem_of_finrank_eq [Fact (Irreducible (kummerPoly K π n))]
    (hn : 2 ≤ n) (hπ : Irreducible π)
    (hcop : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A)) n)
    (L : IntermediateField K (K1 K π n)) {d : ℕ} (hdpos : 0 < d) (hdvd : d ∣ n)
    (hm : Module.finrank L (K1 K π n) = n / d) :
    (piRoot K π n) ^ (n / d) ∈ L := by
  classical
  have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
  have hpin : (piRoot K π n) ^ n = algebraMap A (K1 K π n) π := piRoot_pow K π n
  have hαd := piRoot_pow_div_pow K π n hdvd
  set π' : K1 K π n := piRoot K π n
  set α : K1 K π n := π' ^ (n / d) with hα
  have hmemπn : π' ^ n ∈ L := by
    rw [hpin, IsScalarTower.algebraMap_apply A K (K1 K π n)]
    exact IntermediateField.algebraMap_mem L _
  set πL : L := ⟨π' ^ n, hmemπn⟩
  have hπLcoe : (algebraMap L (K1 K π n)) πL = π' ^ n := rfl
  have hnormpow : (Algebra.norm L π') ^ n
      = πL ^ Module.finrank L (K1 K π n) := by
    have h1 : (Algebra.norm L π') ^ n = Algebra.norm L (π' ^ n) := (map_pow _ _ _).symm
    rw [h1, ← hπLcoe, Algebra.norm_algebraMap]
  set P : K1 K π n := (algebraMap L (K1 K π n)) (Algebra.norm L π') with hP
  have hPmem : P ∈ L := by
    rw [hP]; exact (Algebra.norm L π').2
  have hAinj : Function.Injective (algebraMap A (K1 K π n)) := by
    rw [IsScalarTower.algebraMap_eq A K (K1 K π n)]
    exact (algebraMap K (K1 K π n)).injective.comp (IsFractionRing.injective A K)
  have hαne : α ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : d ≠ 0)] at hαd
    have hπne : (algebraMap A (K1 K π n)) π ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hAinj]
      exact hπ.ne_zero
    exact hπne hαd.symm
  have hπ'ne : π' ≠ 0 := by
    intro h
    apply hαne
    rw [hα, h]
    exact zero_pow (by omega : n / d ≠ 0)
  have hnormne : Algebra.norm L π' ≠ 0 := Algebra.norm_ne_zero_iff.mpr hπ'ne
  have hPne : P ≠ 0 := by
    rw [hP]
    simpa using (map_ne_zero_iff _ (algebraMap L (K1 K π n)).injective).mpr hnormne
  have hPn : P ^ n = (π' ^ n) ^ (n / d) := by
    rw [hP, ← map_pow, hnormpow, hm, map_pow, hπLcoe]
  have hαn : α ^ n = (π' ^ n) ^ (n / d) := by
    rw [hα, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hαP : α ^ n = P ^ n := by rw [hαn, hPn]
  set ζ₀ : K1 K π n := α * P⁻¹ with hζ₀def
  have hζ₀pow : ζ₀ ^ n = 1 := by
    rw [hζ₀def, mul_pow, inv_pow, hαP, mul_inv_cancel₀ (pow_ne_zero n hPne)]
  obtain ⟨k, hk⟩ := mem_algebraMap_range_of_pow_eq_one_K1 K π n hn hπ hcop ζ₀ hζ₀pow
  have hζ₀mem : ζ₀ ∈ L := by
    rw [← hk]
    exact IntermediateField.algebraMap_mem L k
  have hαeq : α = ζ₀ * P := by
    rw [hζ₀def, mul_assoc, inv_mul_cancel₀ hPne, mul_one]
  rw [hαeq]
  exact mul_mem hζ₀mem hPmem

/-- If `n` is prime to the residue characteristic of `A`, then every intermediate field
`K ⊆ L ⊆ K_1` is of the form `L = K[pi^{1/d}]` for some positive divisor `d | n`: `L` is generated
over `K` by the `d`-th root `(pi')^{n/d}` of `pi`, and `[L : K] = d` and `[K_1 : L] = n / d`. -/
@[stacks 09EV "(6)"]
theorem intermediateField_eq_adjoin [Fact (Irreducible (kummerPoly K π n))]
    (hn : 2 ≤ n) (hπ : Irreducible π)
    (hcop : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = 0 ∨
      Nat.Coprime (ringChar (A ⧸ IsLocalRing.maximalIdeal A)) n)
    (L : IntermediateField K (K1 K π n)) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧
      L = IntermediateField.adjoin K {(piRoot K π n) ^ (n / d)} ∧
      Module.finrank K L = d ∧
      Module.finrank L (K1 K π n) = n / d := by
  have hK1 : Module.finrank K (K1 K π n) = n := finrank_K1 K π n hn hπ
  set d : ℕ := Module.finrank K L with hd
  have hmul : Module.finrank K L * Module.finrank L (K1 K π n)
      = Module.finrank K (K1 K π n) := Module.finrank_mul_finrank K L (K1 K π n)
  have hdvd : d ∣ n := by
    rw [← hK1, ← hmul]; exact dvd_mul_right _ _
  have hdpos : 0 < d := by
    rw [hd]
    exact Module.finrank_pos
  have hm : Module.finrank L (K1 K π n) = n / d :=
    Nat.eq_of_mul_eq_mul_left hdpos (by rw [hmul, hK1, Nat.mul_div_cancel' hdvd])
  have hAdeg : Module.finrank K (IntermediateField.adjoin K {(piRoot K π n) ^ (n / d)}) = d :=
    finrank_adjoin_pow_piRoot K π n hπ hdpos hdvd
  refine ⟨d, hdpos, hdvd, ?_, rfl, hm⟩
  have hle : IntermediateField.adjoin K {(piRoot K π n) ^ (n / d)} ≤ L := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact pow_piRoot_mem_of_finrank_eq K π n hn hπ hcop L hdpos hdvd hm
  have : FiniteDimensional K (IntermediateField.adjoin K {(piRoot K π n) ^ (n / d)}) := by
    apply FiniteDimensional.of_finrank_pos
    omega
  exact (IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hAdeg])).symm

end Statements

end Stacks.KummerExtension
