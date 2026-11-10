module

public import StacksFrontier.RingTheory.Length.RingEquiv
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Intersection.AlgebraicMultiplicities.ComputingPolynomial
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FrobeniusAction.IdealIndependentFlat
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FrobeniusAction.LengthQuotientPowers
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.HilbertSamuel.DegreeInvariance
public import StacksFrontier.RingTheory.HilbertSamuel.Dimension
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Kunz's theorem

For a Noetherian ring in which a prime number vanishes, regularity is equivalent to flatness of
the Frobenius endomorphism.

## Main definitions

* `frobeniusOfPrime` is the Frobenius endomorphism of a commutative ring in which a prime number
  vanishes.

## Main results

* `isRegularRing_iff_frobeniusOfPrime_flat` is Kunz's characterization of regular Noetherian
  rings.

## Implementation notes

The Frobenius map is built from the hypotheses that `p` is prime and that its image in the ring
is zero rather than from `ExpChar`. Unlike `frobenius`, this formulation also covers the zero
ring, where `CharP A p` holds for no prime `p`.

In the local case the Frobenius iterates are compared through a universe-level copy `ULift A` of
the ring, so that the source action and the target's regular-module action remain distinct and
`length_baseChange_eq_length_mul_length_quotient` applies.

## References

* [Kunz, *Characterizations of regular local rings of characteristic p*][Kunz-flat]
* [Stacks Project, Tag 0EC0](https://stacks.math.columbia.edu/tag/0EC0)
-/

@[expose] public section

open Polynomial

universe u

/-- The Frobenius endomorphism associated to a prime number which vanishes in a commutative
ring. This version includes the zero ring. -/
def frobeniusOfPrime {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) :
    A →+* A where
  toFun a := a ^ p
  map_one' := one_pow p
  map_mul' a b := mul_pow a b p
  map_zero' := zero_pow hp.ne_zero
  map_add' a b := by
    simpa [hchar] using add_pow_prime_eq hp a b

/-- The Frobenius endomorphism `frobeniusOfPrime p hp hchar` sends `a` to `a ^ p`. -/
@[simp]
lemma frobeniusOfPrime_apply {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hchar : (p : A) = 0) (a : A) : frobeniusOfPrime p hp hchar a = a ^ p := rfl

/-- A proper ideal of a local ring whose radical is the maximal ideal has zero-dimensional
quotient. -/
private lemma dim_quotient_eq_zero_of_radical_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
    (hI : I.radical = IsLocalRing.maximalIdeal R) (hproper : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) = 0 := by
  have hnontrivial : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  apply (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := R ⧸ I)).mp
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro J hJ
  have hmaxle : IsLocalRing.maximalIdeal R ≤ J := by
    rw [← hI]
    exact hJ.1.1.radical_le_iff.mpr hJ.1.2
  have hJmax : IsLocalRing.maximalIdeal R = J :=
    (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ.1.1.ne_top hmaxle
  rw [← hJmax]
  exact IsLocalRing.maximalIdeal.isMaximal R

/-- The range of the enumeration of a finite set by `Fin s.card` is the set itself. -/
private lemma range_equivFin_symm {A : Type*} (s : Finset A) :
    Set.range (fun j : Fin s.card ↦ (s.equivFin.symm j : A)) = (s : Set A) := by
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact (s.equivFin.symm j).property
  · intro hz
    exact ⟨s.equivFin ⟨z, hz⟩, by simp⟩

/-- A finite set generating the maximal ideal of a local ring with as few elements as possible
is ideal-independent. -/
private lemma isIdealIndependent_of_minimalGeneratingFinset
    {A : Type*} [CommRing A] [IsLocalRing A] (s : Finset A)
    (hspan : Ideal.span (s : Set A) = IsLocalRing.maximalIdeal A)
    (hcard : s.card = (IsLocalRing.maximalIdeal A).spanFinrank) :
    IsIdealIndependent (fun i : Fin s.card ↦ (s.equivFin.symm i : A)) := by
  classical
  intro a ha i
  have hgen : Ideal.span (Set.range fun j : Fin s.card ↦ (s.equivFin.symm j : A)) =
      IsLocalRing.maximalIdeal A := by rw [range_equivFin_symm, hspan]
  by_contra hai
  rw [hgen] at hai
  have hunit : IsUnit (a i) := (IsLocalRing.notMem_maximalIdeal).mp hai
  let u : Finset A := s.erase (s.equivFin.symm i).val
  have hxi : (s.equivFin.symm i : A) ∈ Ideal.span (u : Set A) := by
    have hsum : (∑ j : Fin s.card, a j * (s.equivFin.symm j : A)) = 0 := by
      have h := ha
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h
      simpa only [smul_eq_mul] using h
    have hother : (∑ j ∈ Finset.univ.erase i, a j * (s.equivFin.symm j : A)) =
        -(a i * (s.equivFin.symm i : A)) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
      exact (eq_neg_iff_add_eq_zero).2 hsum
    have hother_mem :
        (∑ j ∈ Finset.univ.erase i, a j * (s.equivFin.symm j : A)) ∈
          Ideal.span (u : Set A) := by
      apply Ideal.sum_mem
      intro j hj
      apply Ideal.mul_mem_left
      apply Ideal.subset_span
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hval : (s.equivFin.symm j).val ∈ u := by
        simp only [u, Finset.mem_erase]
        constructor
        · intro heq
          have : j = i := by
            have h' := congrArg s.equivFin (Subtype.ext heq)
            simpa using h'
          exact hji this
        · exact (s.equivFin.symm j).property
      exact hval
    have hprod_mem : a i * (s.equivFin.symm i : A) ∈ Ideal.span (u : Set A) := by
      have hneg : -(∑ j ∈ Finset.univ.erase i, a j * (s.equivFin.symm j : A)) ∈
          Ideal.span (u : Set A) := (Ideal.span (u : Set A)).neg_mem hother_mem
      rw [hother] at hneg
      simpa using hneg
    obtain ⟨v, hv⟩ := hunit
    have hinv_mem : (↑(v⁻¹) : A) *
        (a i * (s.equivFin.symm i : A)) ∈ Ideal.span (u : Set A) :=
      Ideal.mul_mem_left _ _ hprod_mem
    simpa [← hv, mul_assoc] using hinv_mem
  have hspanU : Ideal.span (u : Set A) = IsLocalRing.maximalIdeal A := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rw [← hspan]
      exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_erase.mp hz).2)
    · rw [← hspan]
      apply Ideal.span_le.mpr
      intro z hz
      by_cases hzi : z = (s.equivFin.symm i : A)
      · subst z
        exact hxi
      · exact Ideal.subset_span (by
          simp only [u, Finset.mem_coe, Finset.mem_erase]
          exact ⟨hzi, hz⟩)
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (M := A) u.finite_toSet
  have hcardU : u.card + 1 = s.card := by
    rw [show u = s.erase (s.equivFin.symm i).val by rfl,
      Finset.card_erase_of_mem (s.equivFin.symm i).property]
    exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, (s.equivFin.symm i).property⟩)
  have hle' : (IsLocalRing.maximalIdeal A).spanFinrank ≤ u.card := by
    rw [← hspanU]
    simpa using hle
  have hsmall : (IsLocalRing.maximalIdeal A).spanFinrank < s.card := by
    rw [← hcardU]
    exact Nat.lt_succ_of_le hle'
  exact (Nat.not_lt_of_ge (le_of_eq hcard)) hsmall

/-- If the `k`-th powers of `r` elements lie in an ideal `J`, then the `(r * k + 1)`-st power of
the ideal they span is contained in `J`. -/
private lemma pow_span_fin_le_of_powers_mem
    {A : Type*} [CommRing A] (r k : ℕ) (x : Fin r → A) (J : Ideal A)
    (hk : ∀ i, x i ^ k ∈ J) :
    (Ideal.span (Set.range x)) ^ (r * k + 1) ≤ J := by
  induction r with
  | zero =>
      have hrange : Set.range x = ∅ := by
        ext a
        simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false, not_exists]
        intro i
        exact Fin.elim0 i
      rw [hrange, Ideal.span_empty]
      simp
  | succ r ih =>
      let y : A := x (Fin.last r)
      let z : Fin r → A := fun i ↦ x i.castSucc
      have hz : ∀ i, z i ^ k ∈ J := fun i ↦ hk i.castSucc
      have hy : y ^ k ∈ J := hk (Fin.last r)
      have hspan : Ideal.span (Set.range x) =
          Ideal.span (Set.range z) ⊔ Ideal.span ({y} : Set A) := by
        have hx : x = Fin.snoc z y := by
          funext i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simp [y]
          · simp [z]
        rw [hx, Fin.range_snoc, Set.insert_eq, Set.union_comm, Ideal.span_union]
      rw [hspan, show (r + 1) * k + 1 = (r * k + 1) + k by ring]
      refine (Ideal.sup_pow_add_le_pow_sup_pow).trans ?_
      apply sup_le
      · exact ih z hz
      · rw [Ideal.span_singleton_pow]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)

/-- If one rational polynomial is eventually dominated by another at the naturals and the two
have the same nonnegative degree, its leading coefficient is the smaller. -/
private lemma leadingCoeff_le_of_eventually_eval_le {P Q : ℚ[X]}
    (hPQ : ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ))
    (hdeg : P.degree = Q.degree) (hnonneg : 0 ≤ P.degree) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  by_cases hpos : 0 < P.degree
  · exact HilbertSamuel.leadingCoeff_cmp P Q 0
      (by filter_upwards [hPQ] with n hn; linarith) hdeg hpos
  · have hdegP : P.degree = 0 := le_antisymm (not_lt.mp hpos) hnonneg
    have hdegQ : Q.degree = 0 := by rw [← hdeg]; exact hdegP
    have hPne : P ≠ 0 := by intro h; simp [h] at hdegP
    have hQne : Q ≠ 0 := by intro h; simp [h] at hdegQ
    have hnatP : P.natDegree = 0 := by
      exact_mod_cast (Polynomial.degree_eq_natDegree hPne ▸ hdegP)
    have hnatQ : Q.natDegree = 0 := by
      exact_mod_cast (Polynomial.degree_eq_natDegree hQne ▸ hdegQ)
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hnatP
    obtain ⟨b, rfl⟩ := Polynomial.natDegree_eq_zero.mp hnatQ
    have hab : ∀ᶠ n : ℕ in Filter.atTop, a ≤ b := by
      filter_upwards [hPQ] with n hn
      simpa using hn
    obtain ⟨n, hn⟩ := Filter.Eventually.exists hab
    simpa using hn

/-- The Hilbert–Samuel degree of a Noetherian local ring is the degree of any polynomial
computing the Hilbert–Samuel function for any ideal of definition. -/
private lemma hilbertSamuelDegree_eq_degree_of_computes_of_radical_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I.radical = IsLocalRing.maximalIdeal A)
    {P : ℚ[X]} (hP : Ideal.ComputesHilbertSamuelPoly I A P) :
    Module.hilbertSamuelDegree A A = P.degree := by
  obtain ⟨_, e, hdegree⟩ :=
    Ideal.exists_degree_eq_of_eventually_eval_eq_length_quotient_smul_pow (R := A) A
  have hmrad : (IsLocalRing.maximalIdeal A).radical = IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime.radical
  obtain ⟨Q, hQ⟩ := Ideal.exists_computesHilbertSamuelPoly (IsLocalRing.maximalIdeal A) hmrad A
  have h1 : Module.hilbertSamuelDegree A A = Q.degree :=
    Ideal.hilbertSamuelDegree_eq_degree_of_computes hQ
  rw [h1, (hdegree _ hmrad Q).2 hQ, (hdegree I hI P).2 hP]

/-- If `P` computes the Hilbert–Samuel function of `R` for `I`, then eventually the length of
`R ⧸ I ^ (n + 1)` is a natural number `a` with `P.eval n = a`. -/
private lemma eventually_length_quotient_pow_eq {R : Type*} [CommRing R] {I : Ideal R} {P : ℚ[X]}
    (h : Ideal.ComputesHilbertSamuelPoly I R P) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ a : ℕ,
      Module.length R (R ⧸ I ^ (n + 1)) = a ∧ P.eval (n : ℚ) = a := by
  filter_upwards [h] with n ⟨a, ha, hpa⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at ha
  exact ⟨a, ha, hpa⟩

/-- Iterates of a flat ring endomorphism are flat. -/
private lemma frobenius_iterate_flat {A : Type*} [CommRing A]
    (F : A →+* A) (hF : RingHom.Flat F) (n : ℕ) : RingHom.Flat (F ^ n) := by
  induction n with
  | zero =>
      convert RingHom.Flat.id A using 1
      ext x
      rfl
  | succ n ih =>
      rw [pow_succ, RingHom.mul_def]
      exact RingHom.Flat.comp hF ih

/-- The Frobenius endomorphism of a local ring is a local homomorphism. -/
private lemma frobeniusOfPrime_isLocalHom {A : Type*} [CommRing A] [IsLocalRing A]
    (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) :
    IsLocalHom (frobeniusOfPrime p hp hchar) :=
  ⟨fun x hu ↦ (isUnit_pow_iff hp.ne_zero).mp (by simpa using hu)⟩

/-- Iterates of a local ring endomorphism are local homomorphisms. -/
private lemma frobenius_iterate_isLocalHom {A : Type*} [CommRing A] [IsLocalRing A]
    (F : A →+* A) (hF : IsLocalHom F) (n : ℕ) : IsLocalHom (F ^ n) := by
  induction n with
  | zero =>
      convert isLocalHom_id A using 1
      ext x
      rfl
  | succ n ih =>
      have : IsLocalHom (F ^ n) := ih
      rw [pow_succ, RingHom.mul_def]
      exact RingHom.isLocalHom_comp (F ^ n) F

/-- The `n`-th iterate of the Frobenius endomorphism raises to the power `p ^ n`. -/
private lemma frobeniusOfPrime_iterate_apply {A : Type*} [CommRing A]
    (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) (n : ℕ) (x : A) :
    (frobeniusOfPrime p hp hchar ^ n) x = x ^ p ^ n := by
  change ((fun y : A ↦ y ^ p)^[n]) x = x ^ p ^ n
  rw [pow_iterate]

/-- A Noetherian local ring with flat Frobenius endomorphism is regular. -/
private lemma isRegularLocalRing_of_frobeniusOfPrime_flat {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (p : ℕ) (hp : p.Prime)
    (hchar : (p : A) = 0) (hflat : RingHom.Flat (frobeniusOfPrime p hp hchar)) :
    IsRegularLocalRing A := by
  classical
  by_cases hsub : Subsingleton A
  · apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    exfalso
    exact zero_ne_one (Subsingleton.elim (0 : A) 1)
  let F := frobeniusOfPrime p hp hchar
  have hFlocal : IsLocalHom F := frobeniusOfPrime_isLocalHom p hp hchar
  let S : Type u := ULift.{u, u} A
  let e : A ≃+* S := (ULift.ringEquiv : ULift.{u, u} A ≃+* A).symm
  let : IsLocalRing S := e.isLocalRing
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv A e
  let mA : Ideal A := IsLocalRing.maximalIdeal A
  let mS : Ideal S := IsLocalRing.maximalIdeal S
  have hfg : mA.FG := IsNoetherian.noetherian mA
  obtain ⟨s, hsCard, hsSpan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  let r := s.card
  let x : Fin r → A := fun i ↦ (s.equivFin.symm i : A)
  have hxspan : Ideal.span (Set.range x) = mA := by
    rw [show Set.range x = (s : Set A) from range_equivFin_symm s]
    exact hsSpan
  have hind : IsIdealIndependent x :=
    isIdealIndependent_of_minimalGeneratingFinset s hsSpan hsCard
  let y : Fin r → S := fun i ↦ e (x i)
  have hyspan : Ideal.span (Set.range y) = mS := by
    calc
      Ideal.span (Set.range y) = Ideal.map e (Ideal.span (Set.range x)) := by
        rw [Ideal.map_span]
        congr 1
        ext z
        simp [y]
      _ = mS := by rw [hxspan, IsLocalRing.map_ringEquiv_maximalIdeal]
  let : IsLocalHom (e : A →+* S) := IsLocalHom.of_surjective _ e.surjective
  have hEflat : RingHom.Flat (e : A →+* S) := RingHom.Flat.of_bijective e.bijective
  have hflatPow : ∀ n, RingHom.Flat (F ^ n) := frobenius_iterate_flat F hflat
  have hlocalPow : ∀ n, IsLocalHom (F ^ n) := frobenius_iterate_isLocalHom F hFlocal
  let φ : ℕ → A →+* S := fun n ↦ (e : A →+* S).comp (F ^ n)
  have hφflat (n : ℕ) : RingHom.Flat (φ n) :=
    RingHom.Flat.comp (hflatPow n) hEflat
  have hφlocal (n : ℕ) : IsLocalHom (φ n) := by
    let : IsLocalHom (F ^ n) := hlocalPow n
    exact RingHom.isLocalHom_comp (e : A →+* S) (F ^ n)
  let J : ℕ → Ideal S := fun n ↦ Ideal.map (φ n) mA
  let q : ℕ → ℕ := fun n ↦ p ^ n
  have hφx (n : ℕ) (i : Fin r) : φ n (x i) = y i ^ q n := by
    change e ((frobeniusOfPrime p hp hchar ^ n) (x i)) = e (x i) ^ p ^ n
    rw [frobeniusOfPrime_iterate_apply]
    rw [map_pow]
  have hJspan (n : ℕ) : J n = Ideal.span (Set.range fun i ↦ y i ^ q n) := by
    change Ideal.map (φ n) mA = _
    rw [← hxspan, Ideal.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hφx n i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hφx n i⟩
  have hindPow (n : ℕ) : ∀ (a : Fin r → S),
      (∑ i, a i * y i ^ q n) = 0 →
        ∀ i, a i ∈ Ideal.span (Set.range fun j ↦ y j ^ q n) := by
    have hi := isIdealIndependent_map_of_flat (φ n) (hφflat n) hind
    intro a ha i
    let b : Fin r →₀ S := Finsupp.equivFunOnFinite.symm a
    have ha' : (∑ i, a i * φ n (x i)) = 0 := by
      simpa only [← hφx n] using ha
    have hb : Finsupp.linearCombination S (fun j ↦ φ n (x j)) b = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
      simpa [b, smul_eq_mul] using ha'
    have hz := hi b hb i
    simpa [b, ← hφx n] using hz
  have hgen (n : ℕ) (i : Fin r) : y i ^ q n ∈ J n := by
    rw [← hφx n i]
    exact Ideal.mem_map_of_mem (φ n) (by
      rw [← hxspan]
      exact Ideal.subset_span (Set.mem_range_self i))
  have hJrad (n : ℕ) : (J n).radical = mS := by
    have hJle : J n ≤ mS := by
      let : IsLocalHom (φ n) := hφlocal n
      exact IsLocalRing.map_maximalIdeal_le (φ n)
    apply le_antisymm
    · calc
        (J n).radical ≤ mS.radical := Ideal.radical_mono hJle
        _ = mS := (IsLocalRing.maximalIdeal.isMaximal S).isPrime.radical
    · rw [← hyspan]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change y i ∈ (J n).radical
      rw [Ideal.mem_radical_iff]
      exact ⟨q n, hgen n i⟩
  have hmArad : mA.radical = IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime.radical
  obtain ⟨P, hP⟩ := Ideal.exists_computesHilbertSamuelPoly mA hmArad A
  have hlenEquiv (t : ℕ) : Module.length A (A ⧸ (mA ^ t)) =
      Module.length S (S ⧸ (mS ^ t)) := by
    calc
      Module.length A (A ⧸ (mA ^ t)) =
          Module.length S (S ⧸ (Ideal.map e.toRingHom (mA ^ t))) :=
        Module.quotient_length_eq_of_ringEquiv e (mA ^ t)
      _ = Module.length S (S ⧸ (mS ^ t)) := by
        rw [Ideal.map_pow]
        have hmax : Ideal.map e.toRingHom mA = mS := by
          change Ideal.map e.toRingHom (IsLocalRing.maximalIdeal A) =
            IsLocalRing.maximalIdeal S
          exact IsLocalRing.map_ringEquiv_maximalIdeal e
        rw [hmax]
  have hdegP : Module.hilbertSamuelDegree A A = P.degree :=
    Ideal.hilbertSamuelDegree_eq_degree_of_computes hP
  have hdimEq : Module.hilbertSamuelDegree A A = Module.hilbertSamuelDegree S S := by
    apply WithBot.map_injective (fun a b h ↦ WithTop.coe_injective h)
    change WithBot.map (Nat.cast : ℕ → ℕ∞) (Module.hilbertSamuelDegree A A) =
      WithBot.map (Nat.cast : ℕ → ℕ∞) (Module.hilbertSamuelDegree S S)
    rw [Module.hilbertSamuelDegree_eq_supportDim A A, Module.supportDim_self_eq_ringKrullDim,
      Module.hilbertSamuelDegree_eq_supportDim S S, Module.supportDim_self_eq_ringKrullDim,
      ringKrullDim_eq_of_ringEquiv e]
  have hdegQ (n : ℕ) : ∃ Q : ℚ[X], Ideal.ComputesHilbertSamuelPoly (J n) S Q ∧
      Q.degree = P.degree := by
    obtain ⟨Q, hQ⟩ := Ideal.exists_computesHilbertSamuelPoly (J n) (hJrad n) S
    refine ⟨Q, hQ, ?_⟩
    calc
      Q.degree = Module.hilbertSamuelDegree S S :=
        (hilbertSamuelDegree_eq_degree_of_computes_of_radical_eq (J n) (hJrad n) hQ).symm
      _ = Module.hilbertSamuelDegree A A := hdimEq.symm
      _ = P.degree := hdegP
  have hFiber (n : ℕ) : Module.length S (S ⧸ J n) = (q n ^ r : ℕ∞) := by
    rw [hJspan n]
    simpa [Finset.prod_const] using
      (length_quotient_span_powers_eq_prod y (fun _ ↦ q n) hyspan
        (fun _ ↦ Nat.pow_pos hp.pos) (hindPow n))
  have hscale (n t : ℕ) :
      Module.length A (A ⧸ (mA ^ (t + 1))) * (q n ^ r : ℕ∞) =
        Module.length S (S ⧸ ((J n) ^ (t + 1))) := by
    let : Algebra A S := (φ n).toAlgebra
    let : Module A S := (φ n).toAlgebra.toModule
    let : IsLocalHom (algebraMap A S) := by
      change IsLocalHom (φ n)
      exact hφlocal n
    have hflatAlg : (algebraMap A S).Flat := by
      change RingHom.Flat (φ n)
      exact hφflat n
    let : Module.Flat A S := RingHom.flat_algebraMap_iff.mp hflatAlg
    have hb := length_baseChange_eq_length_mul_length_quotient A S
      (A ⧸ (mA ^ (t + 1)))
    have hext : extendedMaximalIdeal A S = J n := rfl
    rw [hext, hFiber n, length_baseChange_quotient_eq (φ n) (mA ^ (t + 1)),
      Ideal.map_pow] at hb
    exact hb
  obtain ⟨δ, hδ⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := A))
  have hδne : δ ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := A)
    calc
      ringKrullDim A = (δ : WithBot ℕ∞) := hδ.symm
      _ = ⊤ := by rw [h]; simp
  obtain ⟨d, hden⟩ := WithTop.ne_top_iff_exists.mp hδne
  have hd : ((d : ℕ∞) : WithBot ℕ∞) = ringKrullDim A :=
    (congrArg (fun z : ℕ∞ ↦ (z : WithBot ℕ∞)) hden).trans hδ
  have hPdegree : P.degree = (d : WithBot ℕ) := by
    apply WithBot.map_injective (fun a b h ↦ WithTop.coe_injective h)
    change WithBot.map (Nat.cast : ℕ → ℕ∞) P.degree =
      WithBot.map (Nat.cast : ℕ → ℕ∞) (d : WithBot ℕ)
    rw [← hdegP, Module.hilbertSamuelDegree_eq_supportDim A A,
      Module.supportDim_self_eq_ringKrullDim, hd.symm]
    simp
  have hPne : P ≠ 0 := by
    intro h
    simp [h] at hPdegree
  have hPnonneg : ∀ᶠ k : ℕ in Filter.atTop, 0 ≤ P.eval (k : ℚ) := by
    filter_upwards [hP] with k hk
    obtain ⟨z, _, heq⟩ := hk
    rw [heq]
    positivity
  have hPlc0 := HilbertSamuel.nonneg_leadingCoeff_of_eventually_nonneg P hPnonneg
  have hPlcne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hPlcpos : 0 < P.leadingCoeff := lt_of_le_of_ne hPlc0 hPlcne.symm
  by_cases hr0 : r = 0
  · apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hsCard]
    have hs0 : s.card = 0 := by simpa [r] using hr0
    rw [hs0]
    exact (zero_le_ringKrullDim_iff_nontrivial).2 inferInstance
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hbound (n : ℕ) : q n ^ r ≤ (r * q n) ^ d := by
    obtain ⟨Q, hQ, hQdeg⟩ := hdegQ n
    let c : ℕ := q n ^ r
    let k : ℕ := r * q n
    have hkpos : 0 < k := Nat.mul_pos hrpos (Nat.pow_pos hp.pos)
    have hcontain (t : ℕ) : mS ^ (r * (q n * t) + 1) ≤ (J n) ^ t := by
      rw [← hyspan]
      apply pow_span_fin_le_of_powers_mem r (q n * t) y ((J n) ^ t)
      intro i
      simpa only [pow_mul] using (Ideal.pow_mem_pow (hgen n i) t)
    have hquotLe (t : ℕ) :
        Module.length S (S ⧸ ((J n) ^ t)) ≤
          Module.length S (S ⧸ (mS ^ (r * (q n * t) + 1))) := by
      rw [Module.length_quotient, Module.length_quotient]
      exact Order.coheight_anti (hcontain t)
    have hpolyEq : Q = Polynomial.C (c : ℚ) * P := by
      apply Polynomial.eq_of_eventually_eval_natCast_eq
      filter_upwards [eventually_length_quotient_pow_eq hP,
        eventually_length_quotient_pow_eq hQ] with t hpt hqt
      obtain ⟨a, ha, hpa⟩ := hpt
      obtain ⟨b, hb, hqb⟩ := hqt
      have hscale' := hscale n t
      rw [ha, hb] at hscale'
      have hab : a * c = b := by exact_mod_cast hscale'
      have hrat : (b : ℚ) = (c : ℚ) * (a : ℚ) := by
        exact_mod_cast (by simpa [Nat.mul_comm] using hab.symm)
      rw [Polynomial.eval_mul, Polynomial.eval_C, hqb, hpa]
      exact hrat
    let T : ℚ[X] := Polynomial.C (k : ℚ) * Polynomial.X + Polynomial.C (k : ℚ)
    have hT_eq : T = Polynomial.C (k : ℚ) *
        (Polynomial.X + Polynomial.C (1 : ℚ)) := by
      simp only [T, Polynomial.C_1]
      ring
    have hTk : T.degree = 1 := by
      rw [hT_eq, Polynomial.degree_mul, Polynomial.degree_C (by exact_mod_cast hkpos.ne'),
        Polynomial.degree_X_add_C]
      norm_num
    have hTlc : T.leadingCoeff = (k : ℚ) := by
      rw [hT_eq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        Polynomial.leadingCoeff_X_add_C]
      ring
    have hTnd : T.natDegree = 1 := by
      have hTne : T ≠ 0 := by
        intro hz
        rw [hz] at hTk
        simp at hTk
      exact WithBot.coe_injective <|
        (Polynomial.degree_eq_natDegree hTne).symm.trans hTk
    have hPcompDeg : (P.comp T).degree = P.degree := by
      rw [Polynomial.degree_comp (by rw [hTk]; norm_num), hTk, mul_one]
    have hPcompLc : (P.comp T).leadingCoeff =
        P.leadingCoeff * (k : ℚ) ^ P.natDegree := by
      rw [Polynomial.leadingCoeff_comp (by rw [hTnd]; norm_num), hTlc]
    have hcomp : ∀ᶠ z : ℕ in Filter.atTop,
        Q.eval (z : ℚ) ≤ (P.comp T).eval (z : ℚ) := by
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_length_quotient_pow_eq hP)
      filter_upwards [eventually_length_quotient_pow_eq hQ,
        Filter.eventually_atTop.2 ⟨N, fun z hz ↦ hz⟩] with z hqz hz
      obtain ⟨b, hb, hbq⟩ := hqz
      have hK : N ≤ k * z + k := by
        calc
          N ≤ z := hz
          _ ≤ z + 1 := Nat.le_succ z
          _ ≤ k * (z + 1) := by
            calc
              z + 1 = 1 * (z + 1) := by simp
              _ ≤ k * (z + 1) := Nat.mul_le_mul_right (z + 1) (by omega)
          _ = k * z + k := by ring
      obtain ⟨a, ha, hpa⟩ := hN (k * z + k) hK
      have hlenMax : Module.length S (S ⧸ (mS ^ (k * z + k + 1))) = a := by
        calc
          Module.length S (S ⧸ (mS ^ (k * z + k + 1))) =
              Module.length A (A ⧸ (mA ^ (k * z + k + 1))) :=
            (hlenEquiv (k * z + k + 1)).symm
          _ = a := ha
      have hle := hquotLe (z + 1)
      have hexp : r * (q n * (z + 1)) + 1 = k * z + k + 1 := by
        dsimp [k]
        ring
      have hle' : (b : ℕ∞) ≤ (a : ℕ∞) := by
        calc
          (b : ℕ∞) = Module.length S (S ⧸ ((J n) ^ (z + 1))) := hb.symm
          _ ≤ Module.length S (S ⧸ (mS ^ (r * (q n * (z + 1)) + 1))) := hle
          _ = Module.length S (S ⧸ (mS ^ (k * z + k + 1))) := by rw [hexp]
          _ = (a : ℕ∞) := hlenMax
      have hrat : (b : ℚ) ≤ (a : ℚ) := by exact_mod_cast hle'
      have harg : ((k * z + k : ℕ) : ℚ) = Polynomial.eval (z : ℚ) T := by
        simp [T, Polynomial.eval_add, Polynomial.eval_mul]
      rw [Polynomial.eval_comp, harg.symm, hpa, hbq]
      exact hrat
    have hcompdeg : Q.degree = (P.comp T).degree := by
      rw [hQdeg, hPcompDeg]
    have hcompnonneg : 0 ≤ Q.degree := by
      rw [hQdeg, hPdegree]
      exact_mod_cast Nat.zero_le d
    have hLC := leadingCoeff_le_of_eventually_eval_le hcomp hcompdeg hcompnonneg
    have hqnpos : 0 < q n := by dsimp [q]; exact Nat.pow_pos hp.pos
    have hcpos : 0 < c := by dsimp [c]; exact Nat.pow_pos hqnpos
    have hcoeff : Q.leadingCoeff = (c : ℚ) * P.leadingCoeff := by
      rw [hpolyEq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have hnatP : P.natDegree = d :=
      WithBot.coe_injective ((Polynomial.degree_eq_natDegree hPne).symm.trans hPdegree)
    have hmul : (c : ℚ) * P.leadingCoeff ≤ P.leadingCoeff * (k : ℚ) ^ d := by
      simpa [hcoeff, hPcompLc, hnatP] using hLC
    have hrat : (c : ℚ) ≤ (k : ℚ) ^ d :=
      (mul_le_mul_iff_left₀ hPlcpos).mp (by simpa [mul_comm] using hmul)
    exact_mod_cast hrat
  have hdimBound : r ≤ d := by
    by_contra hrd
    have hrd' : d < r := by omega
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (r ^ d : ℝ)
      (by exact_mod_cast hp.one_lt : (1 : ℝ) < (p : ℝ))
    have hpowN : r ^ d < p ^ N := by exact_mod_cast hN
    have hqle : (q N) ^ (r - d) ≤ r ^ d := by
      have hmul : (q N) ^ d * (q N) ^ (r - d) ≤ r ^ d * (q N) ^ d := by
        calc
          (q N) ^ d * (q N) ^ (r - d) = (q N) ^ r := by
            rw [← pow_add]
            rw [show d + (r - d) = r by omega]
          _ ≤ (r * q N) ^ d := hbound N
          _ = r ^ d * (q N) ^ d := Nat.mul_pow _ _ _
      have hqpos : 0 < q N := by dsimp [q]; exact Nat.pow_pos hp.pos
      have hmul' : (q N) ^ d * (q N) ^ (r - d) ≤
          (q N) ^ d * r ^ d := by simpa [Nat.mul_comm] using hmul
      exact Nat.le_of_mul_le_mul_left hmul' (Nat.pow_pos hqpos)
    have hqge : p ^ N ≤ (q N) ^ (r - d) := by
      change p ^ N ≤ (p ^ N) ^ (r - d)
      calc
        p ^ N = (p ^ N) ^ 1 := (pow_one _).symm
        _ ≤ (p ^ N) ^ (r - d) := by
          apply pow_le_pow_right₀
          · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
          · omega
    omega
  have hfr : (IsLocalRing.maximalIdeal A).spanFinrank ≤ ringKrullDim A := by
    rw [← hsCard, ← hd]
    exact_mod_cast hdimBound
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A hfr

/-- A Frobenius map out of a regular local ring is flat. The target is viewed through an
equivalent copy of the source so that the source action and the target's regular-module action
remain distinct. -/
private lemma frobeniusOfPrime_flat_of_isRegularLocalRing {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) :
    RingHom.Flat (frobeniusOfPrime p hp hchar) := by
  let e : ULift.{u, u} A ≃+* A := ULift.ringEquiv
  let g : ULift.{u, u} A →+* A :=
    (frobeniusOfPrime p hp hchar).comp e.toRingHom
  let : IsRegularLocalRing (ULift A) := IsRegularLocalRing.of_ringEquiv e.symm
  let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let : IsLocalHom (frobeniusOfPrime p hp hchar) :=
    frobeniusOfPrime_isLocalHom p hp hchar
  have : IsLocalHom g := RingHom.isLocalHom_comp _ _
  let : Algebra (ULift A) A := g.toAlgebra
  have hmaple : (IsLocalRing.maximalIdeal (ULift A)).map g ≤
      IsLocalRing.maximalIdeal A := IsLocalRing.map_maximalIdeal_le g
  have hmaple_rad : IsLocalRing.maximalIdeal A ≤
      ((IsLocalRing.maximalIdeal (ULift A)).map g).radical := by
    intro x hx
    rw [Ideal.mem_radical_iff]
    refine ⟨p, ?_⟩
    have hx' : ULift.up x ∈ IsLocalRing.maximalIdeal (ULift.{u, u} A) := by
      rw [IsLocalRing.mem_maximalIdeal]
      apply (mem_nonunits_iff).2
      intro hunit
      have hxunit : IsUnit x := hunit.map e.toMonoidHom
      exact (IsLocalRing.notMem_maximalIdeal).mpr hxunit hx
    have hmem := Ideal.mem_map_of_mem g hx'
    have hvalue : g (ULift.up x) = x ^ p := by
      simp [g, frobeniusOfPrime_apply, e, ULift.ringEquiv]
    rw [hvalue] at hmem
    exact hmem
  have hrad : ((IsLocalRing.maximalIdeal (ULift A)).map g).radical =
      IsLocalRing.maximalIdeal A :=
    le_antisymm
      ((IsLocalRing.maximalIdeal.isMaximal A).isPrime.isRadical.radical_le_iff.mpr hmaple)
      hmaple_rad
  have hproper : (IsLocalRing.maximalIdeal (ULift A)).map g ≠ ⊤ :=
    (IsLocalRing.map_maximalIdeal_lt_top g).ne
  have hdimfiber : ringKrullDim (A ⧸ (IsLocalRing.maximalIdeal (ULift A)).map g) = 0 :=
    dim_quotient_eq_zero_of_radical_maximalIdeal hrad hproper
  have hdim : ringKrullDim A = ringKrullDim (ULift A) +
      ringKrullDim (A ⧸ (IsLocalRing.maximalIdeal (ULift A)).map g) := by
    rw [hdimfiber, add_zero, ringKrullDim_eq_of_ringEquiv e.symm]
  have hcm : Module.IsMaximalCohenMacaulay A A :=
    IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay A |>.2
  have hg : RingHom.Flat g :=
    Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hcm hdim
  have heq : g.comp e.symm.toRingHom = frobeniusOfPrime p hp hchar := by
    ext x
    simp [g, e]
  rw [← heq]
  exact (RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective).comp hg

/-- A prime ideal is its own preimage under the Frobenius endomorphism. -/
private lemma comap_frobeniusOfPrime_eq {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hchar : (p : A) = 0) (P : Ideal A) [P.IsPrime] :
    Ideal.comap (frobeniusOfPrime p hp hchar) P = P := by
  ext x
  simp only [Ideal.mem_comap, frobeniusOfPrime_apply]
  exact Ideal.IsPrime.pow_mem_iff_mem (I := P) inferInstance p hp.pos

/-- The localization of the Frobenius endomorphism at a prime is the Frobenius endomorphism of
the localization. -/
private lemma localization_frobenius_eq {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hchar : (p : A) = 0) (P : Ideal A) [P.IsPrime]
    (hcomap : P = Ideal.comap (frobeniusOfPrime p hp hchar) P) :
    Localization.localRingHom P P (frobeniusOfPrime p hp hchar) hcomap =
      frobeniusOfPrime p hp (by
        have hz := congrArg (algebraMap A (Localization.AtPrime P)) hchar
        simpa using hz) := by
  apply IsLocalization.ringHom_ext P.primeCompl
  ext x
  simp [Localization.localRingHom_to_map, frobeniusOfPrime_apply]

/-- The Frobenius endomorphism of a regular ring is flat. -/
private lemma frobeniusOfPrime_flat_of_isRegularRing {A : Type*} [CommRing A]
    [IsRegularRing A] (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) :
    RingHom.Flat (frobeniusOfPrime p hp hchar) := by
  apply RingHom.Flat.ofLocalizationPrime
  intro P hP
  let : P.IsPrime := hP
  let Q : Ideal A := Ideal.comap (frobeniusOfPrime p hp hchar) P
  let : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q = P := comap_frobeniusOfPrime_eq p hp hchar P
  let qQ := Localization.AtPrime Q
  let qP := Localization.AtPrime P
  have hmap : Submonoid.map (RingEquiv.refl A).toMonoidHom Q.primeCompl = P.primeCompl := by
    ext x
    simp [hQP]
  let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime Q) (Localization.AtPrime P)
      (RingEquiv.refl A) hmap
  let φ : qQ →+* qP := Localization.localRingHom Q P
    (frobeniusOfPrime p hp hchar) (by rfl)
  have hcharP : (p : qP) = 0 := by simpa using congrArg (algebraMap A qP) hchar
  let F : qP →+* qP := frobeniusOfPrime p hp hcharP
  have heq : φ = F.comp eLoc.toRingHom := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    ext x
    change (Localization.localRingHom Q P (frobeniusOfPrime p hp hchar) (by rfl))
        (algebraMap A qQ x) = F (eLoc (algebraMap A qQ x))
    rw [Localization.localRingHom_to_map]
    rw [show eLoc (algebraMap A qQ x) = algebraMap A qP x by
      exact IsLocalization.ringEquivOfRingEquiv_eq (S := qQ) (Q := qP) hmap x]
    simp [F, qP, frobeniusOfPrime_apply]
  change RingHom.Flat φ
  rw [heq]
  exact (RingHom.Flat.of_bijective (f := eLoc.toRingHom) eLoc.bijective).comp
    (frobeniusOfPrime_flat_of_isRegularLocalRing p hp hcharP)

/-- **Kunz's theorem.** If a prime number vanishes in a Noetherian ring, the ring is regular if
and only if its Frobenius endomorphism is flat. -/
@[stacks 0EC0]
lemma isRegularRing_iff_frobeniusOfPrime_flat {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) :
    IsRegularRing A ↔ RingHom.Flat (frobeniusOfPrime p hp hchar) := by
  refine ⟨fun _ ↦ frobeniusOfPrime_flat_of_isRegularRing p hp hchar, fun hflat ↦ ?_⟩
  rw [isRegularRing_iff]
  intro P hP
  let : P.IsPrime := hP
  have hcomap : P = Ideal.comap (frobeniusOfPrime p hp hchar) P :=
    (comap_frobeniusOfPrime_eq p hp hchar P).symm
  have hloc :
      (Localization.localRingHom P P (frobeniusOfPrime p hp hchar) hcomap).Flat :=
    RingHom.Flat.localRingHom hflat P P hcomap
  rw [localization_frobenius_eq p hp hchar P hcomap] at hloc
  exact isRegularLocalRing_of_frobeniusOfPrime_flat p hp _ hloc
