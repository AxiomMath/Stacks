module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.PoleReduction

/-!
# Eliminating degree-prime ramification: Laurent coefficients and the constant numerator

Uniformizers under weakly unramified extensions, the Artin--Schreier extension adjoining a root of
`X ^ p - X - π ^ (-n) a`, constant numerators from coefficient lifts, the
trivial/unramified/totally ramified trichotomy for a minimal numerator, and elements outside the
perfect core.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- **A uniformizer remains a uniformizer under a weakly unramified DVR extension.**

Public because the iteration that discharges the antecedent of
`exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport` needs it: that
antecedent is supplied by a weakly unramified base change
(`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`), and the
  layer's
finite set and depth are built from an Artin--Schreier presentation over a uniformizer of the
base, so closing the loop requires knowing the uniformizer — and hence the presentation — is
unchanged by that base change. -/
theorem irreducible_algebraMap_of_isWeaklyUnramified
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (hweak : IsWeaklyUnramified A B) {π : A} (hπ : Irreducible π) :
    Irreducible (algebraMap A B π) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  have h := (ramificationIndex_characterization A B).2.1
  rw [show ramificationIndex A B = 1 from hweak, pow_one,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.map_span, Set.image_singleton] at h
  exact h.symm

/-- Let `π` be a uniformizer of `A`, let `a ∈ A` be a unit and let `n > 0` be prime to `p`. Then
there is a finite Galois extension `K₁ = K(w)` of `K`, totally ramified with respect to `A`, where
`w ^ p - w = π⁻¹ ^ n * a`. -/
theorem exists_isGalois_totallyRamified_artinSchreier
    (A : Type uA) (K : Type uK) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (π : A) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hpn : ¬p ∣ n)
    (a : A) (ha : IsUnit a) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧
      ∃ w : K₁, w ^ p - w = algebraMap K K₁ ((algebraMap A K π)⁻¹ ^ n * algebraMap A K a) ∧
        Algebra.adjoin K {w} = ⊤ := by
  let ξ := (algebraMap A K π)⁻¹ ^ n * algebraMap A K a
  let f : K[X] := X ^ p - (X + C ξ)
  have hf : 0 < f.natDegree := by
    have hdeg : f.degree = p := by
      dsimp [f]
      rw [degree_sub_eq_left_of_degree_lt, degree_X_pow]
      rw [degree_X_add_C, degree_X_pow]
      exact_mod_cast hp.one_lt
    rw [natDegree_eq_of_degree_eq_some hdeg]
    exact hp.pos
  obtain ⟨g, hg, hgf⟩ := exists_irreducible_of_natDegree_pos hf
  let : Fact (Irreducible g) := ⟨hg⟩
  let K₁ := AdjoinRoot g
  let w : K₁ := AdjoinRoot.root g
  have hw : w ^ p - w = algebraMap K K₁ ξ := by
    have he : aeval w f = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hgf (by
      change aeval (AdjoinRoot.root g) g = 0
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    simp only [f, map_sub, map_pow, aeval_X, map_add, aeval_C] at he
    linear_combination he
  have hgen : Algebra.adjoin K {w} = ⊤ := AdjoinRoot.adjoinRoot_eq_top
  obtain ⟨hfin, hgal, -, -, htot, -⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier
      A K K₁ p hp ξ w hw hgen π hπ
  exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, hfin, hgal,
    (htot n a hn hpn ha rfl).1, w, hw, hgen⟩



/-- If the coefficients of a finite expansion lift from the base modulo the pole bound, then its
Laurent principal part has a numerator in the base DVR — and that numerator is the *visible* sum
`∑ i < n, lift i * π ^ i` of the supplied lifts.

The lifts are arguments rather than existential witnesses so that the numerator is a term the
caller can compute with.  What a caller needs from it is its residue, which by
`residue_sum_mul_uniformizer_pow` is the residue of `lift 0` alone; that is what turns knowledge
about the zeroth coefficient into a `p`-th root of the numerator's residue.
`exists_constant_numerator_of_coefficients_lift` is the existential wrapper. -/
theorem eq_constant_numerator_of_coefficients_lift
    {A B L : Type*} [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (π : A) (ht : algebraMap A L π ≠ 0) (n : ℕ)
    (coeff : ℕ → B) (b : B) (ξ : L) (lift : ℕ → A)
    (hexp : algebraMap A L π ^ n * ξ =
      algebraMap B L ((∑ i ∈ Finset.range n, coeff i * algebraMap A B π ^ i) +
        algebraMap A B π ^ n * b))
    (hlift : ∀ i ∈ Finset.range n,
      coeff i - algebraMap A B (lift i) ∈ Ideal.span {algebraMap A B π ^ n}) :
    ∃ b' : B, ξ = (algebraMap A L π)⁻¹ ^ n *
      algebraMap A L (∑ i ∈ Finset.range n, lift i * π ^ i) + algebraMap B L b' := by
  classical
  have hc : ∀ i ∈ Finset.range n, ∃ c : B,
      coeff i = algebraMap A B (lift i) + algebraMap A B π ^ n * c := fun i hi => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hlift i hi)
    exact ⟨c, by linear_combination hc⟩
  choose! c hc using hc
  refine ⟨(∑ i ∈ Finset.range n, c i * algebraMap A B π ^ i) + b, ?_⟩
  apply (mul_left_cancel₀ (pow_ne_zero n ht))
  rw [hexp]
  simp only [map_add, map_sum, map_mul, map_pow, mul_add, Finset.mul_sum,
    ← IsScalarTower.algebraMap_apply]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi]
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  have hcancel : algebraMap A L π ^ n * (algebraMap A L π)⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
  linear_combination -(algebraMap A L (lift i) * algebraMap A L π ^ i) * hcancel


/-- The residue of `∑ i < n, f i * π ^ i` is the residue of its constant term, since every later
term carries a factor of the uniformizer. -/
theorem residue_sum_mul_uniformizer_pow {A : Type*} [CommRing A] [IsLocalRing A]
    {π : A} (hπ : π ∈ IsLocalRing.maximalIdeal A) (n : ℕ) (hn : 0 < n) (f : ℕ → A) :
    IsLocalRing.residue A (∑ i ∈ Finset.range n, f i * π ^ i) =
      IsLocalRing.residue A (f 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmem : (∑ i ∈ Finset.range m, f (i + 1) * π ^ (i + 1)) ∈
      IsLocalRing.maximalIdeal A :=
    Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπ (i + 1) (by omega))
  rw [Finset.sum_range_succ', pow_zero, mul_one, map_add,
    (IsLocalRing.residue_eq_zero_iff _).mpr hmem, zero_add]

/-- If the coefficients of a finite expansion lift from the base modulo the pole bound,
then its Laurent principal part has a numerator in the base DVR. -/
theorem exists_constant_numerator_of_coefficients_lift
    {A B L : Type*} [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (π : A) (ht : algebraMap A L π ≠ 0) (n : ℕ)
    (coeff : ℕ → B) (b : B) (ξ : L)
    (hexp : algebraMap A L π ^ n * ξ =
      algebraMap B L ((∑ i ∈ Finset.range n, coeff i * algebraMap A B π ^ i) +
        algebraMap A B π ^ n * b))
    (hcoeff : ∀ i ∈ Finset.range n, ∃ a : A,
      coeff i - algebraMap A B a ∈ Ideal.span {algebraMap A B π ^ n}) :
    ∃ (a : A) (b' : B),
      ξ = (algebraMap A L π)⁻¹ ^ n * algebraMap A L a + algebraMap B L b' := by
  classical
  choose! lift hlift using hcoeff
  obtain ⟨b', hb'⟩ := eq_constant_numerator_of_coefficients_lift π ht n coeff b ξ lift hexp hlift
  exact ⟨_, b', hb'⟩

/-- The numerator of a positive minimal pole is a unit. -/
theorem isUnit_of_minimal_poleOrder
    {A B L M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field L] [Field M]
    [Algebra A B] [Algebra A L] [Algebra B L] [Algebra L M]
    [IsScalarTower A B L]
    (π : A) (hπ : Irreducible π) (ht : algebraMap A L π ≠ 0)
    (n : ℕ) (hn : 0 < n) (a : A) (b : B) (ξ : L) (z : M) (p : ℕ)
    (hz : z ^ p - z = algebraMap L M ξ) (hgen : Algebra.adjoin L {z} = ⊤)
    (hξ : ξ = (algebraMap A L π)⁻¹ ^ n * algebraMap A L a + algebraMap B L b)
    (hmin : ∀ (m : ℕ) (η : L) (w : M),
      w ^ p - w = algebraMap L M η → Algebra.adjoin L {w} = ⊤ →
      algebraMap A L π ^ m * η ∈ (algebraMap B L).range → n ≤ m) : IsUnit a := by
  by_contra ha
  have ha' : a ∈ IsLocalRing.maximalIdeal A := ha
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.mem_span_singleton] at ha'
  obtain ⟨a₁, rfl⟩ := ha'
  have hpole : algebraMap A L π ^ (n - 1) * ξ ∈ (algebraMap B L).range := by
    refine ⟨algebraMap A B a₁ + algebraMap A B π ^ (n - 1) * b, ?_⟩
    rw [hξ]
    simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    have hpow : algebraMap A L π ^ n = algebraMap A L π ^ (n - 1) * algebraMap A L π := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [inv_pow, hpow]
    field_simp
  exact (Nat.not_le_of_lt (Nat.sub_lt hn Nat.zero_lt_one)) (hmin _ ξ z hz hgen hpole)

/-- **A positive pole order prime to `p` with a unit numerator gives the three non-fierce cases.**

This is `artinSchreier_trivial_or_unramified_or_totallyRamified_of_minimal_numerator_root` with its
minimality hypothesis replaced by the two consequences that proof actually uses: that `p` does not
divide the pole order, and that the numerator is a unit. Nothing else about minimality enters, so
this is the more general statement and the minimal version is derived from it below.

The generalization is what makes the pole-reduction induction usable. Minimality quantifies over
*all* competing generators of the extension, and the reduction does not produce it — worse, it
cannot be expected to, since an `F_p`-combination of individually minimal Artin--Schreier
parameters need not be minimal. `Stacks.EppTheorem.exists_terminal_of_frobeniusNumerator` instead
terminates with exactly the pair of facts asked for here: a unit numerator and a pole order prime
to `p`. That is a weaker conclusion than minimality and, as this theorem shows, sufficient. -/
theorem artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (ξ : K) (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (π : A) (hπ : Irreducible π) (n : ℕ) (a b : A)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a + algebraMap A K b)
    (hn : 0 < n) (hpn : ¬p ∣ n) (ha : IsUnit a) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      trivial ∨ unramified ∨ totallyRamified := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hfin, -, -, -, hpole, -⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier
      A K L p hp ξ z hz hgen π hπ
  refine ⟨hfin, ?_⟩
  have := hfin
  have ht : algebraMap A K π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
  have hab : IsUnit (a + π ^ n * b) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have hzero : IsLocalRing.residue A π = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hπ.not_isUnit
    simpa only [map_add, map_mul, map_pow, hzero, zero_pow hn.ne', zero_mul, add_zero] using
      (IsLocalRing.residue_ne_zero_iff_isUnit a).mpr ha
  have hξ' : ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K (a + π ^ n * b) := by
    rw [hξ, map_add, map_mul, map_pow, inv_pow]
    field_simp [ht]
  exact Or.inr (Or.inr (hpole n (a + π ^ n * b) hn hpn hab hξ'))

/-- A minimal Artin--Schreier parameter whose constant numerator has a `p`-th root in the
residue field cannot give the residually inseparable case of Tag 09F0.

The conclusion deliberately retains the other three possibilities: the extension is trivial,
unramified with separable residue extension, or totally ramified.  For a zero pole the parameter
is integral, while for a positive pole the supplied root rules out divisibility of the minimal
pole order by `p`; minimality also makes the numerator a unit. -/
theorem artinSchreier_trivial_or_unramified_or_totallyRamified_of_minimal_numerator_root
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (ξ : K) (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (π : A) (hπ : Irreducible π) (n : ℕ) (a b : A)
    (hξ : ξ = (algebraMap A K π)⁻¹ ^ n * algebraMap A K a + algebraMap A K b)
    (hmin : ∀ (m : ℕ) (η : K) (w : L),
      w ^ p - w = algebraMap K L η → Algebra.adjoin K {w} = ⊤ →
      algebraMap A K π ^ m * η ∈ (algebraMap A K).range → n ≤ m)
    (c : IsLocalRing.ResidueField A) (hc : c ^ p = IsLocalRing.residue A a) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      trivial ∨ unramified ∨ totallyRamified := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hn0 : n = 0
  · obtain ⟨hfin, -, -, hintegral, -, -⟩ :=
      isGalois_and_ramification_cases_of_adjoin_root_artinSchreier
        A K L p hp ξ z hz hgen π hπ
    refine ⟨hfin, ?_⟩
    have := hfin
    have hξint : ∃ q : A, ξ = algebraMap A K q := by
      refine ⟨a + b, ?_⟩
      simpa only [hn0, pow_zero, inv_one, one_mul, map_add] using hξ
    exact (hintegral hξint).elim Or.inl (fun h => Or.inr (Or.inl h))
  · -- For a positive pole, minimality is consumed only to supply the two hypotheses of
    -- `artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator`.
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have ht : algebraMap A K π ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
    exact artinSchreier_trivial_or_unramified_or_totallyRamified_of_unit_numerator
      A K L p hp ξ z hz hgen π hπ n a b hξ hn
      (not_dvd_poleOrder_of_constant_numerator_of_root p π hπ ht n hn a b ξ z c hc
        hz hgen hξ hmin)
      (isUnit_of_minimal_poleOrder π hπ ht n hn a b ξ z p hz hgen hξ hmin)

/-- Deep roots of the finitely many Laurent coefficients exclude the residually inseparable
Artin--Schreier case.

The coefficient section is required only modulo the pole bound.  If every coefficient has a
`p ^ n`-th root in the residue field, the Laurent principal part can be rewritten with one
constant numerator whose residue visibly has a `p`-th root.  The preceding minimal-numerator
criterion then gives exactly the three non-fierce alternatives from Tag 09F0. -/
theorem artinSchreier_trivial_or_unramified_or_totallyRamified_of_laurent_coefficient_roots
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (ξ : K) (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : Algebra.adjoin K {z} = ⊤)
    (π : A) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n)
    (hmin : ∀ (m : ℕ) (η : K) (w : L),
      w ^ p - w = algebraMap K L η → Algebra.adjoin K {w} = ⊤ →
      algebraMap A K π ^ m * η ∈ (algebraMap A K).range → n ≤ m)
    (σ : IsLocalRing.ResidueField A → A)
    (hσ : ∀ x, IsLocalRing.residue A (σ x) = x)
    (s : IsLocalRing.ResidueField A →+* A ⧸ (IsLocalRing.maximalIdeal A) ^ n)
    (hs : ∀ x, Ideal.Quotient.mk _ (σ x) = s x)
    (coeff : ℕ → IsLocalRing.ResidueField A) (b : A)
    (hexp : ξ = (∑ i ∈ Finset.range n,
      algebraMap A K (σ (coeff i)) * (algebraMap A K π)⁻¹ ^ (n - i)) +
        algebraMap A K b)
    (hroot : ∀ i ∈ Finset.range n,
      ∃ r : IsLocalRing.ResidueField A, r ^ (p ^ n) = coeff i) :
    ∃ hfin : Module.Finite K L,
      letI := hfin
      let B := integralClosure A L
      let mA := IsLocalRing.maximalIdeal A
      let trivial : Prop := Function.Surjective (algebraMap K L)
      let unramified : Prop :=
        Module.finrank K L = p ∧
          ∀ m : Ideal B, m.IsMaximal → ∃ _ : m.LiesOver mA,
            Ideal.ramificationIdx' mA m = 1 ∧
              @Algebra.IsSeparable (A ⧸ mA) (B ⧸ m) _ _
                (Ideal.Quotient.algebraOfLiesOver m mA)
      let totallyRamified : Prop :=
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
          ∀ m : Ideal B, m.IsMaximal → m.LiesOver mA →
            Ideal.ramificationIdx' mA m = p
      trivial ∨ unramified ∨ totallyRamified := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcharA : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  have : CharP A p := hcharA
  have ht : algebraMap A K π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
  have hI : (IsLocalRing.maximalIdeal A) ^ n ≤ Ideal.span {π ^ n} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_pow]
  choose! root hroot' using hroot
  have hlifts : ∀ i ∈ Finset.range n, ∃ l : A,
      σ (coeff i) - l ∈ (IsLocalRing.maximalIdeal A) ^ n := by
    intro i hi
    obtain ⟨l, hl⟩ := IsLocalRing.residue_surjective (root i)
    have hd : σ (root i) - l ∈ IsLocalRing.maximalIdeal A := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, hσ, hl, sub_self]
    have hle : n ≤ p ^ n :=
      (Nat.le_of_lt Nat.lt_two_pow_self).trans
        (Nat.pow_le_pow_left (Fact.out : p.Prime).two_le n)
    have hdN := (Ideal.pow_le_pow_right hle) (Ideal.pow_mem_pow hd (p ^ n))
    rw [sub_pow_char_pow] at hdN
    refine ⟨l ^ (p ^ n), ?_⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_sub, map_pow, hs, ← hroot' i hi] using
      Ideal.Quotient.eq_zero_iff_mem.mpr hdN
  choose! lift hlift using hlifts
  have hexp' : algebraMap A K π ^ n * ξ =
      algebraMap A K ((∑ i ∈ Finset.range n, σ (coeff i) * π ^ i) + π ^ n * b) := by
    rw [hexp, mul_add, Finset.mul_sum, map_add, map_sum, map_mul, map_pow]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, map_pow, inv_pow_sub₀ ht (Nat.le_of_lt (Finset.mem_range.mp hi))]
    field_simp
  obtain ⟨b', hξ'⟩ := eq_constant_numerator_of_coefficients_lift π ht n
    (fun i => σ (coeff i)) b ξ lift hexp' fun i hi => hI (hlift i hi)
  let a : A := ∑ i ∈ Finset.range n, lift i * π ^ i
  have hπm : π ∈ IsLocalRing.maximalIdeal A :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸
      Ideal.mem_span_singleton_self π
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hres : IsLocalRing.residue A a = root 0 ^ (p ^ n) := by
    rw [show a = ∑ i ∈ Finset.range n, lift i * π ^ i from rfl,
      residue_sum_mul_uniformizer_pow hπm n hn lift]
    have hmem : σ (coeff 0) - lift 0 ∈ IsLocalRing.maximalIdeal A :=
      Ideal.pow_le_self (Nat.ne_of_gt hn) (hlift 0 h0)
    have heq : IsLocalRing.residue A (lift 0) = IsLocalRing.residue A (σ (coeff 0)) := by
      rw [eq_comm, ← sub_eq_zero, ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [heq, hσ, hroot' 0 h0]
  apply artinSchreier_trivial_or_unramified_or_totallyRamified_of_minimal_numerator_root
    A K L p hp ξ z hz hgen π hπ n a b' hξ' hmin
    (root 0 ^ (p ^ (n - 1)))
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, hres]

/-- **An element outside the image has a finite Frobenius depth.**

If every element of `K` admitting `p ^ n`-th roots for all `n ≥ 1` — that is, every element of
`perfectCore K p` — already lies in the image of `k`, then an element `x` outside that image has a
largest stage at which it is a `p`-power: there are `r` and `y` with `y ^ (p ^ r) = x` and `y` not
itself a `p`-th power.

This is Kuhlmann's `ν_x`, and it is the *only* thing Tag 09F1's residue hypothesis is used for
where that hypothesis is applied to individual elements.  Stating it with the one implication it
needs, rather than with the `↔` of hypothesis (4), separates the substance of that hypothesis from
a triviality: the other inclusion, `image ⊆ perfectCore`, says no more than that `κ_A` is perfect
(if Frobenius is onto `κ_A` then every element of the image has `p ^ n`-th roots in the image for
every `n`, and conversely that is all `perfectRing_of_range_eq_iInf_pow` extracts).  The inclusion
used here, `perfectCore ⊆ image`, is the whole content.

Taken against the perfect core *itself* rather than against the image of `k`, the same finiteness
needs no hypothesis at all; that is the public
`exists_pow_eq_and_not_pow_of_notMem_perfectCore` of `StacksFrontier.FieldTheory.PerfectCore`, and it
is what the degree-`p` argument below actually uses.

`exists_pow_eq_and_not_pow_of_not_range` is the `↔` form, kept because Tag 09F1 states it that
way. -/
theorem exists_pow_eq_and_not_pow_of_perfectCore_le
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (h : ∀ x : K, (∀ n : ℕ, 1 ≤ n → ∃ y : K, y ^ (p ^ n) = x) →
      ∃ a : k, algebraMap k K a = x)
    (x : K) (hx : ¬∃ a : k, algebraMap k K a = x) :
    ∃ (r : ℕ) (y : K), y ^ (p ^ r) = x ∧ ¬∃ z : K, z ^ p = y := by
  classical
  have H : ∃ n : ℕ, ¬∃ y : K, y ^ (p ^ n) = x := by
    by_contra! H
    exact hx (h x fun n _ => H n)
  let n := Nat.find H
  have hn : ¬∃ y : K, y ^ (p ^ n) = x := Nat.find_spec H
  have hpos : 0 < n := by
    by_contra hn0
    have : n = 0 := by omega
    exact hn ⟨x, by simp [this]⟩
  have hroot : ∃ y : K, y ^ (p ^ (n - 1)) = x := by
    by_contra hy
    have := Nat.find_min H (Nat.sub_lt hpos Nat.zero_lt_one)
    exact this hy
  obtain ⟨y, hy⟩ := hroot
  refine ⟨n - 1, y, hy, ?_⟩
  rintro ⟨z, rfl⟩
  apply hn
  refine ⟨z, ?_⟩
  rw [← pow_mul, ← pow_succ'] at hy
  simpa only [Nat.sub_add_cancel hpos] using hy

/-- `exists_pow_eq_and_not_pow_of_perfectCore_le` under hypothesis (4) of Tag 09F1 as that tag
states it, namely with the image of `k` *equal* to the set of elements having `p ^ n`-th roots for
all `n ≥ 1`.  Only one of the two implications is used. -/
theorem exists_pow_eq_and_not_pow_of_not_range
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p : ℕ) (h : ∀ x : K, (∃ a : k, algebraMap k K a = x) ↔
      ∀ n : ℕ, 1 ≤ n → ∃ y : K, y ^ (p ^ n) = x)
    (x : K) (hx : ¬∃ a : k, algebraMap k K a = x) :
    ∃ (r : ℕ) (y : K), y ^ (p ^ r) = x ∧ ¬∃ z : K, z ^ p = y :=
  exists_pow_eq_and_not_pow_of_perfectCore_le p (fun y hy => (h y).mpr hy) x hx

end IsDiscreteValuationRing
