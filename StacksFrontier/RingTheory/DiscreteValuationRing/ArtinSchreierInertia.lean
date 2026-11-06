module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier

/-!
# Artin–Schreier classes of large pole order are seen by every open part of inertia

Let `A` be a discrete valuation ring with uniformizer `π`, perfect residue field and fraction field
`K` of characteristic `p > 0`.

## Main results

* `IsDiscreteValuationRing.exists_eq_inv_pow_mul`: every element of `K` is `π ^ (-m) · a`, `a ∈ A`.
* `IsDiscreteValuationRing.exists_artinSchreier_reduction`: every element of `K` is, modulo
  `℘(K) = {g ^ p - g}`, either integral or of the form `π ^ (-m) · u` with `u` a unit and `m > 0`
  prime to `p` (the residue field being perfect).
* `IsDiscreteValuationRing.inv_pow_mul_ne_artinSchreier_add`: an element `π ^ (-n) · u`, `u` a
  unit, `n > 0` prime to `p`, does not lie in `℘(K) + A`.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace IsDiscreteValuationRing

section Reduction

variable {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- Every element of the fraction field of a discrete valuation ring is `π ^ (-m) · a` for some
`m : ℕ` and `a ∈ A`. -/
theorem exists_eq_inv_pow_mul {π : A} (hπ : Irreducible π) (h : K) :
    ∃ (m : ℕ) (a : A), h = (algebraMap A K π)⁻¹ ^ m * algebraMap A K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) h
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hπ
  have hu : algebraMap A K (u : A) * algebraMap A K (↑u⁻¹ : A) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hu' : (algebraMap A K (u : A))⁻¹ = algebraMap A K (↑u⁻¹ : A) :=
    (eq_inv_of_mul_eq_one_right hu).symm
  refine ⟨k, a * ↑u⁻¹, ?_⟩
  rw [map_mul, map_mul, map_pow, div_eq_mul_inv, mul_inv, hu', inv_pow]
  ring

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The image in `K` of an irreducible element of `A` is nonzero. -/
theorem algebraMap_irreducible_ne_zero {π : A} (hπ : Irreducible π) : algebraMap A K π ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hπ.ne_zero

/-- Every element of the fraction field of a discrete valuation ring is integral or of the form
`π ^ (-m) · v` with `m > 0` and `v` a unit. -/
theorem exists_eq_algebraMap_or_eq_inv_pow_mul_unit {π : A} (hπ : Irreducible π) (g : K) :
    (∃ c : A, g = algebraMap A K c) ∨
      ∃ (m : ℕ) (v : A), 0 < m ∧ IsUnit v ∧ g = (algebraMap A K π)⁻¹ ^ m * algebraMap A K v := by
  obtain ⟨m, a, rfl⟩ := exists_eq_inv_pow_mul hπ g
  have hϖ := algebraMap_irreducible_ne_zero (K := K) hπ
  rcases eq_or_ne a 0 with rfl | ha
  · exact Or.inl ⟨0, by simp⟩
  obtain ⟨k, v, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  rcases le_or_gt m k with hmk | hmk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
    refine Or.inl ⟨v * π ^ d, ?_⟩
    simp only [map_mul, map_pow, inv_pow, pow_add]
    field_simp
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmk
    refine Or.inr ⟨d + 1, v, d.succ_pos, v.isUnit, ?_⟩
    simp only [map_mul, map_pow, inv_pow, pow_add, pow_one]
    field_simp

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- The reduction step behind `exists_artinSchreier_reduction`, by induction on the pole order. -/
theorem exists_artinSchreier_reduction_inv_pow_mul [PerfectField (IsLocalRing.ResidueField A)]
    {π : A} (hπ : Irreducible π) (m : ℕ) (a : A) :
    ∃ g : K, (∃ b : A, (algebraMap A K π)⁻¹ ^ m * algebraMap A K a =
        g ^ p - g + algebraMap A K b) ∨
      ∃ (n : ℕ) (u : A), 0 < n ∧ ¬ p ∣ n ∧ IsUnit u ∧
        (algebraMap A K π)⁻¹ ^ m * algebraMap A K a =
          g ^ p - g + (algebraMap A K π)⁻¹ ^ n * algebraMap A K u := by
  have hϖ := algebraMap_irreducible_ne_zero (K := K) hπ
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpA : (p : A) = 0 := (IsFractionRing.injective A K) (by simp)
  have : CharP (IsLocalRing.ResidueField A) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).2 (by rw [← map_natCast (IsLocalRing.residue A), hpA,
      map_zero])
  induction m using Nat.strong_induction_on generalizing a with
  | _ m ih =>
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0, Or.inl ⟨a, by simp [zero_pow hp0]⟩⟩
  by_cases ha : IsUnit a
  · by_cases hpm : p ∣ m
    · obtain ⟨m', rfl⟩ := hpm
      have hm' : 0 < m' := Nat.pos_of_mul_pos_left hm
      obtain ⟨w', hw'⟩ := surjective_frobenius (IsLocalRing.ResidueField A) p
        (IsLocalRing.residue A a)
      obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective w'
      have hmem : a - w ^ p ∈ IsLocalRing.maximalIdeal A := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← hw', frobenius_def, sub_self]
      rw [(irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton'] at hmem
      obtain ⟨b, hb⟩ := hmem
      obtain ⟨j, hj⟩ : ∃ j, p * m' = m' + j + 1 := by
        have : 2 * m' ≤ p * m' := Nat.mul_le_mul_right m' hp.out.two_le
        exact ⟨p * m' - m' - 1, by omega⟩
      obtain ⟨g', hg'⟩ := ih (m' + j) (by omega) (b + w * π ^ j)
      set t : K := algebraMap A K w * (algebraMap A K π)⁻¹ ^ m'
      have ht : t ^ p = algebraMap A K w ^ p * (algebraMap A K π)⁻¹ ^ (m' + j + 1) := by
        rw [mul_pow, ← pow_mul, mul_comm m' p, hj]
      have ha' : algebraMap A K a = algebraMap A K w ^ p + algebraMap A K b * algebraMap A K π := by
        rw [← map_pow, ← map_mul, ← map_add, hb]; ring_nf
      have key : (algebraMap A K π)⁻¹ ^ (p * m') * algebraMap A K a =
          t ^ p - t + (algebraMap A K π)⁻¹ ^ (m' + j) * algebraMap A K (b + w * π ^ j) := by
        rw [ht, hj, ha']
        simp only [t, map_add, map_mul, map_pow, inv_pow, pow_add, pow_one]
        field_simp
        ring
      have hadd : (g' + t) ^ p = g' ^ p + t ^ p := add_pow_char g' t p
      refine ⟨g' + t, ?_⟩
      rcases hg' with ⟨b', hb'⟩ | ⟨n, u, hn, hpn, hu, hu'⟩
      · exact Or.inl ⟨b', by rw [key, hb', hadd]; ring⟩
      · exact Or.inr ⟨n, u, hn, hpn, hu, by rw [key, hu', hadd]; ring⟩
    · exact ⟨0, Or.inr ⟨m, a, hm, hpm, ha, by simp [zero_pow hp0]⟩⟩
  · have hmem : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).2 ha
    rw [(irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton'] at hmem
    obtain ⟨b, rfl⟩ := hmem
    obtain ⟨g, hg⟩ := ih (m - 1) (by omega) b
    have key : (algebraMap A K π)⁻¹ ^ m * algebraMap A K (b * π) =
        (algebraMap A K π)⁻¹ ^ (m - 1) * algebraMap A K b := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
      simp only [Nat.zero_add, Nat.add_sub_cancel, map_mul, inv_pow, pow_add, pow_one]
      field_simp
    exact ⟨g, by rwa [key]⟩

/-- **Artin–Schreier reduction.** Over a discrete valuation ring with perfect residue field, every
element of the fraction field is, modulo `℘(K) = {g ^ p - g}`, either integral or of the form
`π ^ (-n) · u` with `u` a unit and `n > 0` prime to `p`. -/
theorem exists_artinSchreier_reduction [PerfectField (IsLocalRing.ResidueField A)]
    {π : A} (hπ : Irreducible π) (h : K) :
    ∃ g : K, (∃ b : A, h = g ^ p - g + algebraMap A K b) ∨
      ∃ (n : ℕ) (u : A), 0 < n ∧ ¬ p ∣ n ∧ IsUnit u ∧
        h = g ^ p - g + (algebraMap A K π)⁻¹ ^ n * algebraMap A K u := by
  obtain ⟨m, a, rfl⟩ := exists_eq_inv_pow_mul hπ h
  exact exists_artinSchreier_reduction_inv_pow_mul p hπ m a

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- `π ^ (-n) · u` with `n > 0` and `u` a unit is not integral. -/
theorem inv_pow_mul_ne_algebraMap {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) {u : A}
    (hu : IsUnit u) (b : A) : (algebraMap A K π)⁻¹ ^ n * algebraMap A K u ≠ algebraMap A K b := by
  intro h
  have hϖ := algebraMap_irreducible_ne_zero (K := K) hπ
  have h' : algebraMap A K u = algebraMap A K (π ^ n * b) := by
    rw [map_mul, map_pow, ← h, inv_pow]; field_simp
  rw [(IsFractionRing.injective A K).eq_iff] at h'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [h', pow_add, pow_one, mul_comm _ π, mul_assoc] at hu
  exact hπ.not_isUnit (isUnit_of_mul_isUnit_left hu)

/-- `u - π ^ k * v` is a unit for a unit `u` and `k > 0`. -/
private theorem isUnit_sub_pow_mul_aux {π : A} (hπ : Irreducible π) {u : A} (hu : IsUnit u)
    {k : ℕ} (hk : 0 < k) (v : A) : IsUnit (u - π ^ k * v) := by
  by_contra h
  have h1 : u - π ^ k * v ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : π ^ k * v ∈ IsLocalRing.maximalIdeal A := by
    rw [(irreducible_iff_uniformizer π).1 hπ]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
    exact Ideal.mem_span_singleton.2 ⟨π ^ k * v, by ring⟩
  have h3 := Ideal.add_mem _ h1 h2
  rw [sub_add_cancel] at h3
  exact (IsLocalRing.mem_maximalIdeal _).1 h3 hu

omit [CharP K p] in
/-- An element `π ^ (-n) · u`, `u` a unit and `n > 0` prime to `p`, is not in `℘(K) + A`. -/
theorem inv_pow_mul_ne_artinSchreier_add {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (hpn : ¬ p ∣ n) {u : A} (hu : IsUnit u) (g : K) (b : A) :
    (algebraMap A K π)⁻¹ ^ n * algebraMap A K u ≠ g ^ p - g + algebraMap A K b := by
  have hϖ := algebraMap_irreducible_ne_zero (K := K) hπ
  rcases exists_eq_algebraMap_or_eq_inv_pow_mul_unit hπ g with ⟨c, rfl⟩ | ⟨m, v, hm, hv, rfl⟩
  · simpa only [map_add, map_sub, map_pow] using
      inv_pow_mul_ne_algebraMap (K := K) hπ hn hu (c ^ p - c + b)
  intro h
  obtain ⟨d, hd⟩ : ∃ d, (p - 1) * m = d + 1 := by
    have : 1 ≤ (p - 1) * m := Nat.one_le_iff_ne_zero.2
      (mul_ne_zero (by have := hp.out.two_le; omega) hm.ne')
    exact ⟨(p - 1) * m - 1, by omega⟩
  set c : A := v ^ p - π ^ ((p - 1) * m) * v + π ^ (p * m) * b
  have hpm : p * m = (p - 1) * m + m := by
    have := hp.out.one_le
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]
  have hc : IsUnit c := by
    rw [show c = v ^ p - π ^ ((p - 1) * m) * (v - π ^ m * b) by
      simp only [c, mul_sub, ← mul_assoc, ← pow_add, ← hpm]; ring]
    exact isUnit_sub_pow_mul_aux hπ (hv.pow p) (by omega) _
  have hval : ((algebraMap A K π)⁻¹ ^ m * algebraMap A K v) ^ p - (algebraMap A K π)⁻¹ ^ m *
      algebraMap A K v + algebraMap A K b = (algebraMap A K π)⁻¹ ^ (p * m) * algebraMap A K c := by
    simp only [c, mul_pow, ← pow_mul, mul_comm m p, map_add, map_sub, map_mul, map_pow]
    rw [hpm]
    simp only [inv_pow, pow_add]
    field_simp
  rw [hval] at h
  have e1 : algebraMap A K (π ^ (p * m) * u) = algebraMap A K (π ^ n * c) := by
    simp only [map_mul, map_pow]
    simp only [inv_pow] at h
    field_simp at h
    linear_combination h
  rw [(IsFractionRing.injective A K).eq_iff, mul_comm, mul_comm _ c] at e1
  have := unit_mul_pow_congr_pow hπ hπ hu.unit hc.unit (p * m) n e1
  exact hpn ⟨m, this.symm⟩

end Reduction

section Galois

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- A ring endomorphism of a field of characteristic `p` fixes every root of `X ^ p - X`: these
are the elements of the prime field. -/
theorem ringHom_apply_eq_of_pow_eq_self {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (σ : L →+* L) {z : L} (hz : z ^ p = z) : σ z = z := by
  rw [← Subfield.mem_bot_iff_pow_eq_self L p, ← ZMod.fieldRange_castHom_eq_bot p] at hz
  obtain ⟨i, rfl⟩ := hz
  rw [← ZMod.natCast_zmod_val i, map_natCast, map_natCast]

/-- Over a separably closed field of characteristic `p`, every Artin–Schreier equation
`y ^ p - y = a` has a root. -/
theorem exists_pow_sub_self_eq {L : Type*} [Field L] [IsSepClosed L] (p : ℕ) [hp : Fact p.Prime]
    [CharP L p] (a : L) : ∃ y : L, y ^ p - y = a := by
  open Polynomial in
  have hdeg : (X ^ p - X - C a : L[X]).natDegree = p := by
    rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [hp.out.one_lt]
  have hsep : (X ^ p - X - C a : L[X]).Separable := by
    rw [Polynomial.separable_def]
    have hd : derivative (X ^ p - X - C a : L[X]) = -1 := by
      simp [derivative_X_pow, CharP.cast_eq_zero]
    rw [hd]
    exact isCoprime_one_right.neg_right
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root _ (by
    rw [degree_eq_natDegree (fun h => by simp [h] at hdeg; exact hp.out.ne_zero hdeg.symm),
      hdeg]; exact_mod_cast hp.out.ne_zero) hsep
  refine ⟨y, ?_⟩
  simpa [sub_eq_zero] using hy

/-- In a finite Galois extension `F / K` which is totally ramified with respect to `A` (one
maximal ideal above `m_A`, trivial residue extension), the inertia group of the maximal ideal is
the whole Galois group. -/
theorem inertia_eq_top_of_isTotallyRamified (F : Type*) [Field F] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [FiniteDimensional K F] [IsGalois K F]
    (h : Stacks.KummerExtension.IsTotallyRamified A K F) (q : Ideal (integralClosure A F))
    [q.IsMaximal] :
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    q.inertia Gal(F/K) = ⊤ := by
  classical
  let C := integralClosure A F
  let := IsIntegralClosure.MulSemiringAction A K F C
  let : SMulCommClass Gal(F/K) A C :=
    ⟨fun σ a c ↦ by
      simp only [Algebra.smul_def, smul_mul']
      congr 1
      exact (galRestrict A K F C σ).commutes a⟩
  obtain ⟨m, hm, hmo, huniq, hdeg⟩ := h
  have hqo : q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q)).symm⟩
  obtain rfl : q = m := huniq q ‹_› hqo
  have hcomap : Ideal.comap (algebraMap A C) q = IsLocalRing.maximalIdeal A := hqo.over.symm
  rw [Ideal.inertiaDeg', dite_eq_left hcomap] at hdeg
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  let := Ideal.Quotient.field q
  let : Algebra (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ q) :=
    Ideal.Quotient.algebraQuotientOfLEComap hcomap.ge
  have : Module.Free (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ q) := Module.Free.of_divisionRing _ _
  have hsurj : ∀ c : C, ∃ a : A, c - algebraMap A C a ∈ q := by
    intro c
    have htop : (⊥ : Subalgebra (A ⧸ IsLocalRing.maximalIdeal A) (C ⧸ q)) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one hdeg
    have hc : Ideal.Quotient.mk q c ∈ (⊥ : Subalgebra _ (C ⧸ q)) := htop ▸ Algebra.mem_top
    obtain ⟨a', ha'⟩ := Algebra.mem_bot.1 hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    refine ⟨a, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ha']
    exact sub_eq_zero.2 rfl
  rw [eq_top_iff]
  intro τ _
  rw [Ideal.mem_inertia]
  intro c
  have hτq : τ • q = q := by
    have hmax : (τ • q).IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) _ ?_
      have : (τ • q).under A = q.under A := Ideal.under_smul A q τ
      rw [this]
      exact Ideal.IsMaximal.under A q
    exact huniq _ hmax inferInstance
  obtain ⟨a, ha⟩ := hsurj c
  have hc : τ • c - c = τ • (c - algebraMap A C a) - (c - algebraMap A C a) := by
    rw [smul_sub, smul_algebraMap]
    ring
  rw [hc]
  exact sub_mem (hτq ▸ Ideal.smul_mem_pointwise_smul τ _ q ha) ha

variable (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- An element of the inertia group of the contraction of `P` to a finite Galois subextension
`F / K` of a Galois extension `L / K` is the restriction of an element of the inertia group of
`P`. -/
theorem exists_mem_inertia_restrictNormal_eq [IsGalois K L] (P : Ideal (integralClosure A L))
    [P.IsPrime] (F : IntermediateField K L) [FiniteDimensional K F] [IsGalois K F] :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    letI := IsIntegralClosure.MulSemiringAction A K F (integralClosure A F)
    letI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ τ ∈ (P.comap (IsScalarTower.toAlgHom A F L).mapIntegralClosure.toRingHom).inertia Gal(F/K),
      ∃ σ ∈ P.inertia Gal(L/K), AlgEquiv.restrictNormal σ F = τ := by
  classical
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let C := integralClosure A F
  let B := integralClosure A L
  let : MulSemiringAction Gal(L/K) B := IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction Gal(F/K) C := IsIntegralClosure.MulSemiringAction A K F C
  let f : C →ₐ[A] B := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let : Algebra C B := f.toRingHom.toAlgebra
  let : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  let : IsScalarTower C B L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower C F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension A K F C
  let : Algebra.IsAlgebraic A L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_algebraic A B fun _ hx ↦
      IsFractionRing.to_map_eq_zero_iff.mp
        ((map_eq_zero (algebraMap K L)).mp <|
          (IsScalarTower.algebraMap_apply A K L _).symm.trans hx)
  have hImage := (IsIntegralClosure.image_stabilizer_and_inertia_restrictNormalHom
    A K F L C B P).2
  intro τ hτ
  have hτ' : τ ∈ ((P.under C).inertia Gal(F/K) : Set Gal(F/K)) := hτ
  rw [← hImage] at hτ'
  obtain ⟨σ, hσ, hres⟩ := hτ'
  exact ⟨σ, hσ, hres⟩

/-- The generator of `K⟮α⟯` generates it as a `K`-algebra when `α` is integral. -/
theorem algebra_adjoin_adjoinSimple_gen_eq_top {F E : Type*} [Field F] [Field E] [Algebra F E]
    {α : E} (hα : IsIntegral F α) :
    Algebra.adjoin F {IntermediateField.AdjoinSimple.gen F α} = ⊤ := by
  apply Subalgebra.map_injective (f := (IntermediateField.adjoin F {α}).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, IntermediateField.range_val,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic]
  simp only [IntermediateField.coe_val, IntermediateField.AdjoinSimple.coe_gen]

variable (p : ℕ) [hp : Fact p.Prime]

/-- **An Artin–Schreier class fixed by inertia is integral.** If every element of the inertia
group of `P` fixes a root `y ∈ L` of `y ^ p - y = h`, then `h ∈ ℘(K) + A`. The reduced form of
`h` cannot have a pole: an Artin–Schreier extension `K(y) / K` with `h = π ^ (-n) · u`, `p ∤ n`,
is totally ramified, so its inertia group is all of `Gal(K(y)/K)`, which moves `y`, and that
inertia lifts to inertia of `P`. -/
theorem exists_eq_pow_sub_self_add_of_forall_inertia [IsSepClosure K L]
    [PerfectField (IsLocalRing.ResidueField A)] [CharP K p] (P : Ideal (integralClosure A L))
    [P.IsMaximal] {π : A} (hπ : Irreducible π) (h : K) (y : L)
    (hy : y ^ p - y = algebraMap K L h)
    (hI : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ σ ∈ P.inertia Gal(L/K), σ y = y) :
    ∃ (g : K) (b : A), h = g ^ p - g + algebraMap A K b := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨g, ⟨b, hb⟩ | ⟨n, u, hn, hpn, hu, hu'⟩⟩ := exists_artinSchreier_reduction p hπ h
  · exact ⟨g, b, hb⟩
  exfalso
  set ξ : K := (algebraMap A K π)⁻¹ ^ n * algebraMap A K u with hξ
  set y' := y - algebraMap K L g with hy'def
  have hy' : y' ^ p - y' = algebraMap K L ξ := by
    have h' : algebraMap K L h = algebraMap K L g ^ p - algebraMap K L g + algebraMap K L ξ := by
      rw [hu']; simp only [map_add, map_sub, map_pow]
    rw [hy'def, sub_pow_char]
    linear_combination hy + h'
  have hI' : ∀ σ ∈ P.inertia Gal(L/K), σ y' = y' := fun σ hσ => by
    rw [hy'def, map_sub, hI σ hσ, AlgEquiv.commutes]
  let F := IntermediateField.adjoin K {y'}
  let z : F := IntermediateField.AdjoinSimple.gen K y'
  have hz : z ^ p - z = algebraMap K F ξ := Subtype.ext (by simpa [z] using hy')
  have hgen : Algebra.adjoin K {z} = ⊤ :=
    algebra_adjoin_adjoinSimple_gen_eq_top (Algebra.IsIntegral.isIntegral y')
  obtain ⟨hfin, hgal, -, -, htot, -⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_artinSchreier A K F p hp.out ξ z hz hgen π hπ
  let := hfin
  have : FiniteDimensional K F := hfin
  have htot' := htot n u hn hpn hu rfl
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let fC := (IsScalarTower.toAlgHom A F L).mapIntegralClosure
  let q := P.comap fC.toRingHom
  have : q.IsMaximal := by
    let : Algebra (integralClosure A F) (integralClosure A L) := fC.toRingHom.toAlgebra
    let : IsScalarTower A (integralClosure A F) (integralClosure A L) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (fC.commutes x).symm
    let : Algebra.IsIntegral (integralClosure A F) (integralClosure A L) :=
      Algebra.IsIntegral.tower_top A
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := integralClosure A F) P
  have htop := inertia_eq_top_of_isTotallyRamified A K F htot'.1 q
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(F/K), τ z ≠ z := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    obtain ⟨k₀, hk₀⟩ := (IsGalois.mem_range_algebraMap_iff_fixed z).2 hcon
    apply inv_pow_mul_ne_artinSchreier_add p hπ hn hpn hu k₀ 0
    apply (algebraMap K F).injective
    rw [map_add, map_sub, map_pow, hk₀, ← hz, map_zero, map_zero, add_zero]
  obtain ⟨σ, hσ, hres⟩ := exists_mem_inertia_restrictNormal_eq A K L P F τ
    (by rw [htop]; exact Subgroup.mem_top τ)
  apply hτ
  apply Subtype.ext
  have hc := AlgEquiv.restrictNormal_commutes σ F z
  rw [hres] at hc
  show algebraMap F L (τ z) = algebraMap F L z
  rw [hc]
  exact hI' σ hσ

/-- `u - π ^ k · v` is a unit for a unit `u` and `k > 0`. -/
theorem isUnit_sub_pow_mul {π : A} (hπ : Irreducible π) {u : A} (hu : IsUnit u) {k : ℕ}
    (hk : 0 < k) (v : A) : IsUnit (u - π ^ k * v) :=
  isUnit_sub_pow_mul_aux hπ hu hk v

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- With `x = π⁻¹`, `a x ^ n + c x = x ^ n (a + c π ^ (n - 1))` for `n ≥ 1`: the shape
`π ^ (-n) · u` of `a x ^ n + c x` used at `∞` on the affine line. -/
theorem mul_inv_pow_add_mul_inv_eq {π : A} (hπ : Irreducible π) (a c : A) {n : ℕ} (hn : 1 ≤ n) :
    algebraMap A K a * (algebraMap A K π)⁻¹ ^ n + algebraMap A K c * (algebraMap A K π)⁻¹ =
      (algebraMap A K π)⁻¹ ^ n * algebraMap A K (a + c * π ^ (n - 1)) := by
  have hϖ := algebraMap_irreducible_ne_zero (K := K) hπ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, map_add, map_mul, map_pow, inv_pow, pow_add, pow_one]
  field_simp

/-- `a + c π ^ k` is a unit for a unit `a` and `k > 0`. -/
theorem isUnit_add_mul_pow {π : A} (hπ : Irreducible π) {a : A} (ha : IsUnit a) (c : A) {k : ℕ}
    (hk : 0 < k) : IsUnit (a + c * π ^ k) := by
  have := isUnit_sub_pow_mul A hπ ha hk (-c)
  rwa [show a - π ^ k * -c = a + c * π ^ k by ring] at this

/-- Two `K`-automorphisms of `L` with the same restriction to a normal subextension `E` differ by
an element of the fixing subgroup of `E`. -/
private theorem inv_mul_mem_fixingSubgroup_of_restrictNormal_eq {E : IntermediateField K L}
    [Normal K E] {σ σ' : Gal(L/K)}
    (h : AlgEquiv.restrictNormal σ E = AlgEquiv.restrictNormal σ' E) :
    σ'⁻¹ * σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro e he
  have h1 := AlgEquiv.restrictNormal_commutes σ E ⟨e, he⟩
  have h2 := AlgEquiv.restrictNormal_commutes σ' E ⟨e, he⟩
  rw [h] at h1
  have h3 : σ e = σ' e := h1.symm.trans h2
  show σ'.symm (σ e) = e
  rw [h3]
  exact σ'.symm_apply_apply e

/-- For a subgroup `I` of `Gal(L/K)` and a normal subextension `E`, there is a map
`s : Gal(E/K) → Gal(L/K)` such that every `σ ∈ I` agrees with `s (σ|_E)` on the elements fixed by
`I ∩ Gal(L/E)`. -/
private theorem exists_apply_eq_apply_restrictNormal_of_forall_fixingSubgroup
    {E : IntermediateField K L} [Normal K E] (I : Subgroup Gal(L/K)) :
    ∃ s : Gal(E/K) → Gal(L/K), ∀ σ ∈ I, ∀ y : L,
      (∀ ρ ∈ I, ρ ∈ E.fixingSubgroup → ρ y = y) → σ y = s (AlgEquiv.restrictNormal σ E) y := by
  classical
  refine ⟨fun τ => if h : ∃ σ ∈ I, AlgEquiv.restrictNormal σ E = τ then h.choose else 1, ?_⟩
  intro σ hσ y hy
  have h : ∃ σ' ∈ I, AlgEquiv.restrictNormal σ' E = AlgEquiv.restrictNormal σ E := ⟨σ, hσ, rfl⟩
  simp only [dite_eq_left h]
  obtain ⟨hσ', hres⟩ := h.choose_spec
  have h4 : h.choose.symm (σ y) = y := hy (h.choose⁻¹ * σ) (I.mul_mem (I.inv_mem hσ') hσ)
    (inv_mul_mem_fixingSubgroup_of_restrictNormal_eq K L hres.symm)
  exact (h.choose.apply_symm_apply _).symm.trans (congrArg h.choose h4)

/-- A `K`-automorphism moves a root of `y ^ p - y = h`, `h ∈ K`, by a root of `z ^ p = z`. -/
private theorem apply_sub_self_pow_eq_of_pow_sub_self_eq [CharP L p] {h : K} {y : L}
    (hy : y ^ p - y = algebraMap K L h) (σ : Gal(L/K)) : (σ y - y) ^ p = σ y - y := by
  have : σ (y ^ p - y) = y ^ p - y := by rw [hy, AlgEquiv.commutes]
  rw [map_sub, map_pow] at this
  rw [sub_pow_char]
  linear_combination this

/-- If roots `y`, `y₀` of `y ^ p - y = π ^ (-n) · u` and `y₀ ^ p - y₀ = h₀`, with `u` a unit and
`p ∤ n`, differ by an element fixed by inertia, then `h₀` is not congruent modulo `℘(K)` to an
element `π ^ (-k) · b` with `b ∈ A` and `k < n`. -/
private theorem ne_pow_sub_self_add_of_forall_inertia_sub [IsSepClosure K L]
    [PerfectField (IsLocalRing.ResidueField A)] [CharP K p] (P : Ideal (integralClosure A L))
    [P.IsMaximal] {π : A} (hπ : Irreducible π) {n : ℕ} {u : A} (hpn : ¬ p ∣ n) (hu : IsUnit u)
    {y y₀ : L} {h₀ : K}
    (hy : y ^ p - y = algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u))
    (hy₀ : y₀ ^ p - y₀ = algebraMap K L h₀)
    (hfix : letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
      ∀ σ ∈ P.inertia Gal(L/K), σ (y - y₀) = y - y₀)
    {g₀ : K} {k : ℕ} {b : A} (hkn : k < n) :
    h₀ ≠ g₀ ^ p - g₀ + (algebraMap A K π)⁻¹ ^ k * algebraMap A K b := by
  intro hk₀
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hroot : (y - y₀) ^ p - (y - y₀) =
      algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u - h₀) := by
    rw [sub_pow_char, map_sub]
    linear_combination hy - hy₀
  obtain ⟨g₁, b₁, h₁⟩ :=
    exists_eq_pow_sub_self_add_of_forall_inertia A K L p P hπ _ _ hroot hfix
  have hadd : (g₁ + g₀) ^ p = g₁ ^ p + g₀ ^ p := add_pow_char g₁ g₀ p
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkn
  apply inv_pow_mul_ne_artinSchreier_add p hπ (by omega) hpn
    (isUnit_sub_pow_mul A hπ hu (Nat.succ_pos d) b) (g₁ + g₀) b₁
  have hϖ := algebraMap_irreducible_ne_zero (K := K) hπ
  have e : (algebraMap A K π)⁻¹ ^ n * algebraMap A K (u - π ^ (d + 1) * b) =
      (algebraMap A K π)⁻¹ ^ n * algebraMap A K u -
        (algebraMap A K π)⁻¹ ^ k * algebraMap A K b := by
    rw [hd]
    simp only [map_sub, map_mul, map_pow, inv_pow, pow_add, pow_one]
    field_simp
  rw [e, hadd]
  linear_combination h₁ + hk₀

/-- **Artin–Schreier classes of large pole order are seen by every open part of inertia.** Let
`A` be a discrete valuation ring with perfect residue field and fraction field `K` of
characteristic `p`, `L` a separable closure of `K` and `P` a maximal ideal of the integral closure
of `A` in `L`, with inertia group `I`. For every open subgroup `U` of `Gal(L/K)` there is `N` such
that for every `f = π ^ (-n) · u` with `u` a unit, `n > N` and `p ∤ n`, every root `y ∈ L` of
`y ^ p - y = f` is moved by some element of `I ∩ U`.

The characters `σ ↦ σ y - y` of `I` trivial on `I ∩ U` factor through the finite group
`Gal(E/K)` for a finite Galois `E` with `Gal(L/E) ⊆ U`, so they are finitely many; two classes
with the same character differ by an element of `℘(K) + A`
(`IsDiscreteValuationRing.exists_eq_pow_sub_self_add_of_forall_inertia`); `N` is the largest
reduced pole order of a representative, and a reduced class of larger pole order prime to `p`
is not in `℘(K) + A` (`IsDiscreteValuationRing.inv_pow_mul_ne_artinSchreier_add`). -/
theorem exists_forall_exists_mem_inertia_mem_ne [IsSepClosure K L]
    [PerfectField (IsLocalRing.ResidueField A)] [CharP K p] (P : Ideal (integralClosure A L))
    [P.IsMaximal] {π : A} (hπ : Irreducible π) (U : Subgroup Gal(L/K))
    (hU : IsOpen (U : Set Gal(L/K))) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ N : ℕ, ∀ (n : ℕ) (u : A), N < n → ¬ p ∣ n → IsUnit u → ∀ y : L,
      y ^ p - y = algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u) →
        ∃ σ ∈ P.inertia Gal(L/K), σ ∈ U ∧ σ y ≠ y := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let I := P.inertia Gal(L/K)
  obtain ⟨E, hEfin, hEnorm, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal K L U).1 (hU.mem_nhds U.one_mem)
  have := hEfin
  have := hEnorm
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  have : IsGalois K E := {}
  -- a lift to inertia of every restriction of an inertia element; elements with the same
  -- restriction to `E` act in the same way on `I ∩ Gal(L/E)`-fixed points
  obtain ⟨s, hs⟩ := exists_apply_eq_apply_restrictNormal_of_forall_fixingSubgroup K L (E := E) I
  -- the values `σ y - y` lie in the prime field
  let Z := {z : L // z ^ p = z}
  have : Finite Z := by
    let := Subfield.fintypeBot L p
    exact Finite.of_equiv (⊥ : Subfield L)
      (Equiv.subtypeEquivRight fun z => Subfield.mem_bot_iff_pow_eq_self L p)
  let G := {q : K × L // q.2 ^ p - q.2 = algebraMap K L q.1 ∧
    ∀ ρ ∈ I, ρ ∈ E.fixingSubgroup → ρ q.2 = q.2}
  let Ψ : G → (Gal(E/K) → Z) := fun q τ =>
    ⟨s τ q.1.2 - q.1.2, apply_sub_self_pow_eq_of_pow_sub_self_eq K L p q.2.1 (s τ)⟩
  have hΨ : ∀ q : G, ∀ σ ∈ I, σ q.1.2 - q.1.2 = (Ψ q (AlgEquiv.restrictNormal σ E) : L) :=
    fun q σ hσ => congrArg (· - q.1.2) (hs σ hσ q.1.2 q.2.2)
  -- reduced pole orders of representatives
  have hM : ∀ φ : Gal(E/K) → Z, ∃ m : ℕ, ∀ q : G, Ψ q = φ → ∃ (q₀ : G) (g : K) (k : ℕ) (b : A),
      Ψ q₀ = φ ∧ k ≤ m ∧ q₀.1.1 = g ^ p - g + (algebraMap A K π)⁻¹ ^ k * algebraMap A K b := by
    intro φ
    by_cases hφ : ∃ q : G, Ψ q = φ
    · obtain ⟨q, hq⟩ := hφ
      obtain ⟨g, ⟨b, hg⟩ | ⟨k, u, -, -, -, hg⟩⟩ := exists_artinSchreier_reduction p hπ q.1.1
      exacts [⟨0, fun _ _ => ⟨q, g, 0, b, hq, le_rfl, by rwa [pow_zero, one_mul]⟩⟩,
        ⟨k, fun _ _ => ⟨q, g, k, u, hq, le_rfl, hg⟩⟩]
    · exact ⟨0, fun q hq => (hφ ⟨q, hq⟩).elim⟩
  choose M hM using hM
  obtain ⟨N, hN⟩ := Finite.exists_le M
  refine ⟨N, fun n u hn hpn hu y hy => ?_⟩
  by_contra hcon
  simp only [ne_eq, not_exists, not_and, not_not] at hcon
  let q : G := ⟨(_, y), hy, fun ρ hρ hρE => hcon ρ hρ (hEU hρE)⟩
  obtain ⟨q₀, g₀, k, b, hq₀, hkm, hk₀⟩ := hM (Ψ q) q rfl
  have hfix : ∀ σ ∈ I, σ (y - q₀.1.2) = y - q₀.1.2 := fun σ hσ => by
    have h₂ := hΨ q₀ σ hσ
    rw [hq₀] at h₂
    rw [map_sub]
    linear_combination hΨ q σ hσ - h₂
  exact ne_pow_sub_self_add_of_forall_inertia_sub A K L p P hπ hpn hu hy q₀.2.1 hfix
    ((hkm.trans (hN _)).trans_lt hn) hk₀

/-- Over a finite field `k ⊆ K` with `q` elements, every root `t` of `t ^ q - t = f` with
`f ∈ K` moves under a `K`-automorphism by an element of `k`. -/
theorem exists_sub_eq_algebraMap_of_pow_card_sub_self (k : Type*) [Field k] [Fintype k]
    [Algebra k K] {L : Type*} [Field L] [Algebra K L] (σ : Gal(L/K)) (t : L) (f : K)
    (ht : t ^ Fintype.card k - t = algebraMap K L f) :
    ∃ c : k, σ t - t = algebraMap K L (algebraMap k K c) := by
  classical
  let e : k →+* L := (algebraMap K L).comp (algebraMap k K)
  obtain ⟨p', hchar⟩ := CharP.exists k
  have : Fact p'.Prime := ⟨CharP.char_is_prime k p'⟩
  have : CharP L p' := charP_of_injective_ringHom e.injective p'
  have hroot : (σ t - t) ^ Fintype.card k = σ t - t := by
    obtain ⟨n, -, hn⟩ := FiniteField.card k p'
    have : σ (t ^ Fintype.card k - t) = t ^ Fintype.card k - t := by rw [ht, AlgEquiv.commutes]
    rw [map_sub, map_pow] at this
    rw [hn, sub_pow_char_pow, ← hn]
    linear_combination this
  open Polynomial in
  have hroots : (X ^ Fintype.card k - X : k[X]).roots = Finset.univ.val :=
    FiniteField.roots_X_pow_card_sub_X k
  open Polynomial in
  have hmap := roots_map_of_injective_of_card_eq_natDegree e.injective
    (p := (X ^ Fintype.card k - X : k[X])) (by
      rw [hroots, ← Finset.card_def, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card])
  open Polynomial in
  have hmem : σ t - t ∈ ((X ^ Fintype.card k - X : k[X]).map e).roots := by
    rw [mem_roots ((Polynomial.map_ne_zero_iff e.injective).2
      (FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card))]
    simp [hroot]
  rw [← hmap, hroots] at hmem
  obtain ⟨c, -, hc⟩ := Multiset.mem_map.1 hmem
  exact ⟨c, hc.symm⟩

/-- An additive subgroup `W` of a finite field `k` over `ZMod p` on which none of the linear forms
`Tr(b ·)`, `b ≠ 0`, vanishes is all of `k`, by nondegeneracy of the trace form. -/
private theorem eq_top_of_forall_exists_trace_mul_ne_zero {k : Type*} [Field k] [Finite k]
    [Algebra (ZMod p) k] (W : AddSubgroup k)
    (htr : ∀ b : k, b ≠ 0 → ∃ w ∈ W, Algebra.trace (ZMod p) k (b * w) ≠ 0) : W = ⊤ := by
  let W' : Submodule (ZMod p) k :=
    { W with
      smul_mem' := fun a w hw => by
        rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
        exact W.nsmul_mem hw _ }
  let β : k →ₗ[ZMod p] Module.Dual (ZMod p) W' :=
    (Algebra.traceForm (ZMod p) k).compl₂ W'.subtype
  have hβ : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro b hb
    by_contra hb0
    obtain ⟨w, hw, hw0⟩ := htr b hb0
    apply hw0
    simpa [β, Algebra.traceForm_apply] using LinearMap.congr_fun (LinearMap.mem_ker.1 hb) ⟨w, hw⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hβ
  rw [Subspace.dual_finrank_eq] at hle
  have htop : W' = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W') hle)
  exact eq_top_iff.2 fun c _ => (htop ▸ Submodule.mem_top : c ∈ W')

/-- For a subgroup `H` of `Gal(L/K)`, an element `t : L` and a ring `k` over `K`, the elements
`c ∈ k` by which some `σ ∈ H` moves `t`, `σ t - t = c`, form an additive subgroup of `k`. -/
private def displacementAddSubgroup (k : Type*) [CommRing k] [Algebra k K]
    (H : Subgroup Gal(L/K)) (t : L) : AddSubgroup k where
  carrier := {c | ∃ σ ∈ H, σ t - t = algebraMap K L (algebraMap k K c)}
  zero_mem' := ⟨1, H.one_mem, by simp⟩
  add_mem' := by
    rintro c₁ c₂ ⟨σ₁, h₁H, h₁⟩ ⟨σ₂, h₂H, h₂⟩
    refine ⟨σ₁ * σ₂, H.mul_mem h₁H h₂H, ?_⟩
    have : σ₁ (σ₂ t) = σ₁ t + algebraMap K L (algebraMap k K c₂) := by
      rw [show σ₂ t = t + algebraMap K L (algebraMap k K c₂) by rw [← h₂]; ring, map_add,
        AlgEquiv.commutes]
    rw [AlgEquiv.mul_apply, this, map_add, map_add]
    linear_combination h₁
  neg_mem' := by
    rintro c ⟨σ, hH, h⟩
    refine ⟨σ⁻¹, H.inv_mem hH, ?_⟩
    have h1 : σ⁻¹ (σ t - t) = σ⁻¹ (algebraMap K L (algebraMap k K c)) := by rw [h]
    have h2 : σ⁻¹ (σ t) = t := σ.symm_apply_apply t
    rw [map_sub, AlgEquiv.commutes, h2] at h1
    rw [map_neg, map_neg]
    linear_combination -h1

/-- Membership in `IsDiscreteValuationRing.displacementAddSubgroup`. -/
@[simp]
private theorem mem_displacementAddSubgroup (k : Type*) [CommRing k] [Algebra k K]
    (H : Subgroup Gal(L/K)) (t : L) (c : k) :
    c ∈ displacementAddSubgroup K L k H t ↔
      ∃ σ ∈ H, σ t - t = algebraMap K L (algebraMap k K c) :=
  Iff.rfl

/-- **The Artin–Schreier character of a large prime-to-`p` pole is onto on every open part of
inertia.** In the situation of
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_mem_ne`, let `k ⊆ A` be a finite field
with `q` elements. For every open subgroup `U` of `Gal(L/K)` there is `N` such that for every
`f = π ^ (-n) · u` with `u` a unit, `n > N` and `p ∤ n`, and every root `t ∈ L` of `t ^ q - t = f`,
the character `σ ↦ σ t - t` maps `I ∩ U` onto `k`.

For `b ∈ k`, `z = ∑_{i < r} (b t) ^ (p ^ i)` (`q = p ^ r`) is a root of `z ^ p - z = b f`, and
`σ z - z = Tr_{k/𝔽_p}(b (σ t - t))`; so the image `W` of `I ∩ U` is not killed by any of the linear
forms `Tr(b ·)`, `b ≠ 0`, and since the trace form is nondegenerate, `W = k`. -/
theorem exists_forall_exists_mem_inertia_mem_sub_eq [IsSepClosure K L]
    [PerfectField (IsLocalRing.ResidueField A)] [CharP K p] (k : Type*) [Field k] [Fintype k]
    [Algebra k A] [Algebra k K] [IsScalarTower k A K] (P : Ideal (integralClosure A L))
    [P.IsMaximal] {π : A} (hπ : Irreducible π) (U : Subgroup Gal(L/K))
    (hU : IsOpen (U : Set Gal(L/K))) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ N : ℕ, ∀ (n : ℕ) (u : A), N < n → ¬ p ∣ n → IsUnit u → ∀ t : L,
      t ^ Fintype.card k - t = algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u) →
        ∀ c : k, ∃ σ ∈ P.inertia Gal(L/K), σ ∈ U ∧
          σ t - t = algebraMap K L (algebraMap k K c) := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  let I := P.inertia Gal(L/K)
  obtain ⟨N, hN⟩ := exists_forall_exists_mem_inertia_mem_ne A K L p P hπ U hU
  refine ⟨N, fun n u hn hpn hu t ht => ?_⟩
  let e : k →+* L := (algebraMap K L).comp (algebraMap k K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 (e.injective (by simp))
  let : Algebra (ZMod p) k := ZMod.algebra k p
  set r := Module.finrank (ZMod p) k
  have hcard : Fintype.card k = p ^ r := by
    rw [Module.card_fintype (Module.finBasis (ZMod p) k), ZMod.card, Fintype.card_fin]
  have hfix : ∀ (σ : Gal(L/K)) (c : k), σ (e c) = e c := fun σ c => AlgEquiv.commutes σ _
  -- the image of `I ∩ U` is an additive subgroup of `k`
  let W := displacementAddSubgroup K L k (I ⊓ U) t
  -- no nonzero linear form `Tr(b ·)` kills `W`
  have htr : ∀ b : k, b ≠ 0 → ∃ w ∈ W, Algebra.trace (ZMod p) k (b * w) ≠ 0 := by
    intro b hb
    let z : L := ∑ i ∈ Finset.range r, (e b * t) ^ (p ^ i)
    have hzp : z ^ p = ∑ i ∈ Finset.range r, (e b * t) ^ (p ^ (i + 1)) := by
      rw [sum_pow_char]
      exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, pow_succ]
    have hbq : e b ^ (p ^ r) = e b := by rw [← map_pow, ← hcard, FiniteField.pow_card]
    have hz : z ^ p - z = algebraMap K L
        ((algebraMap A K π)⁻¹ ^ n * algebraMap A K (algebraMap k A b * u)) := by
      rw [hzp, show z = ∑ i ∈ Finset.range r, (e b * t) ^ (p ^ i) from rfl,
        ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (e b * t) ^ (p ^ i)), pow_zero,
        pow_one, mul_pow, hbq, ← hcard]
      have hb' : algebraMap K L (algebraMap A K (algebraMap k A b)) = e b := by
        simp only [e, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
      rw [map_mul, map_mul, map_mul, hb']
      rw [map_mul] at ht
      linear_combination (e b) * ht
    obtain ⟨σ, hσI, hσU, hσ⟩ := hN n (algebraMap k A b * u) hn hpn
      ((IsUnit.map (algebraMap k A) (Ne.isUnit hb)).mul hu) z hz
    obtain ⟨c, hc⟩ := exists_sub_eq_algebraMap_of_pow_card_sub_self K k σ t _ ht
    refine ⟨c, ⟨σ, Subgroup.mem_inf.2 ⟨hσI, hσU⟩, hc⟩, fun h0 => hσ ?_⟩
    have hσz : σ z - z = e (algebraMap (ZMod p) k (Algebra.trace (ZMod p) k (b * c))) := by
      rw [FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) k, Nat.card_zmod, map_sum, map_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, map_mul, hfix, map_pow, map_mul, ← sub_pow_char_pow, ← mul_sub, hc]
      rfl
    rwa [h0, map_zero, map_zero, sub_eq_zero] at hσz
  -- hence `W = k`, by nondegeneracy of the trace form
  have htop := eq_top_of_forall_exists_trace_mul_ne_zero p W htr
  intro c
  obtain ⟨σ, hσ, hσc⟩ : c ∈ W := by simp [htop]
  exact ⟨σ, (Subgroup.mem_inf.1 hσ).1, (Subgroup.mem_inf.1 hσ).2, hσc⟩

/-- **The twist of a continuous representation by an Artin–Schreier character of large
prime-to-`p` pole order has no fixed vectors and no coinvariants under inertia**, in the strong
form, for a twist by matrices `T c`, `c ∈ k` (e.g. a character `ψ` with values in a field `E`,
acting through the restriction of scalars of `E` to `Λ`): if `T c₀ - 1` is invertible, then some
element `σ` of inertia, with `σ t - t = c₀`, makes `T c₀ * ρ σ - 1` invertible. Here `ρ` is any
continuous representation of `Gal(L/K)` on `Λ ^ m`, `Λ` a topological field; `N` depends only on
`ρ`, `T` and `c₀`.

`T c * g - 1` is invertible for every `c` with `T c - 1` invertible on an open neighbourhood of
`1` in `GL_m(Λ)`; its preimage under `ρ` contains an open subgroup `U`, and
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_mem_sub_eq` gives `σ ∈ I ∩ U` with
`σ t - t = c₀`. -/
theorem exists_forall_exists_mem_inertia_isUnit_mul_sub_one [IsSepClosure K L]
    [PerfectField (IsLocalRing.ResidueField A)] [CharP K p] (k : Type*) [Field k] [Fintype k]
    [Algebra k A] [Algebra k K] [IsScalarTower k A K] (P : Ideal (integralClosure A L))
    [P.IsMaximal] {π : A} (hπ : Irreducible π) {Λ : Type*} [Field Λ] [TopologicalSpace Λ]
    [IsTopologicalRing Λ] [T1Space Λ] {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : Gal(L/K) →* GL m Λ) (hρ : Continuous ρ) (T : k → Matrix m m Λ) (c₀ : k)
    (hc₀ : IsUnit (T c₀ - 1)) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ N : ℕ, ∀ (n : ℕ) (u : A), N < n → ¬ p ∣ n → IsUnit u → ∀ t : L,
      t ^ Fintype.card k - t = algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u) →
        ∃ σ ∈ P.inertia Gal(L/K), σ t - t = algebraMap K L (algebraMap k K c₀) ∧
          IsUnit (T c₀ * (ρ σ : Matrix m m Λ) - 1) := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  -- the open set of `g` with `T c₀ * g - 1` invertible
  let O : Set (GL m Λ) := {g | (T c₀ * (g : Matrix m m Λ) - 1).det ≠ 0}
  have hO : IsOpen O :=
    isOpen_ne_fun (((continuous_const.matrix_mul Units.continuous_val).sub continuous_const :
      Continuous fun g : GL m Λ => T c₀ * (g : Matrix m m Λ) - 1).matrix_det) continuous_const
  have h1O : (1 : GL m Λ) ∈ O := by
    simp only [O, Set.mem_ofPred_eq, Units.val_one, Matrix.mul_one]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hc₀).ne_zero
  obtain ⟨E, hEfin, hEO⟩ := (krullTopology_mem_nhds_one_iff K L (ρ ⁻¹' O)).1
    ((hO.preimage hρ).mem_nhds (by simpa using h1O))
  have := hEfin
  obtain ⟨N, hN⟩ := exists_forall_exists_mem_inertia_mem_sub_eq A K L p k P hπ E.fixingSubgroup
    E.fixingSubgroup_isOpen
  refine ⟨N, fun n u hn hpn hu t ht => ?_⟩
  obtain ⟨σ, hσI, hσU, hσ⟩ := hN n u hn hpn hu t ht c₀
  refine ⟨σ, hσI, hσ, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  exact (hEO hσU : ρ σ ∈ O).isUnit

/-- The scalar case of
`IsDiscreteValuationRing.exists_forall_exists_mem_inertia_isUnit_mul_sub_one`: for a nontrivial
additive character `ψ` of `k` with values in `Λ`, some element `σ` of inertia makes
`ψ (σ t - t) • ρ σ - 1` invertible. -/
theorem exists_forall_exists_mem_inertia_isUnit_smul_sub_one [IsSepClosure K L]
    [PerfectField (IsLocalRing.ResidueField A)] [CharP K p] (k : Type*) [Field k] [Fintype k]
    [Algebra k A] [Algebra k K] [IsScalarTower k A K] (P : Ideal (integralClosure A L))
    [P.IsMaximal] {π : A} (hπ : Irreducible π) {Λ : Type*} [Field Λ] [TopologicalSpace Λ]
    [IsTopologicalRing Λ] [T1Space Λ] {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : Gal(L/K) →* GL m Λ) (hρ : Continuous ρ) (ψ : AddChar k Λ) (hψ : ψ ≠ 1) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    ∃ N : ℕ, ∀ (n : ℕ) (u : A), N < n → ¬ p ∣ n → IsUnit u → ∀ t : L,
      t ^ Fintype.card k - t = algebraMap K L ((algebraMap A K π)⁻¹ ^ n * algebraMap A K u) →
        ∃ σ ∈ P.inertia Gal(L/K), ∀ c : k, σ t - t = algebraMap K L (algebraMap k K c) →
          IsUnit (ψ c • (ρ σ : Matrix m m Λ) - 1) := by
  classical
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  obtain ⟨c₀, hc₀⟩ := AddChar.ne_one_iff.1 hψ
  have hT : IsUnit (ψ c₀ • (1 : Matrix m m Λ) - 1) := by
    rw [show ψ c₀ • (1 : Matrix m m Λ) - 1 = (ψ c₀ - 1) • (1 : Matrix m m Λ) by
      rw [sub_smul, one_smul], Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one,
      mul_one]
    exact (pow_ne_zero _ (sub_ne_zero.2 hc₀)).isUnit
  obtain ⟨N, hN⟩ := exists_forall_exists_mem_inertia_isUnit_mul_sub_one A K L p k P hπ ρ hρ
    (fun c => ψ c • (1 : Matrix m m Λ)) c₀ hT
  refine ⟨N, fun n u hn hpn hu t ht => ?_⟩
  obtain ⟨σ, hσI, hσ, hunit⟩ := hN n u hn hpn hu t ht
  refine ⟨σ, hσI, fun c hc => ?_⟩
  have hcc : c = c₀ := (algebraMap k K).injective ((algebraMap K L).injective (hc.symm.trans hσ))
  subst hcc
  simpa only [Matrix.smul_mul, Matrix.one_mul] using hunit

end Galois

end IsDiscreteValuationRing
