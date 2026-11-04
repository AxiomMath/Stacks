module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.GroupTheory.IndexNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ProEllUniqueIndexPrimeBase

/-!
# Absolute Galois groups which are `ℤ_ℓ`, by Kummer theory

Let `ℓ` be a prime and `F` a field containing a primitive `ℓ ^ e`-th root of unity for every `e`,
with an element `π` which is not an `ℓ`-th power and generates `Fˣ / Fˣ^ℓ`: every nonzero `a` is
`π ^ i * b ^ ℓ`. Assume moreover that every finite subextension of a separable closure `Ω / F` has
degree a power of `ℓ`. Then `Gal(Ω/F)` is isomorphic to `ℤ_ℓ`; precisely, it is a pro-`ℓ` group
with a unique open subgroup of index `ℓ` (the fixing group of `F(π^{1/ℓ})`, by Kummer theory) and
an open normal subgroup of index `ℓ ^ e` for every `e` (the fixing group of `F(π^{1/ℓ^e})`), so
it satisfies `Stacks.GroupCohomology.HasPrimeBase`
(`Stacks.GroupCohomology.hasPrimeBase_of_isProPGroup_of_unique_index_eq`).

The degree of `F(π^{1/ℓ^e})` is computed without irreducibility criteria: the extension is Galois
(it contains all roots of `X ^ (ℓ ^ e) - π`), the Kummer character `σ ↦ σ(α)/α` is a homomorphism
to the roots of unity of `F`, so `α ^ d ∈ F` for the degree `d`, and a Bézout argument with
`α ^ (ℓ ^ e) = π` shows that `d < ℓ ^ e` would make `π` an `ℓ`-th power.

## Main results

* `Stacks.GaloisCohomology.finrank_adjoin_of_pow_eq`: `[F(π^{1/ℓ^e}) : F] = ℓ ^ e`.
* `Stacks.GaloisCohomology.hasPrimeBase_gal_of_kummer`: the prime base of `Gal(Ω/F)`.

## References

* J.-P. Serre, *Cohomologie galoisienne*, II §3.3; *Corps locaux*, IV §2.
-/

@[expose] public section

open Polynomial IntermediateField Module

namespace Stacks.GaloisCohomology

/-- Two `n`-th roots of the same element differ by a power of a primitive `n`-th root of unity. -/
theorem exists_eq_pow_mul_of_pow_eq_pow {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) {α β : K} (hα0 : α ≠ 0) (h : β ^ n = α ^ n) :
    ∃ i < n, β = ζ ^ i * α := by
  obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one (ξ := β / α)
    (by rw [div_pow, h, div_self (pow_ne_zero _ hα0)])
  exact ⟨i, hi, by rw [hie, div_mul_cancel₀ _ hα0]⟩

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- An element which is not an `ℓ`-th power is nonzero. -/
private theorem ne_zero_of_forall_pow_ne {ℓ : ℕ} (hℓ : ℓ.Prime) {π : F}
    (hπ : ∀ y : F, y ^ ℓ ≠ π) : π ≠ 0 :=
  fun h => hπ 0 (by rw [h, zero_pow hℓ.ne_zero])

/-- An `n`-th root of a nonzero element is nonzero. -/
private theorem ne_zero_of_pow_eq_algebraMap {n : ℕ} [NeZero n] {a : F} {α : Ω}
    (hα : α ^ n = algebraMap F Ω a) (ha : a ≠ 0) : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n), eq_comm, map_eq_zero] at hα
  exact ha hα

/-- The fixing subgroup of the fixed field of an open subgroup is the subgroup itself. -/
private theorem fixingSubgroup_fixedField_openSubgroup [IsGalois F Ω]
    (U : OpenSubgroup Gal(Ω/F)) :
    (fixedField (U : Subgroup Gal(Ω/F))).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩

/-- **A Kummer extension is Galois**: adjoining one `n`-th root of `a` adjoins all of them when
`F` contains a primitive `n`-th root of unity. -/
theorem isGalois_adjoin_of_pow_eq [Algebra.IsSeparable F Ω] {n : ℕ} [NeZero n] {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) {a : F} {α : Ω} (hα : α ^ n = algebraMap F Ω a) (ha : a ≠ 0) :
    IsGalois F F⟮α⟯ := by
  have hα0 := ne_zero_of_pow_eq_algebraMap hα ha
  set p : F[X] := X ^ n - C a with hp
  have hp0 : p ≠ 0 := X_pow_sub_C_ne_zero (NeZero.pos n) a
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) n := hζ.map_of_injective (algebraMap F Ω).injective
  have hsplit : (p.map (algebraMap F Ω)).Splits := by
    simpa [p] using X_pow_sub_C_splits_of_isPrimitiveRoot hζΩ hα
  have hroot : ∀ r : Ω, r ∈ p.rootSet Ω ↔ r ^ n = algebraMap F Ω a := by
    intro r
    rw [mem_rootSet]
    simp [p, hp0, sub_eq_zero]
  have heq : F⟮α⟯ = adjoin F (p.rootSet Ω) := by
    refine le_antisymm (adjoin_simple_le_iff.2 (subset_adjoin _ _ ((hroot α).2 hα)))
      (adjoin_le_iff.2 fun r hr => ?_)
    obtain ⟨i, -, hi⟩ := exists_eq_pow_mul_of_pow_eq_pow hζΩ hα0 (((hroot r).1 hr).trans hα.symm)
    rw [hi]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ ζ) i) (mem_adjoin_simple_self F α)
  have : IsSplittingField F (adjoin F (p.rootSet Ω)) p := adjoin_rootSet_isSplittingField hsplit
  have : Normal F (adjoin F (p.rootSet Ω)) := Normal.of_isSplittingField p
  rw [heq]
  exact isGalois_iff.2 ⟨inferInstance, inferInstance⟩

/-- **The degree of `F(π^{1/ℓ^e})`** is `ℓ ^ e` when `F` contains a primitive `ℓ ^ e`-th root of
unity and `π` is not an `ℓ`-th power in `F`. -/
theorem finrank_adjoin_of_pow_eq [Algebra.IsSeparable F Ω] {ℓ e : ℕ} (hℓ : ℓ.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ e)) {π : F} (hπ : ∀ y : F, y ^ ℓ ≠ π) {α : Ω}
    (hα : α ^ (ℓ ^ e) = algebraMap F Ω π) : finrank F F⟮α⟯ = ℓ ^ e := by
  set n := ℓ ^ e with hn
  have : NeZero n := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hπ0 := ne_zero_of_forall_pow_ne hℓ hπ
  have := isGalois_adjoin_of_pow_eq hζ hα hπ0
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional F F⟮α⟯ := adjoin.finiteDimensional hint
  set d := finrank F F⟮α⟯ with hd
  have hdn : d ≤ n := by
    rw [hd, adjoin.finrank hint]
    calc _ ≤ (X ^ n - C π : F[X]).natDegree :=
          natDegree_le_of_dvd (minpoly.dvd F α (p := X ^ n - C π) (by simp [hα]))
            (X_pow_sub_C_ne_zero (NeZero.pos n) π)
      _ = n := natDegree_X_pow_sub_C
  have hdpos : 0 < d := finrank_pos
  set α' : F⟮α⟯ := AdjoinSimple.gen F α with hα'def
  have hα' : α' ^ n = algebraMap F F⟮α⟯ π := Subtype.ext (by simpa [α'] using hα)
  have hζM := hζ.map_of_injective (algebraMap F F⟮α⟯).injective
  have hα'0 := ne_zero_of_pow_eq_algebraMap hα' hπ0
  -- the Kummer character
  have hc : ∀ σ : Gal(F⟮α⟯/F), ∃ i : ℕ, σ α' = algebraMap F F⟮α⟯ (ζ ^ i) * α' := by
    intro σ
    obtain ⟨i, -, hi⟩ := exists_eq_pow_mul_of_pow_eq_pow hζM hα'0
      (by rw [← map_pow σ, hα', AlgEquiv.commutes])
    exact ⟨i, by rw [hi, map_pow]⟩
  choose c hcσ using hc
  set χ : Gal(F⟮α⟯/F) → F := fun σ => ζ ^ c σ with hχ
  have hχσ : ∀ σ, σ α' = algebraMap F F⟮α⟯ (χ σ) * α' := hcσ
  have hχmul : ∀ σ τ, χ (σ * τ) = χ σ * χ τ := by
    intro σ τ
    apply (algebraMap F F⟮α⟯).injective
    apply mul_right_cancel₀ hα'0
    rw [← hχσ, AlgEquiv.mul_apply, hχσ τ, map_mul, AlgEquiv.commutes, hχσ σ, map_mul]
    ring
  have hχ1 : χ 1 = 1 := by
    apply (algebraMap F F⟮α⟯).injective
    apply mul_right_cancel₀ hα'0
    rw [← hχσ, map_one, one_mul]
    rfl
  have hχpow : ∀ σ (k : ℕ), χ (σ ^ k) = χ σ ^ k := by
    intro σ k
    induction k with
    | zero => rw [pow_zero, pow_zero, hχ1]
    | succ k ih => rw [pow_succ, hχmul, ih, pow_succ]
  have hχd : ∀ σ, χ σ ^ d = 1 := by
    intro σ
    rw [← hχpow, hd, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', hχ1]
  have hfix : ∀ σ : Gal(F⟮α⟯/F), σ (α' ^ d) = α' ^ d := by
    intro σ
    rw [map_pow, hχσ, mul_pow, ← map_pow, hχd, map_one, one_mul]
  obtain ⟨c₀, hc₀⟩ : α' ^ d ∈ Set.range (algebraMap F F⟮α⟯) := by
    rw [← IntermediateField.mem_bot]
    exact (IsGalois.mem_bot_iff_fixed _).2 hfix
  -- the Bézout argument
  obtain ⟨j, hje, hj⟩ := (Nat.dvd_prime_pow hℓ).1 (Nat.gcd_dvd_right d n)
  by_contra hne
  have hdlt : d < n := lt_of_le_of_ne hdn hne
  have hjlt : j < e := by
    rcases lt_or_eq_of_le hje with h | rfl
    · exact h
    · exfalso
      have : n ∣ d := by rw [hn, ← hj]; exact Nat.gcd_dvd_left d n
      exact absurd (Nat.le_of_dvd hdpos this) (not_le.2 hdlt)
  have hbez := Nat.gcd_eq_gcd_ab d n
  rw [hj] at hbez
  set A := Nat.gcdA d n
  set B := Nat.gcdB d n
  have hpow : α' ^ ((ℓ ^ j : ℕ) : ℤ) = algebraMap F F⟮α⟯ (c₀ ^ A * π ^ B) := by
    rw [hbez, zpow_add₀ hα'0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hc₀, hα',
      map_mul, map_zpow₀, map_zpow₀]
  have hX : algebraMap F F⟮α⟯ (c₀ ^ A * π ^ B) = α' ^ (ℓ ^ j) := by rw [← hpow, zpow_natCast]
  have he : ℓ ^ j * (ℓ ^ (e - j - 1) * ℓ) = n := by
    rw [hn, ← pow_succ, ← pow_add]
    congr 1
    omega
  have hπpow : algebraMap F F⟮α⟯ π =
      algebraMap F F⟮α⟯ (((c₀ ^ A * π ^ B) ^ ℓ ^ (e - j - 1)) ^ ℓ) := by
    rw [map_pow, map_pow, hX, ← pow_mul, ← pow_mul, he, hα']
  exact hπ _ ((algebraMap F F⟮α⟯).injective hπpow).symm

/-- **A cyclic extension of prime degree `ℓ` contains an `ℓ`-th root of `π`** when `π` generates
`Fˣ / Fˣ^ℓ` and `F` contains a primitive `ℓ`-th root of unity (Kummer theory). -/
theorem exists_pow_eq_of_isCyclic {ℓ : ℕ} (hℓ : ℓ.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
    {π : F} (hgen : ∀ a : F, a ≠ 0 → ∃ (i : ℕ) (b : F), a = π ^ i * b ^ ℓ)
    (M : Type*) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (hM : finrank F M = ℓ) : ∃ β : M, β ^ ℓ = algebraMap F M π := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsCyclic Gal(M/F) := isCyclic_of_prime_card (by rw [IsGalois.card_aut_eq_finrank, hM])
  obtain ⟨α, ⟨a, ha⟩, htop⟩ := exists_root_adjoin_eq_top_of_isCyclic F M
    (by rw [hM]; exact ⟨ζ, (mem_primitiveRoots hℓ.pos).2 hζ⟩)
  rw [hM] at ha
  have hbot : (⊥ : IntermediateField F M) ≠ ⊤ := by
    rw [ne_eq, IntermediateField.bot_eq_top_iff_finrank_eq_one, hM]
    exact hℓ.one_lt.ne'
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hbot (by rw [← htop, IntermediateField.adjoin_zero])
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm] at ha
    exact hα0 (pow_eq_zero_iff hℓ.ne_zero |>.1 ha)
  obtain ⟨i, b, hab⟩ := hgen a ha0
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hℓ.ne_zero, mul_zero] at hab
    exact ha0 hab
  have hζM := hζ.map_of_injective (algebraMap F M).injective
  by_cases hi : ℓ ∣ i
  · exfalso
    obtain ⟨k, rfl⟩ := hi
    have hx0 : algebraMap F M (π ^ k * b) ≠ 0 := by
      rw [ne_eq, map_eq_zero, mul_eq_zero, not_or]
      refine ⟨fun h => ?_, hb0⟩
      have h0 : π ^ (ℓ * k) = 0 := by rw [pow_mul', h, zero_pow hℓ.ne_zero]
      rw [h0, zero_mul] at hab
      exact ha0 hab
    obtain ⟨m, -, hm⟩ := exists_eq_pow_mul_of_pow_eq_pow hζM hx0 (β := α)
      (by rw [← ha, hab, ← map_pow, mul_pow, ← pow_mul, mul_comm ℓ k])
    apply hbot
    rw [← htop, eq_comm, IntermediateField.adjoin_simple_eq_bot_iff, hm, ← map_pow, ← map_mul]
    exact IntermediateField.algebraMap_mem _ _
  · obtain ⟨s, t, hst⟩ : ∃ s t : ℕ, s * i = ℓ * t + 1 := by
      have hcop : Nat.Coprime i ℓ :=
        Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hi)
      obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
      refine ⟨s, s * i / ℓ, ?_⟩
      have := Nat.div_add_mod (s * i) ℓ
      rw [mul_comm i s] at hs
      omega
    have hπ0 : algebraMap F M π ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      rintro rfl
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact hi (dvd_zero ℓ)
      · rw [zero_pow hipos.ne', zero_mul] at hab
        exact ha0 hab
    refine ⟨(α / algebraMap F M b) ^ s / algebraMap F M π ^ t, ?_⟩
    rw [div_pow, ← pow_mul, mul_comm s ℓ, pow_mul, div_pow, ← ha, hab, map_mul, map_pow,
      map_pow, mul_div_cancel_right₀ _ (pow_ne_zero _ (by rwa [ne_eq, map_eq_zero])), ← pow_mul,
      ← pow_mul, mul_comm i s, hst, pow_succ, mul_comm t ℓ,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hπ0)]

variable [IsGalois F Ω]

/-- The fixed field of an open subgroup of `Gal(Ω/F)` is finite over `F`, of degree the index. -/
theorem finiteDimensional_fixedField_and_index_eq (U : OpenSubgroup Gal(Ω/F)) :
    FiniteDimensional F (fixedField (U : Subgroup Gal(Ω/F))) ∧
      (U : Subgroup Gal(Ω/F)).index = finrank F (fixedField (U : Subgroup Gal(Ω/F))) := by
  have hfix := fixingSubgroup_fixedField_openSubgroup U
  refine ⟨?_, ?_⟩
  · rw [← InfiniteGalois.isOpen_iff_finite]
    change IsOpen ((fixedField (U : Subgroup Gal(Ω/F))).fixingSubgroup : Set Gal(Ω/F))
    rw [hfix]
    exact U.isOpen'
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]

/-- **`Gal(Ω/F)` is pro-`ℓ`** when every finite subextension of `Ω/F` has `ℓ`-power degree. -/
theorem isProPGroup_gal {ℓ : ℕ}
    (hdeg : ∀ M : IntermediateField F Ω, FiniteDimensional F M → ∃ k, finrank F M = ℓ ^ k) :
    IsProPGroup ℓ Gal(Ω/F) := by
  intro N
  obtain ⟨hfd, hidx⟩ := finiteDimensional_fixedField_and_index_eq N.toOpenSubgroup
  obtain ⟨k, hk⟩ := hdeg _ hfd
  refine IsPGroup.of_card (n := k) ?_
  change N.toSubgroup.index = ℓ ^ k
  exact hidx.trans hk

/-- **The prime base of `Gal(Ω/F)` for Kummer data.** Let `ℓ` be a prime and `F` a field with
primitive `ℓ ^ e`-th roots of unity for all `e`, an element `π` which is not an `ℓ`-th power and
such that every nonzero element is `π ^ i * b ^ ℓ`, and with every finite subextension of the
separable closure `Ω` of `ℓ`-power degree. Then `Gal(Ω/F) ≅ ℤ_ℓ` has a prime base, so its
cohomology with torsion coefficients vanishes in degrees `≥ 2`. -/
theorem hasPrimeBase_gal_of_kummer [IsSepClosed Ω] {ℓ : ℕ} (hℓ : ℓ.Prime) {π : F}
    (hζ : ∀ e : ℕ, ∃ ζ : F, IsPrimitiveRoot ζ (ℓ ^ e)) (hπ : ∀ y : F, y ^ ℓ ≠ π)
    (hgen : ∀ a : F, a ≠ 0 → ∃ (i : ℕ) (b : F), a = π ^ i * b ^ ℓ)
    (hdeg : ∀ M : IntermediateField F Ω, FiniteDimensional F M → ∃ k, finrank F M = ℓ ^ k) :
    Stacks.GroupCohomology.HasPrimeBase Gal(Ω/F) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hroot : ∀ e : ℕ, ∃ α : Ω, α ^ (ℓ ^ e) = algebraMap F Ω π := by
    intro e
    obtain ⟨ζ, hζe⟩ := hζ e
    have : NeZero (ℓ ^ e) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
    have : NeZero ((ℓ ^ e : ℕ) : F) := hζe.neZero'
    have : NeZero ((ℓ ^ e : ℕ) : Ω) := ⟨by
      rw [← map_natCast (algebraMap F Ω), ne_eq, map_eq_zero]
      exact NeZero.ne _⟩
    exact IsSepClosed.exists_pow_nat_eq _ _
  obtain ⟨ζ₁, hζ₁⟩ := hζ 1
  rw [pow_one] at hζ₁
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hζ₁Ω := hζ₁.map_of_injective (algebraMap F Ω).injective
  obtain ⟨β₀, hβ₀⟩ := hroot 1
  rw [pow_one] at hβ₀
  have hπ0 := ne_zero_of_forall_pow_ne hℓ hπ
  have hdeg₀ : finrank F F⟮β₀⟯ = ℓ := by
    simpa using finrank_adjoin_of_pow_eq (e := 1) hℓ (by rwa [pow_one]) hπ (by rwa [pow_one])
  -- every open subgroup of index `ℓ` fixes `F(β₀)`
  have hfixed : ∀ U : OpenSubgroup Gal(Ω/F), (U : Subgroup Gal(Ω/F)).index = ℓ →
      fixedField (U : Subgroup Gal(Ω/F)) = F⟮β₀⟯ := by
    intro U hU
    set M := fixedField (U : Subgroup Gal(Ω/F))
    obtain ⟨hfd, hidx⟩ := finiteDimensional_fixedField_and_index_eq U
    have hMℓ : finrank F M = ℓ := hidx.symm.trans hU
    -- `U` is normal
    have hUn : (U : Subgroup Gal(Ω/F)).Normal := by
      obtain ⟨N, hNU⟩ :=
        ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one U.isOpen' U.one_mem
      have : Finite (Gal(Ω/F) ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
      set f := QuotientGroup.mk' N.toSubgroup
      have hker : f.ker ≤ (U : Subgroup Gal(Ω/F)) := by
        rw [QuotientGroup.ker_mk']
        exact fun x hx => hNU hx
      have hcomap := Subgroup.comap_map_eq_self hker
      have hidxH : ((U : Subgroup Gal(Ω/F)).map f).index = ℓ := by
        rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hcomap, hU]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isProPGroup_gal hdeg N)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        have := Subgroup.index_dvd_card ((U : Subgroup Gal(Ω/F)).map f)
        rw [hidxH, hk] at this
        exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
      have hn : ((U : Subgroup Gal(Ω/F)).map f).Normal :=
        Subgroup.normal_of_index_eq_minFac_card (by rw [hidxH, hk, Nat.Prime.pow_minFac hℓ hk0])
      rw [← hcomap]
      exact hn.comap f
    have : IsGalois F M := by
      rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_fixedField_openSubgroup U]
      exact hUn
    obtain ⟨β, hβ⟩ := exists_pow_eq_of_isCyclic hℓ hζ₁ hgen M hMℓ
    have hβΩ : (β : Ω) ^ ℓ = algebraMap F Ω π := by
      have := congrArg (fun x : M => (x : Ω)) hβ
      simpa using this
    obtain ⟨i, -, hi⟩ := exists_eq_pow_mul_of_pow_eq_pow hζ₁Ω (α := (β : Ω))
      (ne_zero_of_pow_eq_algebraMap hβΩ hπ0)
      (β := β₀) (by rw [hβ₀, hβΩ])
    have hle : F⟮β₀⟯ ≤ M := by
      rw [adjoin_simple_le_iff, hi]
      exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ ζ₁) i) β.2
    exact (IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hdeg₀, hMℓ])).symm
  refine Stacks.GroupCohomology.hasPrimeBase_of_isProPGroup_of_unique_index_eq hℓ
    (isProPGroup_gal hdeg) (fun U V hU hV => ?_) (fun e => ?_)
  · apply OpenSubgroup.toSubgroup_injective
    rw [← fixingSubgroup_fixedField_openSubgroup U, ← fixingSubgroup_fixedField_openSubgroup V,
      hfixed U hU, hfixed V hV]
  · obtain ⟨α, hα⟩ := hroot e
    obtain ⟨ζ, hζe⟩ := hζ e
    have : NeZero (ℓ ^ e) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
    have := isGalois_adjoin_of_pow_eq hζe hα hπ0
    have hfd : FiniteDimensional F F⟮α⟯ :=
      adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral α)
    refine ⟨{ toSubgroup := F⟮α⟯.fixingSubgroup
              isOpen' := (InfiniteGalois.isOpen_iff_finite _).2 hfd
              isNormal' := (InfiniteGalois.normal_iff_isGalois _).2 inferInstance }, ?_⟩
    change F⟮α⟯.fixingSubgroup.index = ℓ ^ e
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact finrank_adjoin_of_pow_eq hℓ hζe hπ hα

end Stacks.GaloisCohomology

end
