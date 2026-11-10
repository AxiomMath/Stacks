module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Nakayama

/-!
# Characteristic and Hilbert functions over a Noetherian local ring

Fix a Noetherian local ring `(R, m)` and an ideal `I ⊆ R` with `√I = m`. For a finite `R`-module
`M`, the characteristic function is `χ_{I,M}(n) = length_R (M / I^(n+1) M)` and the Hilbert
function is `φ_{I,M}(n) = length_R (I^n M / I^(n+1) M)`, for `n ≥ 0`.

## Main definitions

* `chi`, `charFn`: the characteristic function `χ_{I,M}`, valued in `ℕ∞`.
* `hilbertFn`: the Hilbert function `φ_{I,M}`, valued in `ℕ∞`.
* `HilbertSamuel.hilbertSamuelFunction`: `n ↦ length_R (M / I^(n+1) M)`, valued in `ℕ`.
* `HilbertSamuel.IsHilbertSamuelPoly`: a polynomial in `ℚ[X]` agreeing with
  `HilbertSamuel.hilbertSamuelFunction` for all large `n`.

## Main results

* `chi_bounds_of_quotient_finiteLength`: if `M' ⊆ M` are finite `R`-modules with `M / M'` of
  finite length, there are `c₁, c₂ ∈ ℕ` with
  `c₁ + χ_{I,M'}(n - c₂) ≤ χ_{I,M}(n) ≤ c₁ + χ_{I,M'}(n)` for all `n ≥ c₂`.
* `additivity_of_characteristic_and_hilbert_functions`: for a short exact sequence
  `0 → M' → M → M'' → 0` of finite `R`-modules there are a submodule `N ⊆ M'` of finite colength
  `l` and `c ∈ ℕ` with `χ_{I,M}(n) = χ_{I,M''}(n) + χ_{I,N}(n - c) + l` and
  `φ_{I,M}(n) = φ_{I,M''}(n) + φ_{I,N}(n - c)` for all `n ≥ c`.
* `HilbertSamuel.degree_sub_lt`: if `M` does not have finite length and `M' ⊆ M` has finite
  colength, the difference of the Hilbert–Samuel polynomials of `M` and `M'` has degree less than
  the degree of each of them.
-/

@[expose] public section

/-- The characteristic function `χ_{I,M}(n) = length_R (M / I^(n+1) M)`, valued in `ℕ∞`, where
`I^(n+1) M` is the submodule `I ^ (n + 1) • ⊤`. -/
noncomputable def chi {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ ((I ^ (n + 1)) • (⊤ : Submodule R M)))

/-- Length is antitone in the submodule being quotiented out: if `A ≤ B`, then
`length_R (M ⧸ B) ≤ length_R (M ⧸ A)`. -/
theorem length_quotient_antitone
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {A B : Submodule R M} (h : A ≤ B) :
    Module.length R (M ⧸ B) ≤ Module.length R (M ⧸ A) :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

/-- **Additivity of length.** For submodules `A ≤ B` of `M`,
`length(M/A) = length(B/A) + length(M/B)`, where `B/A` is `↥B ⧸ comap B.subtype A`. -/
theorem length_quotient_add_of_le
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {A B : Submodule R M} (h : A ≤ B) :
    Module.length R (M ⧸ A)
      = Module.length R (B ⧸ Submodule.comap B.subtype A) + Module.length R (M ⧸ B) := by
  set f : (B ⧸ Submodule.comap B.subtype A) →ₗ[R] (M ⧸ A) :=
    (Submodule.comap B.subtype A).mapQ A B.subtype le_rfl with hf
  set g : (M ⧸ A) →ₗ[R] (M ⧸ B) := Submodule.factor h with hg
  have hinj : Function.Injective f := by
    rw [hf, ← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp
  have hfrange : f.range = Submodule.map A.mkQ B := by
    rw [hf, LinearMap.range_eq_map, ← (Submodule.comap B.subtype A).range_mkQ,
      LinearMap.range_eq_map, ← Submodule.map_comp, Submodule.mapQ_mkQ,
      Submodule.map_comp, ← LinearMap.range_eq_map, Submodule.range_subtype]
  have hgker : g.ker = Submodule.map A.mkQ B := by
    rw [hg, Submodule.factor, Submodule.ker_mapQ]
    simp
  exact Module.length_eq_add_of_exact f g hinj (Submodule.factor_surjective h) <| by
    rw [LinearMap.exact_iff, hgker, hfrange]

/-- An ideal whose radical is the maximal ideal lies in the Jacobson radical. -/
private theorem le_jacobson_bot_of_radical_eq
    {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
    (hI : I.radical = IsLocalRing.maximalIdeal R) : I ≤ (⊥ : Ideal R).jacobson :=
  (Ideal.le_radical.trans hI.le).trans (IsLocalRing.maximalIdeal_le_jacobson ⊥)

/-- If `I` is an ideal of definition and `M / M'` has finite length, then a power of `I`
annihilates `M / M'`, i.e. `I^c₂ • ⊤ ≤ M'` for some `c₂`. -/
theorem c2_existence
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : IsIdealOfDefinition I)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (M' : Submodule R M) (hlen : Module.length R (M ⧸ M') < ⊤) :
    ∃ c₂ : ℕ, (I ^ c₂) • (⊤ : Submodule R M) ≤ M' := by
  set N := M ⧸ M'
  obtain ⟨hNoeth, hArt⟩ : IsNoetherian R N ∧ IsArtinian R N :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen.ne)
  have hstab : ∃ k, I ^ (k + 1) • (⊤ : Submodule R N) = I ^ k • (⊤ : Submodule R N) := by
    let f : ℕ →o (Submodule R N)ᵒᵈ :=
      ⟨fun n => OrderDual.toDual (I ^ n • (⊤ : Submodule R N)),
        fun _ _ hab => Submodule.smul_mono (Ideal.pow_le_pow_right hab) le_rfl⟩
    obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes f
    exact ⟨k, (hk (k + 1) (by omega)).symm⟩
  obtain ⟨k, hk⟩ := hstab
  have hbot : I ^ k • (⊤ : Submodule R N) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_
      (le_jacobson_bot_of_radical_eq hI)
    rw [← mul_smul, ← pow_succ', hk]
  refine ⟨k, ?_⟩
  have hmap : (I ^ k • (⊤ : Submodule R M)).map M'.mkQ ≤ ⊥ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, hbot]
  rwa [Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ] at hmap

/-- For any linear map `f : M' → M`, `length (M' / comap f A) ≤ length (M / A)`. -/
private theorem length_comap_quotient_le
    {R : Type*} [CommRing R] {M' M : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M]
    [Module R M] (f : M' →ₗ[R] M) (A : Submodule R M) :
    Module.length R (M' ⧸ A.comap f) ≤ Module.length R (M ⧸ A) :=
  Module.length_le_of_injective ((A.comap f).mapQ A f le_rfl) <| by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.mkQ_map_self]

/-- Pulling `J • ⊤` back along `N.subtype` is bounded below by `J • ⊤` in `N`. -/
private theorem smul_top_le_comap_subtype_smul_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (J : Ideal R) :
    J • (⊤ : Submodule R N) ≤ (J • (⊤ : Submodule R M)).comap N.subtype := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
    Submodule.range_subtype]
  exact Submodule.smul_mono le_rfl le_top

/-- If `N ⊓ A ≤ J • N`, then `A` pulled back to `N` lies in `J • ⊤`. -/
private theorem comap_subtype_le_smul_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (N A : Submodule R M) (J : Ideal R) (h : N ⊓ A ≤ J • N) :
    A.comap N.subtype ≤ J • (⊤ : Submodule R N) := by
  rwa [← Submodule.map_le_map_iff_of_injective N.injective_subtype, Submodule.map_comap_subtype,
    Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]

/-- Let `(R, m, k)` be a Noetherian local ring, `I ⊆ R` an ideal of definition, and
`M' ⊆ M` finite `R`-modules with `M / M'` of finite length. Then there are
constants `c₁, c₂ ∈ ℕ` such that for all `n ≥ c₂`,
`c₁ + χ_{I,M'}(n - c₂) ≤ χ_{I,M}(n) ≤ c₁ + χ_{I,M'}(n)`. -/
@[stacks 00K5]
theorem chi_bounds_of_quotient_finiteLength
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : IsIdealOfDefinition I)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (M' : Submodule R M) (hlen : Module.length R (M ⧸ M') < ⊤) :
    ∃ c₁ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
      (c₁ : ℕ∞) + chi I M' (n - c₂) ≤ chi I M n ∧
      chi I M n ≤ (c₁ : ℕ∞) + chi I M' n := by
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℕ, (c₁ : ℕ∞) = Module.length R (M ⧸ M') :=
    ⟨(Module.length R (M ⧸ M')).toNat, by
      rw [ENat.natCast_toNat (by simpa using hlen.ne)]⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, (I ^ c₂) • (⊤ : Submodule R M) ≤ M' :=
    c2_existence I hI M' hlen
  refine ⟨c₁, c₂, fun n hn => ?_⟩
  set A : Submodule R M := (I ^ (n + 1)) • (⊤ : Submodule R M) with hA
  have hAle : A ≤ M' :=
    le_trans (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl) hc₂
  have h_eq : chi I M n
      = (c₁ : ℕ∞) + Module.length R (M' ⧸ Submodule.comap M'.subtype A) := by
    rw [chi, ← hA, length_quotient_add_of_le hAle, hc₁, add_comm]
  have h_upper : Module.length R (M' ⧸ Submodule.comap M'.subtype A) ≤ chi I M' n :=
    length_quotient_antitone (smul_top_le_comap_subtype_smul_top M' _)
  have h_lower : chi I M' (n - c₂)
      ≤ Module.length R (M' ⧸ Submodule.comap M'.subtype A) := by
    refine length_quotient_antitone (comap_subtype_le_smul_top M' A _ ?_)
    rw [inf_eq_right.mpr hAle, hA, show n + 1 = n - c₂ + 1 + c₂ by omega, pow_add, mul_smul]
    exact Submodule.smul_mono le_rfl hc₂
  refine ⟨?_, ?_⟩ <;> rw [h_eq] <;> gcongr

/-!
## Additivity of the characteristic and Hilbert functions
-/

@[expose] public section

/-!
### Lengths of submodule quotients
-/
namespace StacksHelpers

/-- Length additivity for a chain `B ≤ A` of submodules of `M`:
`length (M/B) = length (A / (B.comap A.subtype)) + length (M/A)`. -/
theorem length_chain {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (B A : Submodule R M) (h : B ≤ A) :
    Module.length R (M ⧸ B)
      = Module.length R (A ⧸ B.comap A.subtype) + Module.length R (M ⧸ A) :=
  length_quotient_add_of_le h

/-- For an exact sequence `M' → M → M'' → 0` and a submodule `A ⊆ M`,
`length (M/A) = length (M' / comap f A) + length (M'' / map g A)`. -/
theorem length_quotient_ses {R : Type*} [CommRing R]
    {M' M M'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [AddCommGroup M''] [Module R M''] (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (A : Submodule R M) :
    Module.length R (M ⧸ A)
      = Module.length R (M' ⧸ A.comap f) + Module.length R (M'' ⧸ A.map g) := by
  refine Module.length_eq_add_of_exact ((A.comap f).mapQ A f le_rfl)
    (A.mapQ (A.map g) g (Submodule.le_comap_map _ _)) ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.mkQ_map_self]
  · rw [← LinearMap.range_eq_top, Submodule.range_mapQ, LinearMap.range_eq_top.mpr hg,
      Submodule.map_top, Submodule.range_mkQ]
  · rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_map_eq, hfg.linearMap_ker_eq,
      Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.range_mapQ]

/-- For a surjective `g`, `map g (I^k • ⊤) = I^k • ⊤`. -/
theorem map_pow_smul_top {R : Type*} [CommRing R] (I : Ideal R)
    {M M'' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M''] [Module R M'']
    (g : M →ₗ[R] M'') (hg : Function.Surjective g) (k : ℕ) :
    Submodule.map g (I ^ k • (⊤ : Submodule R M)) = I ^ k • (⊤ : Submodule R M'') := by
  rw [Submodule.map_smul'']
  congr 1
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr hg]

/-- For a submodule `N`, `(I^k • N).comap N.subtype = I^k • ⊤` inside `↥N`. -/
theorem comap_subtype_smul {R : Type*} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) (k : ℕ) :
    (I ^ k • N).comap N.subtype = I ^ k • (⊤ : Submodule R N) := by
  have hmap : Submodule.map N.subtype (I ^ k • (⊤ : Submodule R N)) = I ^ k • N := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← hmap, Submodule.comap_map_eq_of_injective N.injective_subtype]

/-- Artin–Rees in pulled-back form: for injective `f`, there is `c` with, for all
`m ≥ c`, `comap f (I^m • ⊤) = I^(m-c) • comap f (I^c • ⊤)`. -/
theorem comap_pow_smul_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {M' M : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : M' →ₗ[R] M) (hf : Function.Injective f) :
    ∃ c : ℕ, ∀ m ≥ c,
      (I ^ m • (⊤ : Submodule R M)).comap f
        = I ^ (m - c) • ((I ^ c • (⊤ : Submodule R M)).comap f) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨c, fun m hm => ?_⟩
  have key := hc m hm
  have hcr : (LinearMap.range f).comap f = ⊤ := by
    rw [eq_top_iff]; intro x _; exact LinearMap.mem_range_self f x
  have e1 : (I ^ m • (⊤ : Submodule R M)).comap f
      = (I ^ m • (⊤ : Submodule R M) ⊓ LinearMap.range f).comap f := by
    rw [Submodule.comap_inf, hcr, inf_top_eq]
  rw [e1, key]
  have e2 : I ^ c • (⊤ : Submodule R M) ⊓ LinearMap.range f
      = Submodule.map f ((I ^ c • (⊤ : Submodule R M)).comap f) := by
    rw [Submodule.map_comap_eq, inf_comm]
  rw [e2, ← Submodule.map_smul'', Submodule.comap_map_eq_of_injective hf]

end StacksHelpers

/-- The Hilbert function of `M` with respect to `I`:
`φ_{I,M}(n) = length_R (I^n M / I^{n+1} M)`, valued in `ℕ∞`. -/
noncomputable def hilbertFn (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℕ∞ :=
  let A : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let B : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  Module.length R (A ⧸ (B.comap A.subtype))

/-- The characteristic function of `M` with respect to `I`:
`χ_{I,M}(n) = length_R (M / I^{n+1} M)`, valued in `ℕ∞`. -/
noncomputable def charFn (R : Type*) [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))

/-- Step relation between `χ` and `φ`: for every module `X` and every `n`,
`χ_{I,X}(n+1) = φ_{I,X}(n+1) + χ_{I,X}(n)`. -/
theorem charFn_succ (R : Type*) [CommRing R] (I : Ideal R)
    (X : Type*) [AddCommGroup X] [Module R X] (n : ℕ) :
    charFn R I X (n + 1) = hilbertFn R I X (n + 1) + charFn R I X n := by
  simp only [hilbertFn, charFn]
  exact StacksHelpers.length_chain _ _
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))

/-- If `A = ⊤` then `length (↥A ⧸ B.comap A.subtype) = length (X ⧸ B)`. -/
theorem length_quot_comap_top (R : Type*) [CommRing R]
    (X : Type*) [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hA : A = ⊤) :
    Module.length R (↥A ⧸ (B.comap A.subtype)) = Module.length R (X ⧸ B) := by
  subst hA
  apply LinearEquiv.length_eq
  refine Submodule.Quotient.equiv (B.comap (⊤ : Submodule R X).subtype) B
    Submodule.topEquiv ?_
  have hmapf : Submodule.map
      (↑(Submodule.topEquiv : (⊤ : Submodule R X) ≃ₗ[R] X) :
        (⊤ : Submodule R X) →ₗ[R] X) (B.comap (⊤ : Submodule R X).subtype)
      = Submodule.map (⊤ : Submodule R X).subtype (B.comap (⊤ : Submodule R X).subtype) := rfl
  rw [hmapf, Submodule.map_comap_eq, Submodule.range_subtype, top_inf_eq]

/-- `φ_{I,X}(0) = χ_{I,X}(0)`. -/
theorem hilbertFn_zero (R : Type*) [CommRing R] (I : Ideal R)
    (X : Type*) [AddCommGroup X] [Module R X] :
    hilbertFn R I X 0 = charFn R I X 0 := by
  simp only [hilbertFn, charFn]
  exact length_quot_comap_top R X _ _
    (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul])

/-- For a Noetherian local ring with `√I = m` and finite `X`, `length (X / I^k•⊤) ≠ ⊤`. -/
@[ega "0 16.2.1" "special case", sga "6 X 1.1.2" "special case"]
theorem length_quot_pow_ne_top
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] (k : ℕ) :
    Module.length R (X ⧸ (I ^ k • (⊤ : Submodule R X))) ≠ (⊤ : ℕ∞) := by
  set N : Submodule R X := I ^ k • (⊤ : Submodule R X) with hN
  have hartinianRing : IsArtinianRing (R ⧸ I ^ k) := by
    rcases Nat.eq_zero_or_pos k with hc0 | hcpos
    · subst hc0; rw [pow_zero, Ideal.one_eq_top]; infer_instance
    · have hcne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hcpos
      rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
      refine ⟨inferInstance, ?_⟩
      rw [Ring.krullDimLE_zero_iff]
      intro P hP
      set Q : Ideal R := P.comap (Ideal.Quotient.mk (I ^ k)) with hQ
      have hQp : Q.IsPrime := hP.comap _
      have hIcQ : I ^ k ≤ Q := by
        rw [hQ]; intro x hx
        simp only [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact P.zero_mem
      have hmQ : IsLocalRing.maximalIdeal R ≤ Q := by
        rw [← hI, ← Ideal.radical_pow (I := I) hcne]
        exact hQp.radical_le_iff.mpr hIcQ
      have hQm : Q = IsLocalRing.maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hQp.ne_top) hmQ
      have hQmax : Q.IsMaximal := hQm ▸ (IsLocalRing.maximalIdeal.isMaximal R)
      have hfieldQ : IsField (R ⧸ Q) :=
        (Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hQmax
      have e : (R ⧸ I ^ k) ⧸ Ideal.map (Ideal.Quotient.mk (I ^ k)) Q ≃+* R ⧸ Q :=
        DoubleQuot.quotQuotEquivQuotOfLE hIcQ
      rw [hQ, Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I ^ k))
        (Ideal.Quotient.mk_surjective)] at e
      rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
      exact MulEquiv.isField hfieldQ e.toMulEquiv
  have hArt : IsArtinian R (X ⧸ N) := by
    have : Module.Finite (R ⧸ I ^ k) (X ⧸ N) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ I ^ k) (X ⧸ N)
    exact isArtinian_of_surjective_algebraMap (S := R) (R := R ⧸ I ^ k)
      Ideal.Quotient.mk_surjective
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, hArt⟩

/-- `χ_{I,X}(k) ≠ ⊤` for finite `X` over a Noetherian local ring with `√I = m`. -/
theorem charFn_ne_top
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] (k : ℕ) :
    charFn R I X k ≠ (⊤ : ℕ∞) :=
  length_quot_pow_ne_top R I hI X (k + 1)

/-- `φ_{I,X}(k) ≠ ⊤` for finite `X` over a Noetherian local ring with `√I = m`. -/
theorem hilbertFn_ne_top
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (X : Type*) [AddCommGroup X] [Module R X] [Module.Finite R X] (k : ℕ) :
    hilbertFn R I X k ≠ (⊤ : ℕ∞) := by
  rcases k with _ | m
  · rw [hilbertFn_zero]
    exact charFn_ne_top R I hI X 0
  · exact fun htop => charFn_ne_top R I hI X (m + 1) (by rw [charFn_succ, htop, top_add])

/-- Given a short exact sequence `0 → M' → M → M'' → 0` of finite `R`-modules over a
Noetherian local ring `(R, m)` and an ideal `I` with `√I = m`, there are a submodule
`N ⊆ M'` of finite colength `l = length_R (M'/N)` and an integer `c ≥ 0` such that for
all `n ≥ c`
  `χ_{I,M}(n) = χ_{I,M''}(n) + χ_{I,N}(n - c) + l`  and
  `φ_{I,M}(n) = φ_{I,M''}(n) + φ_{I,N}(n - c)`. -/
@[stacks 00K6]
theorem additivity_of_characteristic_and_hilbert_functions
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (M' M M'' : Type*)
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    ∃ (N : Submodule R M') (c : ℕ) (l : ℕ),
      Module.length R (M' ⧸ N) = (l : ℕ∞) ∧
      (∀ n ≥ c, charFn R I M n = charFn R I M'' n + charFn R I N (n - c) + (l : ℕ∞)) ∧
      (∀ n ≥ c, hilbertFn R I M n = hilbertFn R I M'' n + hilbertFn R I N (n - c)) := by
  obtain ⟨c, hc⟩ := StacksHelpers.comap_pow_smul_eq I f hf
  set N : Submodule R M' := (I ^ c • (⊤ : Submodule R M)).comap f with hN
  have hfin : Module.length R (M' ⧸ N) ≠ ⊤ :=
    ne_top_of_le_ne_top (length_quot_pow_ne_top R I hI M c) (length_comap_quotient_le f _)
  obtain ⟨l, hl⟩ : ∃ l : ℕ, Module.length R (M' ⧸ N) = l := ⟨_, (ENat.natCast_toNat hfin).symm⟩
  have chi_id : ∀ m ≥ c,
      charFn R I M m = charFn R I M'' m + charFn R I (↥N) (m - c) + (l : ℕ∞) := by
    intro m hm
    have hses := StacksHelpers.length_quotient_ses f g hg hfg (I ^ (m + 1) • (⊤ : Submodule R M))
    rw [StacksHelpers.map_pow_smul_top I g hg, hc (m + 1) (by omega),
      StacksHelpers.length_chain _ N Submodule.smul_le_right, StacksHelpers.comap_subtype_smul,
      hl, show m + 1 - c = m - c + 1 by omega] at hses
    simp only [charFn]
    rw [hses]
    ac_rfl
  refine ⟨N, c, l, hl, chi_id, fun n hn => ?_⟩
  rcases eq_or_lt_of_le hn with rfl | hlt
  · rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · have hNtop : N = ⊤ := by
        rw [hN, pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.comap_top]
      have hl0 : (l : ℕ∞) = 0 := by
        rw [← hl, hNtop, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff]
      simpa [hilbertFn_zero, hl0] using chi_id 0 le_rfl
    · obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      have hbd : charFn R I M d = l + charFn R I M'' d := by
        have hses := StacksHelpers.length_quotient_ses f g hg hfg
          (I ^ (d + 1) • (⊤ : Submodule R M))
        rwa [StacksHelpers.map_pow_smul_top I g hg, ← hN, hl] at hses
      rw [Nat.sub_self, hilbertFn_zero]
      refine ENat.add_left_injective_of_ne_top (charFn_ne_top R I hI M d) ?_
      beta_reduce
      rw [← charFn_succ, chi_id (d + 1) le_rfl, Nat.sub_self, charFn_succ R I M'', hbd]
      ac_rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - c = m - c + 1 by omega]
    refine ENat.add_left_injective_of_ne_top (charFn_ne_top R I hI M m) ?_
    beta_reduce
    rw [← charFn_succ, chi_id (m + 1) hn, charFn_succ R I M'', show m + 1 - c = m - c + 1 by omega,
      charFn_succ R I (↥N), chi_id m (by omega)]
    ac_rfl

/-!
## Hilbert–Samuel polynomials of finite-colength submodules
-/

@[expose] public section

open Polynomial

namespace HilbertSamuel

variable {R : Type*} [CommRing R]

/-- An ideal `I ⊆ R` is an *ideal of definition* of a local ring `(R, m)` if its
radical equals the maximal ideal `m`. -/
@[ega "0 16.2.1", ega "III 4.3.13", ega "IV 21.13.12.1", ega "IV 6.1.3", sga "1 I 2.1"]
def IsIdealOfDefinition [IsLocalRing R] (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

/-- The Hilbert–Samuel function of a finite `R`-module `M` with respect to an ideal
`I` is `H_{I,M}(n) = length_R(M / I^{n+1} M)`, recorded as a natural number via
`ENat.toNat`. -/
noncomputable def hilbertSamuelFunction (I : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (n : ℕ) : ℕ :=
  (Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat

/-- A polynomial `χ ∈ Q[t]` *is the Hilbert–Samuel polynomial* of `M` with respect
to `I` if it agrees with the Hilbert–Samuel function for all sufficiently large
`n`, i.e. there is an `n₀` such that `χ(n) = H_{I,M}(n)` for all `n ≥ n₀`. -/
@[ega "0 16.2.1"]
def IsHilbertSamuelPoly (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (χ : ℚ[X]) : Prop :=
  ∀ᶠ (n : ℕ) in Filter.atTop, χ.eval (n : ℚ) = (hilbertSamuelFunction I M n : ℚ)

/-- An `R`-module `M` *has finite length* if `length_R(M) < ∞`. -/
@[sga "3 VIIB 0.4.2"]
def HasFiniteLength (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Prop :=
  Module.length R M < ⊤

/-- A submodule `M' ⊆ M` has *finite colength* if `length_R(M / M') < ∞`. -/
def HasFiniteColength {M : Type*} [AddCommGroup M] [Module R M] (M' : Submodule R M) :
    Prop :=
  Module.length R (M ⧸ M') < ⊤

/-- If `R` is a Noetherian local ring, `I` an ideal whose radical is the maximal
ideal, and `M` a finite `R`-module, then every quotient `M / I^{n+1} M` has finite
length. -/
@[ega "0 16.2.1" "finite length of M/q^nM", ega "IV 21.10.13" "(i)"]
lemma length_quotient_lt_top
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ) :
    Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) < ⊤ := by
  exact lt_top_iff_ne_top.mpr (length_quot_pow_ne_top R I hI M (n + 1))

open Filter in
/-- A polynomial of positive degree with nonnegative leading coefficient is not eventually
bounded above on `ℕ`. -/
theorem not_eventually_le_of_degree_pos (r : ℚ[X]) (hr : 0 < r.degree)
    (hlc : 0 ≤ r.leadingCoeff) (c : ℚ) : ¬ ∀ᶠ n : ℕ in atTop, r.eval (n : ℚ) ≤ c := fun h => by
  obtain ⟨n, h₁, h₂⟩ := (((tendsto_atTop_of_leadingCoeff_nonneg r hr hlc).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop c |>.and h).exists
  exact (h₁.trans_le h₂).false

open Filter in
/-- Polynomial comparison: eventual `≤` up to a constant implies degree `≤`. -/
theorem poly_cmp (p q : ℚ[X]) (c : ℚ)
    (h : ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ) + c)
    (hq : q ≠ 0) (hpc : 0 ≤ p.leadingCoeff) : p.degree ≤ q.degree := by
  by_contra hlt
  push Not at hlt
  have hqdeg : 0 ≤ q.degree := zero_le_degree_iff.mpr hq
  have hpd : 0 < p.degree := lt_of_le_of_lt hqdeg hlt
  set r := p - q with hr
  have hrdeg : r.degree = p.degree := by rw [hr]; exact degree_sub_eq_left_of_degree_lt hlt
  have hrnatdeg : r.natDegree = p.natDegree := natDegree_eq_of_degree_eq hrdeg
  have hrlead : r.leadingCoeff = p.leadingCoeff := by
    rw [leadingCoeff, leadingCoeff, hrnatdeg, hr, Polynomial.coeff_sub]
    rw [coeff_eq_zero_of_degree_lt (hlt.trans_le degree_le_natDegree), sub_zero]
  refine not_eventually_le_of_degree_pos r (by rw [hrdeg]; exact hpd)
    (by rw [hrlead]; exact hpc) c ?_
  filter_upwards [h] with n hn
  simp only [hr, eval_sub]
  linarith

open Filter in
/-- Polynomial comparison at the level of leading coefficients: eventual `≤` up to a
constant, between two polynomials of the same positive degree, forces the leading
coefficients to compare. -/
theorem leadingCoeff_cmp (p q : ℚ[X]) (c : ℚ)
    (h : ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ) + c)
    (hdeg : p.degree = q.degree) (hpd : 0 < p.degree) :
    p.leadingCoeff ≤ q.leadingCoeff := by
  by_contra hlt
  push Not at hlt
  have hp0 : p ≠ 0 := fun h0 => by simp [h0] at hpd
  set s := p - q with hs
  have hpnd : p.natDegree = q.natDegree := natDegree_eq_of_degree_eq hdeg
  have hscoeff : s.coeff p.natDegree = p.leadingCoeff - q.leadingCoeff := by
    rw [hs, Polynomial.coeff_sub, leadingCoeff, leadingCoeff, hpnd]
  have hsdeg_le : s.degree ≤ p.degree := by
    rw [hs]; exact le_trans (Polynomial.degree_sub_le p q) (by rw [hdeg]; simp)
  have hcoeff_pos : 0 < s.coeff p.natDegree := by rw [hscoeff]; linarith
  have hsdeg : s.degree = p.degree := by
    refine le_antisymm hsdeg_le ?_
    rw [Polynomial.degree_eq_natDegree hp0]
    exact le_degree_of_ne_zero hcoeff_pos.ne'
  have hsnd : s.natDegree = p.natDegree := natDegree_eq_of_degree_eq (by rw [hsdeg])
  have hslc : s.leadingCoeff = s.coeff p.natDegree := by rw [Polynomial.leadingCoeff, hsnd]
  refine not_eventually_le_of_degree_pos s (by rw [hsdeg]; exact hpd)
    (by rw [hslc]; exact hcoeff_pos.le) c ?_
  filter_upwards [h] with n hn
  simp only [hs, eval_sub]
  linarith

/-- A surjective linear map between modules of equal finite length is injective. -/
@[ega "IV 2.5.7" "special case", sga "3 X 3.8" "Finite abelian groups"]
theorem inj_of_surj_of_length_eq {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (g : X →ₗ[R] Y) (hg : Function.Surjective g)
    (hlen : Module.length R X = Module.length R Y) (hfin : Module.length R Y < ⊤) :
    Function.Injective g := by
  have hexact : Function.Exact (LinearMap.ker g).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have heq := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    Subtype.coe_injective hg hexact
  rw [hlen] at heq
  have hkr0 : Module.length R (LinearMap.ker g) = 0 :=
    ENat.add_left_injective_of_ne_top hfin.ne_top (by simpa using heq.symm)
  have hsub : Subsingleton (LinearMap.ker g) := Module.length_eq_zero_iff.mp hkr0
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker g) 0)

open Filter in
/-- The Hilbert–Samuel polynomial of a finite module of infinite length has positive
degree. -/
theorem hsPoly_degree_pos [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : ¬ HasFiniteLength R N) (χ : ℚ[X]) (hχ : IsHilbertSamuelPoly I N χ) :
    0 < χ.degree := by
  by_contra hdeg
  push Not at hdeg
  have hχC : χ = C (χ.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hχ
  have hconst : ∀ n ≥ n₀, hilbertSamuelFunction I N n = hilbertSamuelFunction I N n₀ := by
    intro n hn
    have e1 := hn₀ n hn
    have e2 := hn₀ n₀ le_rfl
    rw [hχC, Polynomial.eval_C] at e1 e2
    exact_mod_cast e1.symm.trans e2
  have hstep : hilbertSamuelFunction I N (n₀ + 1) = hilbertSamuelFunction I N n₀ :=
    hconst (n₀ + 1) (by omega)
  set B : Submodule R N := I ^ (n₀ + 1) • (⊤ : Submodule R N) with hB
  set A : Submodule R N := I ^ (n₀ + 2) • (⊤ : Submodule R N) with hA
  have hAB : A ≤ B := by
    rw [hA, hB]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  have hfinB : Module.length R (N ⧸ B) < ⊤ := length_quotient_lt_top I hI N n₀
  have hfinA : Module.length R (N ⧸ A) < ⊤ := length_quotient_lt_top I hI N (n₀ + 1)
  have hlenAB : Module.length R (N ⧸ A) = Module.length R (N ⧸ B) := by
    have := congrArg (Nat.cast : ℕ → ℕ∞) hstep
    rwa [hilbertSamuelFunction, hilbertSamuelFunction, ENat.natCast_toNat hfinA.ne_top,
      ENat.natCast_toNat hfinB.ne_top] at this
  have hinj : Function.Injective (Submodule.factor hAB) :=
    inj_of_surj_of_length_eq (Submodule.factor hAB) (Submodule.factor_surjective hAB)
      hlenAB hfinB
  have hBA : B ≤ A := by
    intro b hb
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hinj
    rwa [← Submodule.mkQ_apply, Submodule.factor_mk hAB, map_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
  have hABeq : A = B := le_antisymm hAB hBA
  have hBIB : B = I • B :=
    hABeq.symm.trans (by rw [hA, hB, ← smul_assoc, smul_eq_mul, ← pow_succ'])
  have hjac : I ≤ (⊥ : Ideal R).jacobson := le_jacobson_bot_of_radical_eq hI
  have hfg : B.FG := Submodule.FG.of_finite
  have hBbot : B = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I B hfg (le_of_eq hBIB) hjac
  have hiso : Module.length R (N ⧸ B) = Module.length R N := by
    rw [hBbot]
    exact (Submodule.quotEquivOfEqBot (⊥ : Submodule R N) rfl).length_eq
  exact hN (hiso ▸ hfinB : Module.length R N < ⊤)

open Filter in
/-- A polynomial eventually nonnegative on `ℕ` has nonnegative leading coefficient. -/
theorem nonneg_leadingCoeff_of_eventually_nonneg (p : ℚ[X])
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ p.eval (n : ℚ)) : 0 ≤ p.leadingCoeff := by
  by_contra hneg
  push Not at hneg
  have hp0 : p ≠ 0 := by rintro rfl; simp at hneg
  rcases lt_or_ge (0 : WithBot ℕ) p.degree with hdeg | hdeg
  · refine not_eventually_le_of_degree_pos (-p) (by rwa [degree_neg])
      (by rw [leadingCoeff_neg]; linarith) 0 ?_
    filter_upwards [h] with n hn
    simp only [eval_neg]
    linarith
  · have hpC : p = C (p.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
    have hlc : p.leadingCoeff = p.coeff 0 := by rw [hpC, leadingCoeff_C, coeff_C_zero]
    obtain ⟨n, h2⟩ := h.exists
    rw [hpC, Polynomial.eval_C] at h2
    linarith

/-- The Hilbert–Samuel polynomial of a finite module of infinite length is nonzero. -/
theorem hsPoly_ne_zero [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : ¬ HasFiniteLength R N) (χ : ℚ[X]) (hχ : IsHilbertSamuelPoly I N χ) :
    χ ≠ 0 := by
  intro hχ0
  have hev : ∀ᶠ (n : ℕ) in Filter.atTop, (hilbertSamuelFunction I N n : ℚ) = 0 := by
    filter_upwards [hχ] with n hn
    simpa [hχ0] using hn.symm
  obtain ⟨n, hn⟩ := hev.exists
  have hHSF : hilbertSamuelFunction I N n = 0 := by exact_mod_cast hn
  unfold hilbertSamuelFunction at hHSF
  have hlt := length_quotient_lt_top I hI N n
  have hlen0 : Module.length R (N ⧸ (I ^ (n + 1) • (⊤ : Submodule R N))) = 0 :=
    (ENat.toNat_eq_zero.mp hHSF).resolve_right hlt.ne
  have hsub : Subsingleton (N ⧸ (I ^ (n + 1) • (⊤ : Submodule R N))) :=
    Module.length_eq_zero_iff.mp hlen0
  have htop : I ^ (n + 1) • (⊤ : Submodule R N) = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp hsub
  have hjac : I ^ (n + 1) ≤ (⊥ : Ideal R).jacobson :=
    (Ideal.pow_le_self (by omega)).trans (le_jacobson_bot_of_radical_eq hI)
  have hle : (⊤ : Submodule R N) ≤ I ^ (n + 1) • (⊤ : Submodule R N) := by rw [htop]
  have hfg : (⊤ : Submodule R N).FG := Module.finite_def.mp (by infer_instance)
  have hbot : (⊤ : Submodule R N) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (I ^ (n + 1)) ⊤ hfg hle hjac
  have hNsub : Subsingleton N :=
    (Submodule.subsingleton_iff R).mp (subsingleton_iff_bot_eq_top.mp hbot.symm)
  exact hN (by unfold HasFiniteLength; simp)

/-- Upper length bound: `length (M / Jⁿ⁺¹M) ≤ length (M' / Jⁿ⁺¹M') + length (M/M')`. -/
theorem length_le_upper {M : Type*} [AddCommGroup M] [Module R M]
    (M' : Submodule R M) (J : Ideal R) :
    Module.length R (M ⧸ (J • (⊤ : Submodule R M))) ≤
      Module.length R (↥M' ⧸ (J • (⊤ : Submodule R ↥M'))) + Module.length R (M ⧸ M') := by
  rw [StacksHelpers.length_quotient_ses M'.subtype M'.mkQ M'.mkQ_surjective
    (LinearMap.exact_subtype_mkQ M') (J • (⊤ : Submodule R M))]
  exact add_le_add (length_quotient_antitone (smul_top_le_comap_subtype_smul_top M' J))
    (Module.length_le_of_surjective _ (Submodule.mkQ_surjective _))

/-- Lower length bound (Artin–Rees): for some `k`, for all `n ≥ k`,
`length (M' / Iⁿ⁻ᵏ⁺¹M') ≤ length (M / Iⁿ⁺¹M)`. -/
theorem length_ge_lower {M : Type*} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (M' : Submodule R M) (I : Ideal R) :
    ∃ k : ℕ, ∀ n ≥ k,
      Module.length R (↥M' ⧸ (I ^ ((n - k) + 1) • (⊤ : Submodule R ↥M'))) ≤
        Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (M := M) M'
  refine ⟨k, fun n hn => ?_⟩
  set A : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M) with hA
  have hinj : Module.length R (↥M' ⧸ Submodule.comap M'.subtype A) ≤ Module.length R (M ⧸ A) :=
    length_comap_quotient_le M'.subtype A
  have hcomap_le : Submodule.comap M'.subtype A ≤ I ^ ((n - k) + 1) • (⊤ : Submodule R ↥M') := by
    refine comap_subtype_le_smul_top M' A _ ?_
    rw [inf_comm, hA, hk (n + 1) (by omega), show n + 1 - k = n - k + 1 by omega]
    exact smul_mono_right _ inf_le_right
  exact (length_quotient_antitone hcomap_le).trans hinj

/-- A submodule of finite colength in a module of infinite length has infinite length. -/
theorem not_hasFiniteLength_of_hasFiniteColength {M : Type*} [AddCommGroup M] [Module R M]
    (hM : ¬ HasFiniteLength R M) (M' : Submodule R M) (hM' : HasFiniteColength M') :
    ¬ HasFiniteLength R M' := fun hfin => hM <| by
  unfold HasFiniteLength at hfin ⊢
  rw [Module.length_eq_add_of_exact M'.subtype M'.mkQ Subtype.coe_injective M'.mkQ_surjective
    (LinearMap.exact_subtype_mkQ M')]
  exact ENat.add_lt_top.mpr ⟨hfin, hM'⟩

/-- A Hilbert–Samuel polynomial has nonnegative leading coefficient. -/
theorem leadingCoeff_nonneg_of_isHilbertSamuelPoly {I : Ideal R} {M : Type*} [AddCommGroup M]
    [Module R M] {χ : ℚ[X]} (hχ : IsHilbertSamuelPoly I M χ) : 0 ≤ χ.leadingCoeff :=
  nonneg_leadingCoeff_of_eventually_nonneg χ <| by
    filter_upwards [hχ] with n hn
    exact hn ▸ Nat.cast_nonneg _

open Filter in
/-- For a finite-colength submodule `M' ⊆ M`, eventually
`χ_{I,M}(n) ≤ χ_{I,M'}(n) + length_R(M / M')`. -/
theorem hsPoly_eventually_le_add [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (M' : Submodule R M) (hM' : HasFiniteColength M') {χM χM' : ℚ[X]}
    (hχM : IsHilbertSamuelPoly I M χM) (hχM' : IsHilbertSamuelPoly I (↥M') χM') :
    ∀ᶠ n : ℕ in atTop,
      χM.eval (n : ℚ) ≤ χM'.eval (n : ℚ) + ((Module.length R (M ⧸ M')).toNat : ℚ) := by
  have hfin : Module.length R (M ⧸ M') < ⊤ := hM'
  filter_upwards [hχM, hχM'] with n h₁ h₂
  have hfin' := length_quotient_lt_top I hI (↥M') n
  have hle := ENat.toNat_le_toNat (length_le_upper M' (I ^ (n + 1)))
    (ENat.add_lt_top.mpr ⟨hfin', hfin⟩).ne_top
  rw [ENat.toNat_add hfin'.ne_top hfin.ne_top] at hle
  rw [h₁, h₂]
  unfold hilbertSamuelFunction
  exact_mod_cast hle

open Filter in
/-- By Artin–Rees, some shift `P(t) = χ_{I,M'}(t - k)` of the Hilbert–Samuel polynomial of a
submodule `M' ⊆ M` satisfies `P(n) ≤ χ_{I,M}(n)` for all large `n`. -/
theorem hsPoly_exists_shift_le [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (M' : Submodule R M) {χM χM' : ℚ[X]}
    (hχM : IsHilbertSamuelPoly I M χM) (hχM' : IsHilbertSamuelPoly I (↥M') χM') :
    ∃ P : ℚ[X], P.degree = χM'.degree ∧ P.leadingCoeff = χM'.leadingCoeff ∧
      ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ χM.eval (n : ℚ) := by
  obtain ⟨k, hk⟩ := length_ge_lower M' I
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hχM'
  refine ⟨χM'.comp (X - C (k : ℚ)), ?_, ?_, ?_⟩
  · rw [degree_comp, degree_X_sub_C, mul_one]
    rw [degree_X_sub_C]
    exact one_pos
  · rw [leadingCoeff_comp (by rw [natDegree_X_sub_C]; norm_num), leadingCoeff_X_sub_C, one_pow,
      mul_one]
  · filter_upwards [hχM, eventually_ge_atTop (k + n₀)] with n h₁ hn
    have hkn : k ≤ n := by omega
    rw [eval_comp, eval_sub, eval_X, eval_C, h₁, ← Nat.cast_sub hkn, hn₀ (n - k) (by omega)]
    unfold hilbertSamuelFunction
    exact_mod_cast ENat.toNat_le_toNat (hk n hkn) (length_quotient_lt_top I hI M n).ne_top

/-- Let `(R, m)` be a Noetherian local ring, `I ⊆ R` an ideal of definition, and `M`
a finite `R`-module which does not have finite length.  Let `M' ⊆ M` be a
submodule with finite colength, and let `χ_{I,M}`, `χ_{I,M'} ∈ Q[t]` be the
Hilbert–Samuel polynomials of `M` and `M'`.  Then the difference
`χ_{I,M} - χ_{I,M'}` has degree strictly less than the degree of each of the two
Hilbert–Samuel polynomials. -/
@[stacks 00KB, ega "0 16.2.2.2" "special case"]
theorem degree_sub_lt
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : IsIdealOfDefinition I)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : ¬ HasFiniteLength R M)
    (M' : Submodule R M) (hM' : HasFiniteColength M')
    (χM χM' : ℚ[X])
    (hχM : IsHilbertSamuelPoly I M χM)
    (hχM' : IsHilbertSamuelPoly I (↥M') χM') :
    (χM - χM').degree < χM.degree ∧ (χM - χM').degree < χM'.degree := by
  have hM'inf := not_hasFiniteLength_of_hasFiniteColength hM M' hM'
  have hχMne := hsPoly_ne_zero I hI M hM χM hχM
  have hdegM := hsPoly_degree_pos I hI M hM χM hχM
  have hup := hsPoly_eventually_le_add I hI M' hM' hχM hχM'
  obtain ⟨P, hPdeg, hPlc, hlow⟩ := hsPoly_exists_shift_le I hI M' hχM hχM'
  have hlow₀ := hlow.mono fun n h => (add_zero (χM.eval (n : ℚ))).symm ▸ h
  have hdeg_eq : χM.degree = χM'.degree :=
    le_antisymm
      (poly_cmp χM χM' _ hup (hsPoly_ne_zero I hI (↥M') hM'inf χM' hχM')
        (leadingCoeff_nonneg_of_isHilbertSamuelPoly hχM))
      (hPdeg ▸ poly_cmp P χM 0 hlow₀ hχMne
        (hPlc ▸ leadingCoeff_nonneg_of_isHilbertSamuelPoly hχM'))
  have hPM : P.degree = χM.degree := hPdeg.trans hdeg_eq.symm
  have hlc_eq : χM.leadingCoeff = χM'.leadingCoeff :=
    le_antisymm (leadingCoeff_cmp χM χM' _ hup hdeg_eq hdegM)
      (hPlc ▸ leadingCoeff_cmp P χM 0 hlow₀ hPM (hPM ▸ hdegM))
  have h₁ := degree_sub_lt_left hdeg_eq hχMne hlc_eq
  exact ⟨h₁, hdeg_eq ▸ h₁⟩

end HilbertSamuel
