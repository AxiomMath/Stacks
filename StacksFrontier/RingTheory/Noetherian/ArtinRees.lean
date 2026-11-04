module

public import StacksCore.Tactic.StacksAttribute
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

/-!
# The Artin–Rees lemma and the intersection of the powers of an ideal

Let `R` be a Noetherian ring and `I ⊆ R` an ideal. This file proves the Artin–Rees lemma for a
submodule of a finite `R`-module and for a map of finite `R`-modules, and describes the submodule
`⋂_n I^n M` of a finite `R`-module `M`.

## Main definitions

* `krullIntersection`: the submodule `⋂_n I^n M`.

## Main results

* `artin_rees`: the Artin–Rees lemma.
* `exists_comap_smul_eq_and_range_inf_le`: the Artin–Rees lemma for a map of finite modules.
* `exists_notMem_localized_krullIntersection_eq_bot`: for every prime `p ⊇ I` there is `f ∉ p`
  such that `⋂_n I^n M` vanishes after inverting `f`.
* `krullIntersection_eq_bot_of_le_jacobson`: `⋂_n I^n M = 0` if `I` is contained in the Jacobson
  radical of `R`.
-/

@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.show false


/-- **Artin–Rees lemma.** For a Noetherian ring `R`, an ideal `I ⊆ R` and a submodule `N` of a
finite `R`-module `M`, there is a constant `c > 0` with `I^n M ⊓ N = I^(n-c) • (I^c M ⊓ N)` for
every `n ≥ c`. -/
@[stacks 00IN, ega "0 7.3.2.1"]
theorem artin_rees
    {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) :
    ∃ c > 0, ∀ n ≥ c,
      (I ^ n • (⊤ : Submodule R M)) ⊓ N
        = I ^ (n - c) • ((I ^ c • (⊤ : Submodule R M)) ⊓ N) := by
  -- Mathlib provides the result with a possibly-zero witness `k`; bump to `k + 1`.
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨k + 1, Nat.succ_pos k, fun n hn => ?_⟩
  have hkp1 : (I ^ (k + 1) • (⊤ : Submodule R M)) ⊓ N
      = I ^ 1 • ((I ^ k • (⊤ : Submodule R M)) ⊓ N) := by
    simpa using hk (k + 1) (by omega)
  rw [hk n (by omega), show n - k = (n - (k + 1)) + 1 from by omega,
    pow_add, mul_smul, ← hkp1]

/-!
## Map version of Artin–Rees

Given an exact sequence `0 → K → M → N` of finitely generated modules over a
Noetherian ring `R` and an ideal `I ⊆ R`, there is a constant `c` such that for
all `n ≥ c`, the preimage `f⁻¹(IⁿN)` equals `K + Iⁿ⁻ᶜ · f⁻¹(IᶜN)` and
`f(M) ∩ IⁿN ⊆ f(Iⁿ⁻ᶜM)`.
-/


/-- `f` applied to `Iᵈ · f⁻¹(Iᶜ · ⊤)` equals `Iᵈ · (Iᶜ · ⊤ ⊓ range f)`. -/
lemma map_smul_comap_smul_top
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) (I : Ideal R) (c d : ℕ) :
    Submodule.map f (I ^ d • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) =
      I ^ d • ((I ^ c • (⊤ : Submodule R N)) ⊓ LinearMap.range f) := by
  rw [Submodule.map_smul'', Submodule.map_comap_eq, inf_comm]

/-- For `n ≥ c`, `Iⁿ⁻ᶜ · f⁻¹(IᶜN) ⊆ f⁻¹(IⁿN)`. -/
lemma smul_comap_le_comap
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) (I : Ideal R) (c n : ℕ) (hn : c ≤ n) :
    I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) ≤
      Submodule.comap f (I ^ n • (⊤ : Submodule R N)) := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  refine le_trans (smul_mono_right _ (Submodule.map_comap_le f _)) ?_
  rw [← Submodule.mul_smul, ← pow_add, Nat.sub_add_cancel hn]

/-- For `c ≤ n`, if `IⁿN ∩ f(M) = Iⁿ⁻ᶜ · (IᶜN ∩ f(M))`, then
`f⁻¹(IⁿN) = ker f + Iⁿ⁻ᶜ · f⁻¹(IᶜN)`. -/
lemma comap_smul_top_eq_ker_sup_smul_comap
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) (I : Ideal R) (c n : ℕ) (hn : c ≤ n)
    (hAR : I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ LinearMap.range f)) :
    Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
      LinearMap.ker f +
        I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) := by
  rw [Submodule.add_eq_sup]
  refine le_antisymm (fun x hx => ?_)
    (sup_le (LinearMap.ker_le_comap f) (smul_comap_le_comap f I c n hn))
  rw [Submodule.mem_comap] at hx
  have hxr : f x ∈ I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f := ⟨hx, ⟨x, rfl⟩⟩
  rw [hAR, ← map_smul_comap_smul_top f I c (n - c)] at hxr
  obtain ⟨y, hy, hfy⟩ := hxr
  have hker : x - y ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hfy, sub_self]
  have hx_eq : x = (x - y) + y := by abel
  rw [hx_eq]
  exact Submodule.add_mem_sup hker hy

/-- If `IⁿN ∩ f(M) = Iⁿ⁻ᶜ · (IᶜN ∩ f(M))`, then `f(M) ∩ IⁿN ⊆ f(Iⁿ⁻ᶜM)`. -/
lemma range_inf_smul_top_le_map_smul_top
    {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) (I : Ideal R) (c n : ℕ)
    (hAR : I ^ n • (⊤ : Submodule R N) ⊓ LinearMap.range f =
        I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ LinearMap.range f)) :
    LinearMap.range f ⊓ (I ^ n • (⊤ : Submodule R N)) ≤
      Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
  rw [inf_comm, hAR]
  refine le_trans (smul_mono_right _ inf_le_right) ?_
  rw [Submodule.map_smul'', Submodule.map_top]

/-- **Map version of Artin–Rees.** For an exact sequence `0 → K → M → N` of
finitely generated modules over a Noetherian ring `R` and an ideal `I`, there is
a constant `c` such that for all `n ≥ c`,
`f⁻¹(IⁿN) = K + Iⁿ⁻ᶜ · f⁻¹(IᶜN)` and `f(M) ∩ IⁿN ⊆ f(Iⁿ⁻ᶜ M)`. -/
@[stacks 00IO, ega "0 7.3.2.1" "more general"]
theorem exists_comap_smul_eq_and_range_inf_le
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (f : M →ₗ[R] N) (I : Ideal R) :
    ∃ c, ∀ n ≥ c,
      Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
        LinearMap.ker f +
          I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) ∧
      LinearMap.range f ⊓ (I ^ n • (⊤ : Submodule R N)) ≤
        Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := N) I (LinearMap.range f)
  exact ⟨c, fun n hn => ⟨comap_smul_top_eq_ker_sup_smul_comap f I c n hn (hc n hn),
    range_inf_smul_top_le_map_smul_top f I c n (hc n hn)⟩⟩

-- Krull's intersection theorem: for a Noetherian local ring `R`, a proper ideal `I ⊆ R`
-- and a finite `R`-module `M`, one has `⋂_{n ≥ 0} I^n M = 0`.
add_to_stacks 00IP "Krull's intersection theorem for a finite module over a Noetherian local ring"
  Ideal.iInf_pow_smul_eq_bot_of_isLocalRing

/-!
## Intersection of powers of an ideal acting on a finite module

Let `R` be a Noetherian ring, `I ⊂ R` an ideal, and `M` a finite `R`-module. Let
`N = ⋂_n I^n M`.

1. For every prime `p ⊇ I` there exists `f ∈ R`, `f ∉ p`, such that the
   localization `N_f` is zero.
2. If `I` is contained in the Jacobson radical of `R`, then `N = 0`.

We package `N` as the submodule
`krullIntersection M I := ⨅ i : ℕ, I ^ i • (⊤ : Submodule R M)`,
which matches the form used by `Ideal.mem_iInf_smul_pow_eq_bot_iff` and
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` in Mathlib.
-/

@[expose] public section

/-- The submodule `N = ⋂_n I^n M` for an ideal `I` of `R` and an `R`-module `M`,
packaged as the infimum over `n : ℕ` of `I ^ n • (⊤ : Submodule R M)`. -/
def krullIntersection {R : Type*} [CommRing R] (M : Type*)
    [AddCommGroup M] [Module R M] (I : Ideal R) : Submodule R M :=
  ⨅ i : ℕ, I ^ i • (⊤ : Submodule R M)

/-- For every prime ideal `p` containing `I`, there exists `f ∈ R` with
`f ∉ p` such that the localization of `N = ⋂_n I^n M` at the submonoid
generated by `f` is the zero submodule. -/
@[stacks 00IQ, ega "0 7.4.2" "more general", sga "3 VIB 6.5.3" "special case"]
theorem exists_notMem_localized_krullIntersection_eq_bot
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    ∃ f : R, f ∉ p ∧
      (krullIntersection M I).localized (Submonoid.powers f) = ⊥ := by
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      I (krullIntersection M I) (IsNoetherian.noetherian _)
      (fun x hx => by
        obtain ⟨s, hsx⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff I x).mp hx
        rw [← hsx]
        exact Submodule.smul_mem_smul s.property hx)
  refine ⟨r, fun hrp => ‹p.IsPrime›.ne_top <| (Ideal.eq_top_iff_one p).mpr <| by
    simpa using p.sub_mem hrp (hIp hr1), ?_⟩
  rw [eq_bot_iff]
  rintro _ ⟨m, hm, s, rfl⟩
  rw [Submodule.mem_bot, IsLocalizedModule.mk'_eq_zero']
  exact ⟨⟨r, Submonoid.mem_powers r⟩, hr m hm⟩

/-- If `I` is contained in the Jacobson radical of `R`, then `N = ⋂_n I^n M = 0`. -/
@[stacks 00IQ, ega "0 7.3.5" "(a) => (c)"]
theorem krullIntersection_eq_bot_of_le_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) :
    krullIntersection M I = ⊥ :=
  Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hI

