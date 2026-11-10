module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# A map which is bijective on adic completions is bijective near the vanishing locus

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `φ : M →ₗ[A] N` a map of finite `A`-modules
whose `I`-adic completion is bijective. Adic completion preserves surjectivity, so the completion
of the cokernel of `φ` vanishes and therefore `N / φ(M) = I • (N / φ(M))`; Nakayama's lemma
produces an `a ≡ 1 (mod I)` annihilating the cokernel. Injectivity of the completed map puts the
kernel of `φ` inside `⨅ n, I ^ n • M`, which the Artin–Rees lemma shows is an `I`-multiple of
itself, so Nakayama annihilates it too. A single `a ≡ 1 (mod I)` therefore kills both kernel and
cokernel, and `φ` becomes bijective after localizing at the powers of `a`. Since `a ≡ 1 (mod I)`,
no prime containing `I` contains `a`, so `V(I) ⊆ D(a)`: the map is an isomorphism on an open
neighbourhood of the vanishing locus of `I`.

For a principal ideal `I = (f)` the completion hypothesis is cheap to verify: if `f` is a
nonzerodivisor on `N` and `φ` is bijective modulo `f`, then an induction on `n` makes `φ`
bijective modulo `f ^ n` for every `n`, hence bijective on `f`-adic completions.

Together these are the two steps of the surjectivity half of [Stacks, Tag 0EIH] which compare a
finite module `M` with the module `N` of sections of its restriction to a punctured spectrum.
There `f` is a nonzerodivisor on `M` and on `N`, and for `g` in the defining ideal the reduction
`M_g / f M_g → N_g / f N_g` is bijective; the conclusion is that `M_g → N_g` is an isomorphism on
a neighbourhood of `V(f) ∩ D(g)`.

## Main results

All of these live in the namespace `Stacks.AdicCompletion.NearVanishingLocus`.

* `exists_sub_one_mem_and_smul_ker_eq_zero_and_smul_mem_range`: a bijection on `I`-adic
  completions is a bijection up to multiplication by a single element of `1 + I`.
* `exists_sub_one_mem_and_bijective_localizedModule_map`: such a map becomes bijective after
  localizing at an element congruent to `1` modulo `I`.
* `exists_zeroLocus_subset_basicOpen_and_bijective`: the same, with the localizing element
  presented through the inclusion `V(I) ⊆ D(a)` of its basic open set.
* `bijective_adicCompletionMap_of_isSMulRegular`: bijectivity modulo a nonzerodivisor `f`
  implies bijectivity on `f`-adic completions.
* `exists_sub_one_mem_and_bijective_localizedModule_map_localization`: the localization
  `M_g → N_g` of such a map is an isomorphism on a neighbourhood of the vanishing locus of `f`
  in `Spec A_g`.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
-/

@[expose] public section

universe u v w

namespace Stacks.AdicCompletion.NearVanishingLocus

open LinearMap

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N : Type w} [AddCommGroup N] [Module A N]

/-- The step `(a) • M` of the adic filtration of a module by a principal ideal consists of the
multiples of `a`. -/
theorem mem_span_singleton_smul_top_iff (a : A) (x : M) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule A M) ↔ ∃ y : M, a • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- Over a Noetherian ring the intersection `⨅ n, I ^ n • M` of the adic filtration of a finite
module is annihilated by an element congruent to `1` modulo `I`. -/
theorem exists_sub_one_mem_and_smul_iInf_eq_zero [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ a : A, a - 1 ∈ I ∧ ∀ x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule A M), a • x = 0 := by
  set J : Submodule A M := ⨅ n : ℕ, I ^ n • ⊤
  have hJle : ∀ n : ℕ, J ≤ I ^ n • (⊤ : Submodule A M) := fun n => iInf_le _ n
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul J
  have hle : J ≤ I • J :=
    le_of_eq <| calc
      J = I ^ (k + 1) • (⊤ : Submodule A M) ⊓ J := (inf_eq_right.mpr (hJle _)).symm
      _ = I ^ 1 • (I ^ k • (⊤ : Submodule A M) ⊓ J) := by simpa using hk (k + 1) (Nat.le_succ k)
      _ = I • J := by rw [pow_one, inf_eq_right.mpr (hJle k)]
  exact Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I J
    (IsNoetherian.noetherian J) hle

/-- **A bijection on `I`-adic completions is a bijection up to a factor congruent to `1`.**
If `A` is Noetherian, `M` and `N` are finite `A`-modules and `φ : M →ₗ[A] N` induces a bijection
on `I`-adic completions, then some `a` with `a - 1 ∈ I` annihilates the kernel of `φ` and carries
`N` into the image of `φ`. -/
theorem exists_sub_one_mem_and_smul_ker_eq_zero_and_smul_mem_range [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N] (I : Ideal A) (φ : M →ₗ[A] N)
    (h : Function.Bijective (AdicCompletion.map I φ)) :
    ∃ a : A, a - 1 ∈ I ∧ (∀ x : M, φ x = 0 → a • x = 0) ∧ ∀ y : N, a • y ∈ range φ := by
  obtain ⟨a₁, ha₁, hker⟩ := exists_sub_one_mem_and_smul_iInf_eq_zero I M
  have hcomp : (range φ).mkQ ∘ₗ φ = 0 := by
    ext x
    simp
  have hzero : ∀ z : AdicCompletion I (N ⧸ range φ), z = 0 := by
    intro z
    obtain ⟨u, hu⟩ :=
      AdicCompletion.map_surjective I (Submodule.mkQ_surjective (range φ)) z
    obtain ⟨t, ht⟩ := h.surjective u
    rw [← hu, ← ht, AdicCompletion.map_comp_apply, hcomp]
    simp
  have hquot : ∀ y : N ⧸ range φ, y ∈ (I • ⊤ : Submodule A (N ⧸ range φ)) := by
    intro y
    have hsub : Subsingleton ((N ⧸ range φ) ⧸ (I ^ 1 • ⊤ : Submodule A (N ⧸ range φ))) := by
      refine ⟨fun p q => ?_⟩
      obtain ⟨p', hp'⟩ := AdicCompletion.eval_surjective I (N ⧸ range φ) 1 p
      obtain ⟨q', hq'⟩ := AdicCompletion.eval_surjective I (N ⧸ range φ) 1 q
      rw [← hp', ← hq', hzero p', hzero q']
    have hy : (I ^ 1 • (⊤ : Submodule A (N ⧸ range φ))).mkQ y = 0 := hsub.elim _ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    simpa using hy
  obtain ⟨a₂, ha₂, hcoker⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (⊤ : Submodule A (N ⧸ range φ)) Module.Finite.fg_top fun y _ => hquot y
  refine ⟨a₁ * a₂, ?_, ?_, ?_⟩
  · rw [show a₁ * a₂ - 1 = a₁ * (a₂ - 1) + (a₁ - 1) by ring]
    exact I.add_mem (I.mul_mem_left _ ha₂) ha₁
  · intro x hx
    have hx0 : AdicCompletion.of I M x = 0 := by
      apply h.injective
      simp [AdicCompletion.map_of, hx]
    have hmem : x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule A M) := by
      rw [Submodule.mem_iInf]
      intro n
      have := congrArg (fun z : AdicCompletion I M => z.val n) hx0
      simp only [AdicCompletion.of_apply, AdicCompletion.val_zero_apply,
        Submodule.mkQ_apply] at this
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    rw [mul_comm, mul_smul, hker x hmem, smul_zero]
  · intro y
    have : (range φ).mkQ (a₂ • y) = 0 := by
      rw [map_smul]
      exact hcoker _ Submodule.mem_top
    rw [mul_smul]
    exact (range φ).smul_mem a₁ ((Submodule.Quotient.mk_eq_zero _).mp this)

/-- A map whose kernel is annihilated by `a` and whose image contains `a • N` becomes bijective
after localizing at the powers of `a`. -/
theorem bijective_localizedModule_map_of_smul_ker_eq_zero_of_smul_mem_range (φ : M →ₗ[A] N)
    (a : A) (hker : ∀ x : M, φ x = 0 → a • x = 0) (hrange : ∀ y : N, a • y ∈ range φ) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  set T := Submonoid.powers a
  have haT : a ∈ T := Submonoid.mem_powers a
  constructor
  · apply IsLocalizedModule.injective_of_map_zero T (LocalizedModule.mkLinearMap T M)
    intro m hm
    change LocalizedModule.map T φ (LocalizedModule.mk m 1) = 0 at hm
    rw [LocalizedModule.map_mk] at hm
    obtain ⟨t, ht⟩ :=
      (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T N)).1 hm
    have hφ : φ ((t : A) • m) = 0 := by
      simpa only [map_smul, Submonoid.smul_def] using ht
    apply (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T M)).2
    refine ⟨(⟨a, haT⟩ : T) * t, ?_⟩
    simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hker _ hφ
  · intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨y, hy⟩ := hrange m
      refine ⟨LocalizedModule.mk y ((⟨a, haT⟩ : T) * s), ?_⟩
      rw [LocalizedModule.map_mk, hy]
      exact LocalizedModule.mk_cancel_common_left ⟨a, haT⟩ s m

/-- An element congruent to `1` modulo `I` lies outside every prime containing `I`. -/
theorem notMem_of_sub_one_mem {I : Ideal A} {a : A} (ha : a - 1 ∈ I) {p : Ideal A} [p.IsPrime]
    (hp : I ≤ p) : a ∉ p := fun hap =>
  (‹p.IsPrime›).ne_top <| (Ideal.eq_top_iff_one p).mpr <| by simpa using p.sub_mem hap (hp ha)

/-- **A map of finite modules which is bijective on `I`-adic completions is bijective on a
neighbourhood of `V(I)`.** There is an `a ∈ A` congruent to `1` modulo `I`, so that in particular
`V(I) ⊆ D(a)`, for which the localization of `φ` at the powers of `a` is bijective. -/
theorem exists_sub_one_mem_and_bijective_localizedModule_map [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N] (I : Ideal A) (φ : M →ₗ[A] N)
    (h : Function.Bijective (AdicCompletion.map I φ)) :
    ∃ a : A, a - 1 ∈ I ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  obtain ⟨a, ha, hker, hrange⟩ :=
    exists_sub_one_mem_and_smul_ker_eq_zero_and_smul_mem_range I φ h
  exact ⟨a, ha,
    bijective_localizedModule_map_of_smul_ker_eq_zero_of_smul_mem_range φ a hker hrange⟩

/-- **Geometric form of the previous statement.** A map of finite modules over a Noetherian ring
which is bijective on `I`-adic completions is bijective on a basic open set containing the
vanishing locus of `I`. For `I = (f)` this contains `V(f) ∩ D(g)` for every `g ∈ A`. -/
theorem exists_zeroLocus_subset_basicOpen_and_bijective [IsNoetherianRing A] [Module.Finite A M]
    [Module.Finite A N] (I : Ideal A) (φ : M →ₗ[A] N)
    (h : Function.Bijective (AdicCompletion.map I φ)) :
    ∃ a : A, PrimeSpectrum.zeroLocus (I : Set A) ⊆
        (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ∧
      Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  obtain ⟨a, ha, hbij⟩ := exists_sub_one_mem_and_bijective_localizedModule_map I φ h
  refine ⟨a, fun p hp => ?_, hbij⟩
  rw [PrimeSpectrum.mem_zeroLocus] at hp
  exact notMem_of_sub_one_mem ha hp

/-- A map which is bijective modulo every power of `I` is bijective on `I`-adic completions. -/
theorem bijective_adicCompletionMap_of_forall_bijective_reduceModIdeal (I : Ideal A)
    (φ : M →ₗ[A] N) (hφ : ∀ n : ℕ, Function.Bijective (φ.reduceModIdeal (I ^ n))) :
    Function.Bijective (AdicCompletion.map I φ) := by
  constructor
  · intro x y hxy
    refine AdicCompletion.ext fun n => (hφ n).injective ?_
    exact congrArg (fun z : AdicCompletion I N => z.val n) hxy
  · intro y
    choose x hx using fun n => (hφ n).surjective (y.val n)
    have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
        AdicCompletion.transitionMap I M hmn (x n) = x m := by
      intro m n hmn
      refine (hφ m).injective ?_
      have ht :=
        LinearMap.congr_fun (AdicCompletion.transitionMap_comp_reduceModIdeal I φ hmn) (x n)
      change AdicCompletion.transitionMap I N hmn (φ.reduceModIdeal (I ^ n) (x n)) =
        φ.reduceModIdeal (I ^ m) (AdicCompletion.transitionMap I M hmn (x n)) at ht
      rw [← ht, hx, y.property, hx]
    exact ⟨⟨x, hcompat⟩, AdicCompletion.ext hx⟩

variable (φ : M →ₗ[A] N)

/-- Two classes modulo `(a) • ⊤` agree iff their difference is a multiple of `a`. -/
private theorem mk_eq_mk_span_singleton_smul_top_iff {P : Type*} [AddCommGroup P] [Module A P]
    (a : A) (x y : P) :
    (Submodule.Quotient.mk x : P ⧸ (Ideal.span {a} • ⊤ : Submodule A P)) =
      Submodule.Quotient.mk y ↔ ∃ w : P, a • w = x - y := by
  rw [Submodule.Quotient.eq, mem_span_singleton_smul_top_iff]

/-- Bijectivity of the reduction modulo a principal ideal, read off on elements. -/
theorem bijective_reduceModIdeal_span_singleton_iff (a : A) :
    Function.Bijective (φ.reduceModIdeal (Ideal.span {a})) ↔
      (∀ x : M, (∃ y : N, φ x = a • y) → ∃ z : M, x = a • z) ∧
        ∀ y : N, ∃ (x : M) (w : N), y = φ x + a • w := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x ⟨y, hy⟩ => ?_, fun y => ?_⟩
    · have := hinj (a₁ := Submodule.Quotient.mk x) (a₂ := Submodule.Quotient.mk 0) <| by
        rw [LinearMap.reduceModIdeal_apply, LinearMap.reduceModIdeal_apply,
          mk_eq_mk_span_singleton_smul_top_iff]
        exact ⟨y, by simpa using hy.symm⟩
      obtain ⟨z, hz⟩ := (mk_eq_mk_span_singleton_smul_top_iff a _ _).1 this
      exact ⟨z, by simpa using hz.symm⟩
    · obtain ⟨q, hq⟩ := hsurj (Submodule.Quotient.mk (p := (Ideal.span {a} • ⊤ : Submodule A N)) y)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.reduceModIdeal_apply, mk_eq_mk_span_singleton_smul_top_iff] at hq
      obtain ⟨w, hw⟩ := hq
      refine ⟨x, -w, ?_⟩
      rw [smul_neg, hw]
      abel
  · rintro ⟨hinj, hsurj⟩
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_zero, LinearMap.reduceModIdeal_apply,
        mk_eq_mk_span_singleton_smul_top_iff] at hq
      obtain ⟨y, hy⟩ := hq
      obtain ⟨z, hz⟩ := hinj x ⟨y, by simpa using hy.symm⟩
      rw [← Submodule.Quotient.mk_zero, mk_eq_mk_span_singleton_smul_top_iff]
      exact ⟨z, by simpa using hz.symm⟩
    · intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, w, hw⟩ := hsurj y
      refine ⟨Submodule.Quotient.mk (p := (Ideal.span {a} • ⊤ : Submodule A M)) x, ?_⟩
      rw [LinearMap.reduceModIdeal_apply, mk_eq_mk_span_singleton_smul_top_iff]
      exact ⟨-w, by rw [hw]; module⟩

/-- If `f` is a nonzerodivisor on `N` and `φ` is injective modulo `f`, then a multiple of `f ^ n`
in the image of `φ` comes from a multiple of `f ^ n`. -/
theorem exists_eq_pow_smul_of_eq_pow_smul {f : A} (hreg : IsSMulRegular N f)
    (hinj : ∀ x : M, (∃ y : N, φ x = f • y) → ∃ z : M, x = f • z) (n : ℕ) (x : M)
    (hx : ∃ y : N, φ x = f ^ n • y) : ∃ z : M, x = f ^ n • z := by
  induction n generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := hx
    obtain ⟨z, hz⟩ := ih x ⟨f • y, by rw [hy, pow_succ, mul_smul]⟩
    have hzy : φ z = f • y := by
      apply hreg.pow n
      change f ^ n • φ z = f ^ n • (f • y)
      rw [← map_smul, ← hz, hy, pow_succ, mul_smul]
    obtain ⟨w, hw⟩ := hinj z ⟨y, hzy⟩
    exact ⟨w, by rw [hz, hw, pow_succ, mul_smul]⟩

/-- If `φ` is surjective modulo `f`, then it is surjective modulo every power of `f`. -/
theorem exists_add_pow_smul_of_exists_add_smul {f : A}
    (hsurj : ∀ y : N, ∃ (x : M) (w : N), y = φ x + f • w) (n : ℕ) (y : N) :
    ∃ (x : M) (w : N), y = φ x + f ^ n • w := by
  induction n generalizing y with
  | zero => exact ⟨0, y, by simp⟩
  | succ n ih =>
    obtain ⟨x, w, hw⟩ := ih y
    obtain ⟨x', w', hw'⟩ := hsurj w
    refine ⟨x + f ^ n • x', w', ?_⟩
    rw [hw, hw', map_add, map_smul, pow_succ, mul_smul]
    module

/-- **Bijectivity modulo a nonzerodivisor gives bijectivity on completions.** If `f` is a
nonzerodivisor on `N` and `φ` is bijective modulo `f`, then `φ` is bijective on `f`-adic
completions. -/
theorem bijective_adicCompletionMap_of_isSMulRegular {f : A} (hreg : IsSMulRegular N f)
    (h : Function.Bijective (φ.reduceModIdeal (Ideal.span {f}))) :
    Function.Bijective (AdicCompletion.map (Ideal.span {f}) φ) := by
  obtain ⟨hinj, hsurj⟩ := (bijective_reduceModIdeal_span_singleton_iff φ f).1 h
  refine bijective_adicCompletionMap_of_forall_bijective_reduceModIdeal _ φ fun n => ?_
  rw [Ideal.span_singleton_pow, bijective_reduceModIdeal_span_singleton_iff]
  exact ⟨fun x hx => exists_eq_pow_smul_of_eq_pow_smul φ hreg hinj n x hx,
    exists_add_pow_smul_of_exists_add_smul φ hsurj n⟩

/-- A nonzerodivisor on `N` stays a nonzerodivisor on every localization of `N`. -/
theorem isSMulRegular_localizedModule (S : Submonoid A) {f : A} (hreg : IsSMulRegular N f) :
    IsSMulRegular (LocalizedModule S N) f := by
  have key : ∀ v : LocalizedModule S N, f • v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h n s =>
      rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hv
      obtain ⟨u, hu⟩ := hv
      have hun : (u : A) • n = 0 := by
        apply hreg
        change f • ((u : A) • n) = f • (0 : N)
        rw [smul_zero, smul_comm]
        simpa [Submonoid.smul_def] using hu
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
      exact ⟨u, by simp [Submonoid.smul_def, hun]⟩
  intro z w hzw
  have hzw' : f • z = f • w := hzw
  rw [← sub_eq_zero]
  refine key _ ?_
  rw [smul_sub, hzw', sub_self]

/-- **Stacks 0EIH, the localization-at-`g` comparison.** Let `A` be Noetherian, let `φ : M →ₗ[A] N`
be a map of finite `A`-modules, let `f` be a nonzerodivisor on `N` and let `g ∈ A`. If the
localization of `φ` at `g` is bijective modulo `f`, then it is an isomorphism after a further
localization at an element of `A_g` congruent to `1` modulo `f`; in particular `M_g → N_g` is an
isomorphism on an open neighbourhood of the vanishing locus of `f` in `Spec A_g`, that is, on a
neighbourhood of `V(f) ∩ D(g)`. -/
theorem exists_sub_one_mem_and_bijective_localizedModule_map_localization [IsNoetherianRing A]
    [Module.Finite A M] [Module.Finite A N] (f g : A) (hreg : IsSMulRegular N f)
    (h : Function.Bijective ((LocalizedModule.map (Submonoid.powers g) φ).reduceModIdeal
      (Ideal.span {algebraMap A (Localization (Submonoid.powers g)) f}))) :
    ∃ a : Localization (Submonoid.powers g),
      a - 1 ∈ Ideal.span {algebraMap A (Localization (Submonoid.powers g)) f} ∧
        Function.Bijective (LocalizedModule.map (Submonoid.powers a)
          (LocalizedModule.map (Submonoid.powers g) φ)) := by
  have _ : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have _ : Module.FinitePresentation A N := Module.finitePresentation_of_finite A N
  have hregloc : IsSMulRegular (LocalizedModule (Submonoid.powers g) N)
      (algebraMap A (Localization (Submonoid.powers g)) f) := by
    have hbase := isSMulRegular_localizedModule (N := N) (Submonoid.powers g) hreg
    intro z w hzw
    have hzw' : algebraMap A (Localization (Submonoid.powers g)) f • z =
        algebraMap A (Localization (Submonoid.powers g)) f • w := hzw
    exact hbase (by simpa only [algebraMap_smul] using hzw')
  exact exists_sub_one_mem_and_bijective_localizedModule_map _ _
    (bijective_adicCompletionMap_of_isSMulRegular _ hregloc h)

end Stacks.AdicCompletion.NearVanishingLocus
