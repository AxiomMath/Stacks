module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Functoriality

/-!
# Exactness of the sheaf associated to a graded module

Let `S` be a commutative ring with a nonnegative grading `𝒮 : ℕ → σ`. Taking a `ℤ`-graded
`S`-module `M` to the sheaf `M̃` of `𝒪_{Proj(S)}`-modules it generates is exact: a short exact
sequence `0 → M → N → P → 0` of graded `S`-modules with degree-preserving maps gives a short
exact sequence `0 → M̃ → Ñ → P̃ → 0`.

Short exactness of a sequence of sheaves of modules is short exactness of the induced sequence
on every stalk, and the stalk of `M̃` at a homogeneous prime `𝔭` is the degree-zero part `M₍𝔭₎`
of the localization of `M` at `𝔭`, compatibly with the induced maps. So the statement proved
here is that at every point of `Proj(S)` the sequence of stalks is short exact.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap`: the map on
  stalks induced by a degree-preserving linear map of graded modules.

## Main results

* `Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkMap_shortExact`:
  the stalk sequence of a short exact sequence of graded modules is short exact.

## Implementation notes

The reduction to the degree-zero prime localizations is
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafMap_stalk`: under the
stalk identification the induced map is the localization of the given map at `𝔭`. What remains
is that the degree-zero parts of a short exact sequence localize to a short exact sequence, and
all three assertions rest on one observation: `M₍𝔭₎` consists of the *single* fractions `m / s`
with `m` and `s` homogeneous of the same degree
(`exists_mk_of_mem_degreeZeroModuleAt`), because such fractions are already closed under
addition — the common denominator of two of them is again homogeneous of the degree of the
resulting numerator — and under multiplication by a degree-zero fraction of `S`.

Injectivity then needs nothing beyond injectivity of the localization of an injective map.
Surjectivity needs that a surjective degree-preserving map is surjective in each degree, which
follows because a degree-preserving map commutes with the homogeneous projections
(`decompose_map`). For exactness in the middle, a fraction `n / s` of `N₍𝔭₎` whose image in
`P₍𝔭₎` vanishes satisfies `t • ψ n = 0` for some `t` outside `𝔭`; replacing `t` by one of its
homogeneous components outside `𝔭` — one exists because `𝔭` is homogeneous — preserves the
relation, since the homogeneous components of `t • ψ n` are the `tᵢ • ψ n`
(`decompose_smul_of_mem`). That produces a homogeneous `w` outside `𝔭` with `w • n` in the image
of `φ`, and the homogeneous component of a preimage in the degree of `w • n` is again a
preimage, so `n / s` is the image of a fraction of `M₍𝔭₎`.

## References

* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum
open AlgebraicGeometry
open Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u v w t t' t''

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- A degree-preserving linear map of graded modules commutes with the homogeneous
projections. -/
private theorem decompose_map {R : Type*} [CommRing R] {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] {α β : Type*}
    [SetLike α A] [AddSubgroupClass α A] (ℳ : ℤ → α) [Decomposition ℳ]
    [SetLike β B] [AddSubgroupClass β B] (𝒩 : ℤ → β) [Decomposition 𝒩]
    (φ : A →ₗ[R] B) (hφ : ∀ i (a : A), a ∈ ℳ i → φ a ∈ 𝒩 i) (i : ℤ) (a : A) :
    (decompose 𝒩 (φ a) i : B) = φ (decompose ℳ a i : A) := by
  induction a using DirectSum.Decomposition.inductionOn (ℳ := ℳ) with
  | zero => simp
  | @homogeneous j a =>
      by_cases h : j = i
      · subst h
        rw [decompose_of_mem_same ℳ a.2, decompose_of_mem_same 𝒩 (hφ j a.1 a.2)]
      · rw [decompose_of_mem_ne ℳ a.2 h, decompose_of_mem_ne 𝒩 (hφ j a.1 a.2) h, map_zero]
  | add a a' ha ha' => simp [ha, ha']

/-- The product of homogeneous elements of degrees `i` and `d` is homogeneous of degree
`i + d`, with the degree written as a natural number cast. -/
private theorem smul_mem_graded_nat {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A]
    [Module R A] {σ' α : Type*} [SetLike σ' R] [AddSubgroupClass σ' R] (𝒜 : ℕ → σ')
    [GradedRing 𝒜] [SetLike α A] [AddSubgroupClass α A] (ℳ : ℤ → α)
    [SetLike.GradedSMul 𝒜 ℳ] {r : R} {a : A} {i d : ℕ} (hr : r ∈ 𝒜 i) (ha : a ∈ ℳ (d : ℤ)) :
    r • a ∈ ℳ ((i + d : ℕ) : ℤ) := by
  simpa only [vadd_nat_int, Nat.cast_add] using
    SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) hr ha

/-- The homogeneous components of `r • a`, for `a` homogeneous, are the products of the
homogeneous components of `r` with `a`. -/
private theorem decompose_smul_of_mem {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A]
    [Module R A] {σ' α : Type*} [SetLike σ' R] [AddSubgroupClass σ' R] (𝒜 : ℕ → σ')
    [GradedRing 𝒜] [SetLike α A] [AddSubgroupClass α A] (ℳ : ℤ → α) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] (r : R) {d : ℕ} {a : A} (ha : a ∈ ℳ (d : ℤ)) (i : ℕ) :
    (decompose ℳ (r • a) ((i + d : ℕ) : ℤ) : A) = (decompose 𝒜 r i : R) • a := by
  induction r using DirectSum.Decomposition.inductionOn (ℳ := 𝒜) with
  | zero => simp
  | @homogeneous j r =>
      have hra := smul_mem_graded_nat 𝒜 ℳ r.2 ha
      by_cases h : j = i
      · subst h
        rw [decompose_of_mem_same 𝒜 r.2, decompose_of_mem_same ℳ hra]
      · rw [decompose_of_mem_ne 𝒜 r.2 h, decompose_of_mem_ne ℳ hra
          (fun hc => h (by simpa using hc)), zero_smul]
  | add r r' hr hr' =>
      push_cast at hr hr'
      simp [add_smul, hr, hr']

variable {S : Type u} {M N P : Type v} {σ : Type w} {τ : Type t} {υ : Type t'} {ρ : Type t''}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [AddCommGroup P] [Module S P]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]
  [SetLike ρ P] [AddSubgroupClass ρ P] (𝒬 : ℤ → ρ) [Decomposition 𝒬]
  [SetLike.GradedSMul 𝒮 𝒬]

/-- The homogeneous ideal of a point `x` of `Proj 𝒮` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The degree-zero prime localization `S₍ₓ₎` acts on the fibre of a module at `x` through its
inclusion into the full localization of `S` at the homogeneous prime of `x`. -/
local instance fiberModuleUngraded {M' : Type*} [AddCommGroup M'] [Module S M']
    (x : ProjectiveSpectrum.top 𝒮) :
    Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M') 𝒮 x) :=
  Module.compHom _ (algebraMap
    (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
    (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))

omit [AddSubgroupClass τ M] [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] in
/-- The degree-zero part of the localization of `M` at `x` is spanned by the single fractions
`m / s` with numerator and denominator homogeneous of the same degree. -/
private theorem degreeZeroModuleAt_eq_span (x : ProjectiveSpectrum.top 𝒮) :
    degreeZeroModuleAt 𝒮 𝒨 x =
      Submodule.span (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        {z | ∃ (d : ℕ) (m : M) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
          m ∈ 𝒨 (d : ℤ) ∧ (s : S) ∈ 𝒮 d ∧ z = LocalizedModule.mk m s} := rfl

omit [AddSubgroupClass τ M] [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] in
/-- A single homogeneous fraction lies in the degree-zero part. -/
private theorem mk_mem_degreeZeroModuleAt (x : ProjectiveSpectrum.top 𝒮) (d : ℕ) (m : M)
    (s : x.asHomogeneousIdeal.toIdeal.primeCompl) (hm : m ∈ 𝒨 (d : ℤ)) (hs : (s : S) ∈ 𝒮 d) :
    LocalizedModule.mk m s ∈ degreeZeroModuleAt 𝒮 𝒨 x := by
  rw [degreeZeroModuleAt_eq_span]
  exact Submodule.subset_span ⟨d, m, s, hm, hs, rfl⟩

omit [Decomposition 𝒨] in
/-- Every element of the degree-zero part is a single homogeneous fraction: the sum of two such
fractions, and the product of one with a degree-zero fraction of `S`, are again of that form. -/
theorem exists_mk_of_mem_degreeZeroModuleAt (x : ProjectiveSpectrum.top 𝒮)
    {z : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x}
    (hz : z ∈ degreeZeroModuleAt 𝒮 𝒨 x) :
    ∃ (d : ℕ) (m : M) (s : x.asHomogeneousIdeal.toIdeal.primeCompl),
      m ∈ 𝒨 (d : ℤ) ∧ (s : S) ∈ 𝒮 d ∧ z = LocalizedModule.mk m s := by
  rw [degreeZeroModuleAt_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
      exact ⟨0, 0, 1, zero_mem _, by simpa using SetLike.one_mem_graded 𝒮,
        (LocalizedModule.zero_mk 1).symm⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨d₁, m₁, s₁, hm₁, hs₁, rfl⟩ := h₁
      obtain ⟨d₂, m₂, s₂, hm₂, hs₂, rfl⟩ := h₂
      refine ⟨d₁ + d₂, (s₂ : S) • m₁ + (s₁ : S) • m₂, s₁ * s₂, ?_,
        SetLike.mul_mem_graded hs₁ hs₂, LocalizedModule.mk_add_mk⟩
      have h₁' := smul_mem_graded_nat 𝒮 𝒨 hs₂ hm₁
      rw [add_comm] at h₁'
      exact add_mem h₁' (smul_mem_graded_nat 𝒮 𝒨 hs₁ hm₂)
  | smul a z _ h =>
      obtain ⟨d, m, s, hm, hs, rfl⟩ := h
      refine ⟨a.deg + d, a.num • m, ⟨a.den, a.den_mem⟩ * s, ?_,
        SetLike.mul_mem_graded a.den_mem_deg hs, ?_⟩
      · exact smul_mem_graded_nat 𝒮 𝒨 a.num_mem_deg hm
      · change HomogeneousLocalization.val a • LocalizedModule.mk m s = _
        rw [HomogeneousLocalization.eq_num_div_den, LocalizedModule.mk_smul_mk]

omit [AddSubgroupClass τ M] [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] in
/-- Given `t` outside the homogeneous prime of `x`, some homogeneous component of `t` lies
outside that prime. -/
private theorem exists_decompose_notMem (x : ProjectiveSpectrum.top 𝒮) {t : S}
    (ht : t ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    ∃ i : ℕ, (decompose 𝒮 t i : S) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := by
  by_contra h
  refine ht ((Ideal.IsHomogeneous.mem_iff 𝒮 x.asHomogeneousIdeal.isHomogeneous).mpr fun i => ?_)
  by_contra hi
  exact h ⟨i, hi⟩

/-- The map on stalks at `x` induced by a degree-preserving linear map of graded modules. -/
noncomputable def associatedModuleSheafStalkMap (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (x : ProjectiveSpectrum.top 𝒮) :
    associatedModuleSheafStalk 𝒮 𝒨 x →+ associatedModuleSheafStalk 𝒮 𝒩 x :=
  ConcreteCategory.hom (CategoryTheory.Limits.colim.map
    (Functor.whiskerLeft (OpenNhds.inclusion x).op
      ((PresheafOfModules.toPresheaf _).map
        (ProjSheafFunctoriality.associatedModuleSheafMap 𝒮 𝒨 𝒩 φ hφ).val)))

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- Under the stalk identifications the induced map on stalks is the localization of the given
map at the homogeneous prime of `x`. -/
private theorem associatedModuleSheafStalkMap_equiv (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (x : ProjectiveSpectrum.top 𝒮)
    (s : associatedModuleSheafStalk 𝒮 𝒨 x) :
    ((associatedModuleSheafStalkEquiv 𝒮 𝒩 x
        (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x s) : degreeZeroModuleAt 𝒮 𝒩 x) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) =
      LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ
        (associatedModuleSheafStalkEquiv 𝒮 𝒨 x s : degreeZeroModuleAt 𝒮 𝒨 x) :=
  associatedModuleSheafMap_stalk 𝒮 𝒨 𝒩 φ hφ x s

omit [Decomposition 𝒨] [Decomposition 𝒩] in
/-- An injective degree-preserving map induces an injective map on stalks. -/
private theorem associatedModuleSheafStalkMap_injective (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (hinj : Function.Injective φ)
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Injective (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x) := by
  intro a b hab
  refine (associatedModuleSheafStalkEquiv 𝒮 𝒨 x).injective (Subtype.ext ?_)
  refine LocalizedModule.map_injective _ φ hinj ?_
  rw [← associatedModuleSheafStalkMap_equiv 𝒮 𝒨 𝒩 φ hφ x a,
    ← associatedModuleSheafStalkMap_equiv 𝒮 𝒨 𝒩 φ hφ x b, hab]

omit [Decomposition 𝒨] [Decomposition 𝒩] [Decomposition 𝒬] in
/-- The composition of the two induced maps on stalks vanishes. -/
private theorem associatedModuleSheafStalkMap_comp_eq_zero (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (ψ : N →ₗ[S] P)
    (hψ : ∀ i (n : N), n ∈ 𝒩 i → ψ n ∈ 𝒬 i) (hcomp : ∀ m : M, ψ (φ m) = 0)
    (x : ProjectiveSpectrum.top 𝒮) (a : associatedModuleSheafStalk 𝒮 𝒨 x) :
    associatedModuleSheafStalkMap 𝒮 𝒩 𝒬 ψ hψ x
        (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x a) = 0 := by
  have key : ∀ z : ProjectiveSpectrum.Proj.ModuleFiber (M := M) 𝒮 x,
      LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl ψ
        (LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ z) = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | _ m s => simp [hcomp m]
  apply (associatedModuleSheafStalkEquiv 𝒮 𝒬 x).injective
  rw [map_zero]
  apply Subtype.ext
  rw [associatedModuleSheafStalkMap_equiv, associatedModuleSheafStalkMap_equiv, key]
  simp

/-- If `φ m` is homogeneous of degree `e`, then for `s` homogeneous of degree `e` outside the
prime of `x` the fraction `φ m / s` is the image of a stalk element. -/
private theorem exists_stalkMap_eq_mk (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (x : ProjectiveSpectrum.top 𝒮) {e : ℕ} {m : M}
    (hm : φ m ∈ 𝒩 (e : ℤ)) (s : x.asHomogeneousIdeal.toIdeal.primeCompl) (hs : (s : S) ∈ 𝒮 e) :
    ∃ a, ((associatedModuleSheafStalkEquiv 𝒮 𝒩 x
        (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x a) : degreeZeroModuleAt 𝒮 𝒩 x) :
        ProjectiveSpectrum.Proj.ModuleFiber (M := N) 𝒮 x) = LocalizedModule.mk (φ m) s := by
  have hdec := decompose_map 𝒨 𝒩 φ hφ (e : ℤ) m
  rw [decompose_of_mem_same 𝒩 hm] at hdec
  obtain ⟨a, ha⟩ := (associatedModuleSheafStalkEquiv 𝒮 𝒨 x).surjective
    ⟨LocalizedModule.mk (decompose 𝒨 m (e : ℤ) : M) s,
      mk_mem_degreeZeroModuleAt 𝒮 𝒨 x e _ s (decompose 𝒨 m (e : ℤ)).2 hs⟩
  refine ⟨a, ?_⟩
  rw [associatedModuleSheafStalkMap_equiv, ha]
  change LocalizedModule.map _ φ (LocalizedModule.mk (decompose 𝒨 m (e : ℤ) : M) s) = _
  rw [LocalizedModule.map_mk, hdec]

/-- A surjective degree-preserving map induces a surjective map on stalks: a homogeneous
fraction of `P₍𝔭₎` is the image of the fraction with the same denominator whose numerator is the
homogeneous component of a preimage. -/
private theorem associatedModuleSheafStalkMap_surjective (ψ : N →ₗ[S] P)
    (hψ : ∀ i (n : N), n ∈ 𝒩 i → ψ n ∈ 𝒬 i) (hsurj : Function.Surjective ψ)
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Surjective (associatedModuleSheafStalkMap 𝒮 𝒩 𝒬 ψ hψ x) := by
  intro c
  obtain ⟨d, p, s, hp, hs, hz⟩ := exists_mk_of_mem_degreeZeroModuleAt 𝒮 𝒬 x
    (associatedModuleSheafStalkEquiv 𝒮 𝒬 x c).2
  obtain ⟨n, hn⟩ := hsurj p
  obtain ⟨b, hb⟩ := exists_stalkMap_eq_mk 𝒮 𝒩 𝒬 ψ hψ x (m := n) (hn ▸ hp) s hs
  exact ⟨b, (associatedModuleSheafStalkEquiv 𝒮 𝒬 x).injective (Subtype.ext (by rw [hb, hn, hz]))⟩

/-- The stalk sequence is exact in the middle: a homogeneous fraction of `N₍𝔭₎` killed in
`P₍𝔭₎` is killed after multiplying its numerator by a homogeneous element `w` outside `𝔭`, and
a homogeneous preimage of `w • n` divided by `w` times the denominator is a preimage of it. -/
private theorem associatedModuleSheafStalkMap_exact (φ : M →ₗ[S] N)
    (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) (ψ : N →ₗ[S] P)
    (hψ : ∀ i (n : N), n ∈ 𝒩 i → ψ n ∈ 𝒬 i) (hexact : Function.Exact φ ψ)
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Exact (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x)
      (associatedModuleSheafStalkMap 𝒮 𝒩 𝒬 ψ hψ x) := by
  intro b
  refine ⟨fun hb => ?_, ?_⟩
  · obtain ⟨d, n, s, hn, hs, hz⟩ := exists_mk_of_mem_degreeZeroModuleAt 𝒮 𝒩 x
      (associatedModuleSheafStalkEquiv 𝒮 𝒩 x b).2
    have h0 : LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl ψ
        (LocalizedModule.mk n s) = 0 := by
      rw [← hz, ← associatedModuleSheafStalkMap_equiv 𝒮 𝒩 𝒬 ψ hψ x b, hb]
      simp
    rw [LocalizedModule.map_mk,
      show (0 : ProjectiveSpectrum.Proj.ModuleFiber (M := P) 𝒮 x) = LocalizedModule.mk 0 1 from
        (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    have hu' : (u : S) • ψ n = 0 := by
      simp only [one_smul, smul_zero] at hu
      exact hu
    obtain ⟨i, hi⟩ := exists_decompose_notMem 𝒮 x u.2
    have hw : (decompose 𝒮 (u : S) i : S) • ψ n = 0 := by
      have h := decompose_smul_of_mem 𝒮 𝒬 (u : S) (hψ (d : ℤ) n hn) i
      rw [hu'] at h
      simpa using h.symm
    have hwn : ψ ((decompose 𝒮 (u : S) i : S) • n) = 0 := by rwa [map_smul]
    obtain ⟨m, hm⟩ := (hexact ((decompose 𝒮 (u : S) i : S) • n)).mp hwn
    obtain ⟨a, ha⟩ := exists_stalkMap_eq_mk 𝒮 𝒨 𝒩 φ hφ x (m := m)
      (hm ▸ smul_mem_graded_nat 𝒮 𝒩 (decompose 𝒮 (u : S) i).2 hn)
      (⟨(decompose 𝒮 (u : S) i : S), hi⟩ * s)
      (SetLike.mul_mem_graded (decompose 𝒮 (u : S) i).2 hs)
    refine ⟨a, (associatedModuleSheafStalkEquiv 𝒮 𝒩 x).injective (Subtype.ext ?_)⟩
    rw [ha, hm, hz]
    exact LocalizedModule.mk_cancel_common_left ⟨(decompose 𝒮 (u : S) i : S), hi⟩ s n
  · rintro ⟨a, rfl⟩
    exact associatedModuleSheafStalkMap_comp_eq_zero 𝒮 𝒨 𝒩 𝒬 φ hφ ψ hψ
      (fun m => (hexact (φ m)).mpr ⟨m, rfl⟩) x a

/-- **Stacks Project, Tag 01M7.** The functor `M ↦ M̃` is exact: at every point of `Proj(S)`
the stalks of a short exact sequence of graded `S`-modules with degree-preserving maps form a
short exact sequence.

This is the form the source proves it in. The passage from exactness on all stalks to exactness
in the category of sheaves of `𝒪_{Proj(S)}`-modules is the lemma the source cites for it, Tag
01AG, which is `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` in
`StacksFrontier/Topology/Sheaves/Modules/Exactness.lean`; the sheaf-level statement it yields, that
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor` is exact into
`SheafOfModules`, is
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafFunctor_shortExact` in
`StacksFrontier/AlgebraicGeometry/ProjSheafFunctoriality/Exactness.lean`. -/
theorem associatedModuleSheafStalkMap_shortExact
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i)
    (ψ : N →ₗ[S] P) (hψ : ∀ i (n : N), n ∈ 𝒩 i → ψ n ∈ 𝒬 i)
    (hinj : Function.Injective φ) (hsurj : Function.Surjective ψ)
    (hexact : Function.Exact φ ψ) (x : ProjectiveSpectrum.top 𝒮) :
    Function.Injective (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x) ∧
      Function.Exact (associatedModuleSheafStalkMap 𝒮 𝒨 𝒩 φ hφ x)
        (associatedModuleSheafStalkMap 𝒮 𝒩 𝒬 ψ hψ x) ∧
      Function.Surjective (associatedModuleSheafStalkMap 𝒮 𝒩 𝒬 ψ hψ x) :=
  ⟨associatedModuleSheafStalkMap_injective 𝒮 𝒨 𝒩 φ hφ hinj x,
    associatedModuleSheafStalkMap_exact 𝒮 𝒨 𝒩 𝒬 φ hφ ψ hψ hexact x,
    associatedModuleSheafStalkMap_surjective 𝒮 𝒩 𝒬 ψ hψ hsurj x⟩

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

end
