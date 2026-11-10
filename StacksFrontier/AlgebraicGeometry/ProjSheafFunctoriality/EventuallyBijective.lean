module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.TorsionVanishing

/-!
# Fiberwise bijectivity of a degree-preserving map that is eventually bijective

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring and let `φ : M →ₗ[S] N` be a
degree-preserving linear map of `ℤ`-graded `S`-modules. This file proves that if `φ` restricts
to a bijection `𝒨 j → 𝒩 j` on homogeneous components for every sufficiently large `j`, then at
*every* point `x` of `Proj S` the induced map of localized-module fibers is bijective — with no
hypothesis on the small degrees at all.

This is the local, fiberwise half of the saturation comparison: *a degree-preserving map of
graded `S`-modules that is bijective in all sufficiently large degrees induces an isomorphism of
the associated sheaves on `Proj S`.* The remaining step, lifting fiberwise bijectivity across the
local-fraction condition that cuts out the sections of the associated sheaf, is not carried out
here.

## Main results

* `ProjSheafFunctoriality.decompose_apply_eq`: a degree-preserving linear map commutes with the
  homogeneous decomposition, component by component.
* `ProjSheafFunctoriality.bijective_localizedModule_map_of_eventually_bijective`: **the
  fiberwise bijectivity theorem.**

## The route

Fix a point `x` of `Proj S` and, by
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.exists_homogeneous_pos_degree_notMem`, a
homogeneous `g` of some positive degree `d` outside the prime of `x`. For injectivity, clear the
denominator of a fraction in the kernel to get `φ (u • m) = 0` for some `u` in the primeCompl;
decompose `u • m` into its finitely many homogeneous components and raise *all* of them past the
threshold `N₀` at once with a single power of `g`, chosen as the supremum, over the finite
support, of the exponent each component needs — this is where finiteness of the support is used
and a single `g` outside the prime suffices for every component simultaneously. The commutation
lemma transfers `φ (u • m) = 0` down to each component, and hypothesis `hinj` at the raised
degree kills each one, hence their sum `g ^ k • (u • m)`. For surjectivity, the denominator of the
target fraction is fixed once and for all, and the induction is run on the homogeneous
decomposition of the *numerator*: a single component of degree `j` is raised to degree `≥ N₀` by
one power of `g`, `hsurj` supplies a preimage there, and the sum of two preimages over the *same*
fixed denominator is again a preimage of the sum, by `LocalizedModule.mk_add_mk` with a common
denominator.

## Implementation notes

The index arithmetic combining a `ℕ`-degree of `S` with a `ℤ`-degree of `M` or `N` through
`SetLike.GradedSMul.smul_mem` is phrased with the scoped `ℕ`-smul `k • d` rather than `k * d`, and
the membership conclusions in this file are stated directly against `(k : ℤ) * d + i`: the gap
between the two is closed by `rfl`, since `SetLike.pow_mem_graded`'s nsmul on `ℕ` is definitionally
multiplication, `Nat.cast_mul` is definitional on `ℤ`, and the `ℕ`-on-`ℤ` `VAdd` instance
`Stacks.GradedLocalization.instVAddNatInt` unfolds to the cast-and-add it names.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjSerreCorrespondence (exists_homogeneous_pos_degree_notMem)

namespace Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u v w

attribute [local instance] ProjectiveSpectrum.isPrime

variable {S : Type u} {M N : Type v} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {τ : Type*} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  {υ : Type*} [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

/-- A degree-preserving linear map commutes with the homogeneous decomposition, component by
component. -/
theorem decompose_apply_eq (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i)
    (w : M) (i : ℤ) :
    (DirectSum.decompose 𝒩 (φ w) i : N) = φ (DirectSum.decompose 𝒨 w i : M) := by
  induction w using DirectSum.Decomposition.inductionOn 𝒨 with
  | zero => simp
  | homogeneous m =>
      rename_i j
      rcases eq_or_ne i j with hij | hij
      · subst hij
        rw [DirectSum.decompose_of_mem_same 𝒨 m.2,
          DirectSum.decompose_of_mem_same 𝒩 (hφ i m m.2)]
      · rw [DirectSum.decompose_of_mem_ne 𝒨 m.2 (Ne.symm hij),
          DirectSum.decompose_of_mem_ne 𝒩 (hφ j m m.2) (Ne.symm hij), map_zero]
  | add m m' hm hm' =>
      simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hm,
        hm']

/-- A fraction over a submonoid vanishes exactly when the submonoid kills the numerator. -/
private theorem mk_eq_zero_iff {P : Type*} [AddCommGroup P] [Module S P]
    (T : Submonoid S) (n : P) (s : T) :
    (LocalizedModule.mk n s : LocalizedModule T P) = 0 ↔ ∃ u : T, u • n = 0 := by
  rw [show (0 : LocalizedModule T P) = LocalizedModule.mk 0 1 from
    (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq]
  simp

/-- Two fractions with the same denominator add by adding numerators. -/
private theorem mk_add_mk_same {P : Type*} [AddCommGroup P] [Module S P]
    (T : Submonoid S) (s : T) (n n' : P) :
    (LocalizedModule.mk n s : LocalizedModule T P) + LocalizedModule.mk n' s =
      LocalizedModule.mk (n + n') s := by
  rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]

/-- Raising a degree `i` by `k` multiples of a positive `d` reaches `N₀` once
`(N₀ - i).toNat ≤ k`. -/
private theorem le_mul_add_of_toNat_le {N₀ i : ℤ} {d k : ℕ} (hd : 0 < d)
    (hk : (N₀ - i).toNat ≤ k) : N₀ ≤ (k : ℤ) * d + i := by
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have h0 : (0 : ℤ) ≤ ((N₀ - i).toNat : ℤ) := by positivity
  have h1 : N₀ - i ≤ ((N₀ - i).toNat : ℤ) := Int.self_le_toNat _
  have h2 : ((N₀ - i).toNat : ℤ) ≤ k := by exact_mod_cast hk
  nlinarith

omit [AddSubgroupClass τ M] [Decomposition 𝒨] in
/-- Multiplying by the `k`-th power of a homogeneous element of degree `d` shifts degrees by
`k * d`. -/
private theorem pow_smul_mem_graded {g : S} {d : ℕ} (hg : g ∈ 𝒮 d) (k : ℕ) {i : ℤ} {m : M}
    (hm : m ∈ 𝒨 i) : g ^ k • m ∈ 𝒨 ((k : ℤ) * d + i) :=
  SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) (SetLike.pow_mem_graded k hg) hm

omit [SetLike.GradedSMul 𝒮 𝒩] in
/-- **Fiberwise injectivity.** If a degree-preserving linear map is injective on homogeneous
components in every degree `≥ N₀`, then the induced map of fibers at every point of `Proj S` is
injective. -/
private theorem injective_localizedModule_map_of_eventually_injective
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) {N₀ : ℤ}
    (hinj : ∀ j : ℤ, N₀ ≤ j → ∀ m : M, m ∈ 𝒨 j → φ m = 0 → m = 0)
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Injective
      (LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ :
        ModuleFiber (M := M) 𝒮 x → ModuleFiber (M := N) 𝒮 x) := by
  classical
  set T := x.asHomogeneousIdeal.toIdeal.primeCompl
  obtain ⟨d, hd, g, hg, hgx⟩ := exists_homogeneous_pos_degree_notMem 𝒮 x
  have hkerzero : ∀ w : LocalizedModule T M, LocalizedModule.map T φ w = 0 → w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h m s =>
      intro hw0
      rw [LocalizedModule.map_mk] at hw0
      obtain ⟨u, hu⟩ := (mk_eq_zero_iff T (φ m) s).mp hw0
      rw [Submonoid.smul_def, ← map_smul] at hu
      set F := (DirectSum.decompose 𝒨 ((u : S) • m)).support
      set k := F.sup (fun i => (N₀ - i).toNat)
      have hzero : g ^ k • ((u : S) • m) = 0 := by
        rw [← DirectSum.sum_support_decompose 𝒨 ((u : S) • m), Finset.smul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hphi0 : φ (DirectSum.decompose 𝒨 ((u : S) • m) i : M) = 0 := by
          have hc := decompose_apply_eq (𝒨 := 𝒨) (𝒩 := 𝒩) φ hφ ((u : S) • m) i
          rw [hu, DirectSum.decompose_zero, DirectSum.zero_apply,
            ZeroMemClass.coe_zero] at hc
          exact hc.symm
        exact hinj _
          (le_mul_add_of_toNat_le hd (Finset.le_sup (f := fun i => (N₀ - i).toNat) hi)) _
          (pow_smul_mem_graded 𝒮 𝒨 hg k (DirectSum.decompose 𝒨 ((u : S) • m) i).2)
          (by rw [map_smul, hphi0, smul_zero])
      refine (mk_eq_zero_iff T m s).mpr ⟨⟨g ^ k, T.pow_mem hgx k⟩ * u, ?_⟩
      change (g ^ k * (u : S)) • m = 0
      rw [mul_smul]
      exact hzero
  intro a b hab
  have hsub : LocalizedModule.map T φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (hkerzero _ hsub)

omit [AddSubgroupClass τ M] [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] in
/-- **Fiberwise surjectivity.** If a linear map is surjective onto homogeneous components in every
degree `≥ N₀`, then the induced map of fibers at every point of `Proj S` is surjective. -/
private theorem surjective_localizedModule_map_of_eventually_surjective
    (φ : M →ₗ[S] N) {N₀ : ℤ}
    (hsurj : ∀ j : ℤ, N₀ ≤ j → ∀ n : N, n ∈ 𝒩 j → ∃ m : M, m ∈ 𝒨 j ∧ φ m = n)
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Surjective
      (LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ :
        ModuleFiber (M := M) 𝒮 x → ModuleFiber (M := N) 𝒮 x) := by
  classical
  set T := x.asHomogeneousIdeal.toIdeal.primeCompl
  obtain ⟨d, hd, g, hg, hgx⟩ := exists_homogeneous_pos_degree_notMem 𝒮 x
  intro z
  induction z using LocalizedModule.induction_on with
  | h n s =>
    suffices h : ∃ w : LocalizedModule T M,
        LocalizedModule.map T φ w = LocalizedModule.mk n s by
      obtain ⟨w, hw⟩ := h
      exact ⟨w, hw⟩
    induction n using DirectSum.Decomposition.inductionOn 𝒩 with
    | zero => exact ⟨0, by simp⟩
    | homogeneous n =>
        rename_i j
        set k := (N₀ - j).toNat
        obtain ⟨m, -, hφm⟩ := hsurj _ (le_mul_add_of_toNat_le (i := j) hd le_rfl) _
          (pow_smul_mem_graded 𝒮 𝒩 hg k n.2)
        refine ⟨LocalizedModule.mk m (⟨g ^ k, T.pow_mem hgx k⟩ * s), ?_⟩
        rw [LocalizedModule.map_mk, hφm]
        exact LocalizedModule.mk_cancel_common_left ⟨g ^ k, T.pow_mem hgx k⟩ s (n : N)
    | add n n' hn hn' =>
        obtain ⟨w, hw⟩ := hn
        obtain ⟨w', hw'⟩ := hn'
        exact ⟨w + w', by rw [map_add, hw, hw', mk_add_mk_same]⟩

/-- **Fiberwise bijectivity.** If a degree-preserving linear map `φ : M →ₗ[S] N` of graded
`S`-modules restricts to a bijection on homogeneous components in every degree `≥ N₀`, then at
every point of `Proj S` the induced map of localized-module fibers is bijective. -/
theorem bijective_localizedModule_map_of_eventually_bijective
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) {N₀ : ℤ}
    (hinj : ∀ j : ℤ, N₀ ≤ j → ∀ m : M, m ∈ 𝒨 j → φ m = 0 → m = 0)
    (hsurj : ∀ j : ℤ, N₀ ≤ j → ∀ n : N, n ∈ 𝒩 j → ∃ m : M, m ∈ 𝒨 j ∧ φ m = n)
    (x : ProjectiveSpectrum.top 𝒮) :
    Function.Bijective
      (LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ :
        ModuleFiber (M := M) 𝒮 x → ModuleFiber (M := N) 𝒮 x) :=
  ⟨injective_localizedModule_map_of_eventually_injective 𝒮 𝒨 𝒩 φ hφ hinj x,
    surjective_localizedModule_map_of_eventually_surjective 𝒮 𝒨 𝒩 φ hsurj x⟩

end Stacks.AlgebraicGeometry.ProjSheafFunctoriality

end
