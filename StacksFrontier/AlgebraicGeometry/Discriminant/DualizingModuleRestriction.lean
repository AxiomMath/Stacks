module

public import StacksFrontier.AlgebraicGeometry.Discriminant.LocalAnnihilation
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison

/-!
# The canonical comparison restricts a functional

The relative dualizing modules of two finite-open factorizations of the same quasi-finite
algebra are canonically identified. When the intermediate algebra of the first maps to that of
the second, compatibly with the maps to the target, that identification should send a pure
tensor to the pure tensor whose functional is restricted along the map. This file proves it
under a hypothesis that is local on the target, and deduces the case of an isomorphism of
intermediate algebras.

## Main results

* `Stacks.Discriminant.comparison_restrict_of_local_annihilation`: the canonical comparison
  restricts a functional along a map of intermediate algebras, under local annihilation of the
  kernel.
* `Stacks.Discriminant.comparison_restrict_of_equiv`: the same for an isomorphism of
  intermediate algebras.

## Implementation notes

The difference of the two sides is an element of the relative dualizing module, and the scalars
annihilating it form an ideal. The local hypothesis produces, at every maximal ideal, a power of
an element outside it that annihilates the difference, so the ideal is not contained in any
maximal ideal and is therefore everything.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v w x

open Topology
open scoped TensorProduct

attribute [local instance] algebraDualModule



/-- The canonical comparison of the relative dualizing modules of two finite-open
factorizations restricts a functional along a map of intermediate algebras, provided the kernel
of the second intermediate algebra in the target is, locally on the target, annihilated by a
power of an element of the first. -/
theorem comparison_restrict_of_local_annihilation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hloc : ∀ p : PrimeSpectrum B, ∃ c : F.middle,
      algebraMap F.middle B c ∉ p.asIdeal ∧
        ∃ n : ℕ, ∀ k : H.middle, algebraMap H.middle B k = 0 → (r c) ^ n * k = 0)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv H F (dualizingModule.tmul H φ b) =
      dualizingModule.tmul F (φ.comp r.toLinearMap) b := by
  obtain ⟨K, q, hq, hK, hqB⟩ := exists_image_factorization H
  let e := dualizingModuleEquiv H F
  let δ := e (dualizingModule.tmul H φ b) -
    dualizingModule.tmul F (φ.comp r.toLinearMap) b
  let I : Ideal B := (LinearMap.toSpanSingleton B (dualizingModule F) δ).ker
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal hne
    let p : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    obtain ⟨c, hc, n, hn⟩ := hloc p
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_factor_functional q.toLinearMap hq ((r c) ^ n • φ) (by
      intro k hk
      have hkB : algebraMap H.middle B k = 0 := by
        rw [← hqB, show q k = 0 from hk, map_zero]
      show φ ((r c) ^ n * k) = 0
      rw [hn k hkB, map_zero])
    have hψr : ψ.comp (q.comp r).toLinearMap = c ^ n • (φ.comp r.toLinearMap) := by
      ext z
      have hh := DFunLike.congr_fun hψ (r z)
      simpa [algebraDualModule_smul_apply, map_mul, map_pow] using hh
    have heq := dualizingModuleEquiv_tmul H F K hK q (q.comp r)
      hqB (fun c => (hqB (r c)).trans (hr c)) ψ b
    simp only [hψ, hψr] at heq
    rw [dualizingModule.tmul_dual_smul, dualizingModule.tmul_dual_smul, map_smul] at heq
    rw [map_pow, hr c, map_pow] at heq
    have hmem : algebraMap F.middle B c ^ n ∈ I := by
      show algebraMap F.middle B c ^ n • δ = 0
      exact (smul_sub _ _ _).trans (sub_eq_zero.mpr heq)
    have hp : algebraMap F.middle B c ∈ P := hP.isPrime.mem_of_pow_mem n (hIP hmem)
    exact hc hp
  have hz : (1 : B) ∈ I := htop ▸ Submodule.mem_top
  have hδ : δ = 0 := by simpa [I] using hz
  exact sub_eq_zero.mp hδ

/-- The canonical comparison of the relative dualizing modules of two finite-open
factorizations with isomorphic intermediate algebras restricts a functional along that
isomorphism. -/
theorem comparison_restrict_of_equiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (H : FiniteOpenFactorization.{u, v, x} A B)
    (e : F.middle ≃ₐ[A] H.middle)
    (he : ∀ c : F.middle,
      algebraMap H.middle B (e c) = algebraMap F.middle B c)
    (φ : Module.Dual A H.middle) (b : B) :
    dualizingModuleEquiv H F
        (dualizingModule.tmul H φ b) =
      dualizingModule.tmul F (φ.comp e.toLinearMap) b := by
  let hloc : ∀ p : PrimeSpectrum B, ∃ c : F.middle,
      algebraMap F.middle B c ∉ p.asIdeal ∧
        ∃ n : ℕ, ∀ k : H.middle,
          algebraMap H.middle B k = 0 → (e c) ^ n * k = 0 := by
    intro p
    let pF := PrimeSpectrum.comap (algebraMap F.middle B) p
    obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, hpc, hc⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
        (show pF ∈ Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) from ⟨p, rfl⟩)
        F.isOpenEmbedding_comap.isOpen_range
    have hnot : algebraMap F.middle B c ∉ p.asIdeal := by
      simpa [pF, PrimeSpectrum.comap_asIdeal] using hpc
    have hFaway := F.awayMap_bijective c hc
    let : IsNoetherianRing H.middle :=
      isNoetherianRing_iff.mpr (isNoetherian_of_tower A inferInstance)
    let I : Ideal H.middle := RingHom.ker (algebraMap H.middle B)
    have hker : ∀ k ∈ I, ∃ n : ℕ, (e c) ^ n * k = 0 := by
      intro k hk
      have hkB : algebraMap H.middle B k = 0 := RingHom.mem_ker.mp hk
      let x := e.symm k
      have hxB : algebraMap F.middle B x = 0 := by
        rw [← he x]
        simpa [x] using hkB
      have hzero :
          Localization.awayMap (algebraMap F.middle B) c
            (algebraMap F.middle (Localization.Away c) x) = 0 := by
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
        simp [hxB]
      have hlocalzero : algebraMap F.middle (Localization.Away c) x = 0 := by
        apply hFaway.1
        simpa using hzero
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq c
        (hlocalzero.trans (map_zero _).symm)
      have hn' : c ^ n * x = 0 := by simpa using hn
      have heq := congrArg e.toRingHom hn'
      exact ⟨n, by simpa [x, map_mul, map_pow] using heq⟩
    obtain ⟨n, hn⟩ := Submodule.exists_uniform_pow_annihilator I
      (IsNoetherian.noetherian I) (e c) (by
        intro k hk
        obtain ⟨m, hm⟩ := hker k hk
        exact ⟨m, by simpa [Algebra.smul_def] using hm⟩)
    refine ⟨c, hnot, n, ?_⟩
    intro k hk
    exact hn k (RingHom.mem_ker.mpr hk)
  exact comparison_restrict_of_local_annihilation F H e.toAlgHom he hloc φ b

end Stacks.Discriminant
