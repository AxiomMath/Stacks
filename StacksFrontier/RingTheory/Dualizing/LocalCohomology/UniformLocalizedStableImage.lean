module

public import StacksFrontier.RingTheory.LocalCohomology.UniformLocalizedVanishing
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalizedStableImageTransport

/-!
# A uniform bound for the localized stable image of a direct system of finite modules

Let `A` be a commutative ring and `G : ℕ ⥤ Mod(A)` a direct system whose term `G(m)` is a
Noetherian `A`-module. Say that the system has **stable image at `(m, k)` over a prime `𝔭`** when,
after localization at `𝔭`, every value of `G(m) ⟶ G(k)` is a value of `G(0) ⟶ G(k)`. If that
holds at *some* `k` for every prime `𝔭` of a set `T`, then it holds at **one** index for every
`𝔭 ∈ T` at once, and at every larger index.

This is the exact analogue, for the stable-image half of [Stacks, Tag 0EFX], of
`Stacks.LocalCohomology.exists_forall_localized_map_eq_zero` for the pro-zero half, and it rests
on the same chain condition: the kernels `ker(G(m) ⟶ G(k))` form an increasing chain of
submodules of the single Noetherian module `G(m)`, hence are constant from some index `k₀` on.

Why the chain condition suffices is a short computation. Since `G(0) ⟶ G(k)` factors through
`G(m) ⟶ G(k)`, the stable image at `(m, k)` says precisely that

`G(m)_𝔭 = (image of G(0) ⟶ G(m))_𝔭 + ker(G(m) ⟶ G(k))_𝔭`,

and the right-hand side only grows with `k`. So the condition is monotone in `k`, and beyond the
stabilization index of the chain the kernel no longer grows: one index therefore serves every
prime at which the condition holds at all. As in the pro-zero half this replaces the source's
spreading-out over a neighbourhood of `𝔮` together with the quasi-compactness of the locus.

## Main results

* `Stacks.Algebraization.ker_localizedModule_map_le_of_ker_le` — a containment of kernels survives
  localization.
* `Stacks.Algebraization.exists_forall_localized_stableImage` — the uniform bound.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- **A containment of kernels survives localization.** If the kernel of `ψ : M ⟶ P` is contained
in the kernel of `φ : M ⟶ N`, the same holds after localization at a multiplicative subset.

A general element of `M_S` is a fraction `x/s`, and `ψ(x)/s = 0` produces a `c ∈ S` with `c • x`
in the kernel of `ψ`, hence in that of `φ`; so `c • φ(x) = 0` and `φ(x)/s = 0`. This is the
kernel-containment form of
`Stacks.LocalCohomology.localizedModuleFunctor_map_eq_zero_of_ker_le`, in the model of the
localization functor whose carrier is `LocalizedModule`. -/
theorem ker_localizedModule_map_le_of_ker_le (S : Submonoid A)
    {M N P : ModuleCat.{u} A} (φ : M ⟶ N) (ψ : M ⟶ P)
    (hker : LinearMap.ker ψ.hom ≤ LinearMap.ker φ.hom) :
    LinearMap.ker ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map ψ).hom ≤
      LinearMap.ker ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map φ).hom := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) z
  have hψ : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S P) (ψ.hom x) s = 0 := by
    rw [← IsLocalizedModule.map_mk' S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S P) ψ.hom x s]
    exact hz
  obtain ⟨c, hc⟩ := (IsLocalizedModule.mk'_eq_zero' (LocalizedModule.mkLinearMap S P) s).1 hψ
  have hcx : (c : A) • x ∈ LinearMap.ker ψ.hom := (map_smul ψ.hom (c : A) x).trans hc
  have hφ : (c : A) • φ.hom x = 0 := (map_smul φ.hom (c : A) x).symm.trans (hker hcx)
  refine Eq.trans ?_ ((IsLocalizedModule.mk'_eq_zero'
    (LocalizedModule.mkLinearMap S N) s).2 ⟨c, hφ⟩)
  exact IsLocalizedModule.map_mk' S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) φ.hom x s

/-- A transition map of a localized direct system, split through an intermediate index, read on an
element. -/
theorem localizedModule_map_apply_split (G : ℕ ⥤ ModuleCat.{u} A) (S : Submonoid A)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c)
    (x : (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).obj (G.obj a)) :
    ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
        (G.map (homOfLE hac))).hom x =
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
        (G.map (homOfLE hbc))).hom
        (((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
          (G.map (homOfLE hab))).hom x) := by
  have hc : G.map (homOfLE hac) = G.map (homOfLE hab) ≫ G.map (homOfLE hbc) :=
    (congrArg G.map (Subsingleton.elim _ _)).trans (G.map_comp (homOfLE hab) (homOfLE hbc))
  exact ConcreteCategory.congr_hom
    ((congrArg (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map hc).trans
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map_comp _ _)) x

/-- The stable image at `(m, k)` is monotone in `k`: the maps out of `G(m)` and `G(0)` at a larger
index are the old ones followed by one and the same transition map. -/
theorem localized_stableImage_of_le (G : ℕ ⥤ ModuleCat.{u} A) (S : Submonoid A)
    {m k k' : ℕ} (h : m ≤ k) (h' : m ≤ k') (hkk' : k ≤ k')
    (hst : ∀ y, ∃ z,
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
        (G.map (homOfLE h))).hom y =
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
        (G.map (homOfLE (Nat.zero_le k)))).hom z) :
    ∀ y, ∃ z,
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
        (G.map (homOfLE h'))).hom y =
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).map
        (G.map (homOfLE (Nat.zero_le k')))).hom z := by
  intro y
  obtain ⟨z, hz⟩ := hst y
  refine ⟨z, ?_⟩
  rw [localizedModule_map_apply_split.{u} G S h hkk' h' y,
    localizedModule_map_apply_split.{u} G S (Nat.zero_le k) hkk' (Nat.zero_le k') z, hz]

/-- **One index serves every prime at once.** Let `G` be a direct system of `A`-modules whose term
at `m` is Noetherian, and let `T` be a set of primes of `A` such that at every `𝔭 ∈ T` the system
has stable image at `(m, k)` for *some* `k ≥ m`. Then there is a `k₀ ≥ m` such that it has stable
image at `(m, k)` for **every** `k ≥ k₀` and every `𝔭 ∈ T`.

The kernels of the transition maps out of `G(m)` form an increasing chain of submodules of the
Noetherian module `G(m)`, hence are constant from some index `k₀` on. Given `k ≥ k₀` and `𝔭 ∈ T`,
choose an index `k₁` where the stable image holds; past `max k k₁` it still holds, and there the
kernel agrees with the one at `k`, so the stable image descends to `k`.

This is the uniformity the last two paragraphs of the proof of [Stacks, Tag 0EFX] need for the
degree `s + 1` assertion, in the form in which the finite Ext modules `Ext^j_A(IⁿM, ω_A^•)` supply
it. -/
theorem exists_forall_localized_stableImage (G : ℕ ⥤ ModuleCat.{u} A) (m : ℕ)
    (hnoeth : IsNoetherian A (G.obj m)) (T : Set (PrimeSpectrum A))
    (hex : ∀ p ∈ T, ∃ (k : ℕ) (h : m ≤ k), ∀ y, ∃ z,
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
          p.asIdeal.primeCompl).map (G.map (homOfLE h))).hom y =
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
          p.asIdeal.primeCompl).map (G.map (homOfLE (Nat.zero_le k)))).hom z) :
    ∃ (k₀ : ℕ) (h₀ : m ≤ k₀), ∀ (k : ℕ) (hk : k₀ ≤ k), ∀ p ∈ T, ∀ y, ∃ z,
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
          p.asIdeal.primeCompl).map (G.map (homOfLE (h₀.trans hk)))).hom y =
      ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
          p.asIdeal.primeCompl).map (G.map (homOfLE (Nat.zero_le k)))).hom z := by
  classical
  obtain ⟨d₀, hd₀⟩ := monotone_stabilizes_iff_noetherian.2 hnoeth
    (⟨fun d => LinearMap.ker (G.map (homOfLE (Nat.le_add_right m d))).hom,
      fun d d' hdd' => Stacks.LocalCohomology.ker_map_le_ker_map.{u, u} G
        (Nat.le_add_right m d) (Nat.le_add_right m d') (by omega)⟩ :
      ℕ →o Submodule A (G.obj m))
  refine ⟨m + d₀, Nat.le_add_right m d₀, fun k hk p hp => ?_⟩
  obtain ⟨k₁, h₁, hk₁⟩ := hex p hp
  obtain ⟨e, rfl⟩ : ∃ e, k = m + e := ⟨k - m, by omega⟩
  have hmk₂ : m ≤ m + (e + k₁) := Nat.le_add_right _ _
  have hkereq : LinearMap.ker (G.map (homOfLE hmk₂)).hom ≤
      LinearMap.ker (G.map (homOfLE (Nat.le_add_right m e))).hom :=
    (((hd₀ (e + k₁) (by omega)).symm.trans (hd₀ e (by omega))) :
      LinearMap.ker (G.map (homOfLE (Nat.le_add_right m (e + k₁)))).hom =
        LinearMap.ker (G.map (homOfLE (Nat.le_add_right m e))).hom).le
  -- transfer the stable image from `m + (e + k₁)` down to `m + e` using the kernel containment
  intro y
  obtain ⟨z, hz⟩ :=
    localized_stableImage_of_le.{u} G p.asIdeal.primeCompl h₁ hmk₂ (by omega) hk₁ y
  refine ⟨z, ?_⟩
  have hzsub : y - ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
        p.asIdeal.primeCompl).map (G.map (homOfLE (Nat.zero_le m)))).hom z ∈
      LinearMap.ker ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u}
        p.asIdeal.primeCompl).map (G.map (homOfLE hmk₂))).hom := by
    rw [LinearMap.mem_ker, map_sub, hz,
      localizedModule_map_apply_split.{u} G p.asIdeal.primeCompl (Nat.zero_le m) hmk₂
        (Nat.zero_le (m + (e + k₁))) z, sub_self]
  have hzsub' := ker_localizedModule_map_le_of_ker_le.{u} p.asIdeal.primeCompl
    (G.map (homOfLE (Nat.le_add_right m e))) (G.map (homOfLE hmk₂)) hkereq hzsub
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hzsub'
  rw [hzsub', localizedModule_map_apply_split.{u} G p.asIdeal.primeCompl (Nat.zero_le m)
    (Nat.le_add_right m e) (Nat.zero_le (m + e)) z]

end Stacks.Algebraization

end
