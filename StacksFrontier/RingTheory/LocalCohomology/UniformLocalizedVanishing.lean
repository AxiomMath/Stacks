module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A uniform bound for the localized vanishing of a direct system of finite modules

Let `A` be a commutative ring, `G : ℕ ⥤ Mod(A)` a direct system of `A`-modules and `m` an index
whose term `G(m)` is a Noetherian `A`-module. Suppose that for every prime `𝔭` in a set `T` of
primes *some* transition map out of `G(m)` dies after localization at `𝔭`. Then one index works
for every prime at once: there is a `k₀ ≥ m` such that for all `k ≥ k₀` and all `𝔭 ∈ T` the
localization at `𝔭` of `G(m) ⟶ G(k)` is zero.

The reason is that the kernels `ker(G(m) ⟶ G(k))` form an **increasing** chain of submodules of
the single Noetherian module `G(m)`, so the chain is constant from some index `k₀` on; and the
localization at `𝔭` of `G(m) ⟶ G(k)` is determined, as far as its vanishing goes, by that kernel
(`Stacks.LocalCohomology.localizedModuleFunctor_map_eq_zero_of_ker_le`). Beyond `k₀` the
transition maps out of `G(m)` therefore all vanish at exactly the same primes, and at each
`𝔭 ∈ T` one of them vanishes.

This is the uniformity step of the proof of [Stacks, Tag 0EFX]. The source obtains it by
spreading the vanishing of a map of finite modules out over an open neighbourhood of `𝔮` and
covering a level set of the dimension function, which is quasi-compact because `Spec(A)` is a
Noetherian topological space. The argument here replaces both the neighbourhood and the covering
by the ascending chain condition in one module, and so needs neither the topology of the locus
nor a stratification of it: the bound `k₀` depends on `m` alone.

## Main results

* `Stacks.LocalCohomology.localizedModuleFunctor_map_eq_zero_of_ker_le` — if the kernel of
  `ψ : M ⟶ P` is contained in the kernel of `φ : M ⟶ N` and `ψ` dies after localization, so
  does `φ`.
* `Stacks.LocalCohomology.ker_map_le_ker_map` — the kernels of the transition maps out of a
  fixed term of a direct system increase with the target index.
* `Stacks.LocalCohomology.exists_forall_localized_map_eq_zero` — the uniform bound.

## Implementation notes

The first lemma is proved on fractions rather than through the factorization of `φ` and `ψ`
through the quotient by their common kernel: a fraction `x/s` is sent to `φ(x)/s`, and the
vanishing of `ψ(x)/s` produces a `c` in the multiplicative subset with `c • x` in the kernel of
`ψ`, hence in the kernel of `φ`, which is exactly the statement that `φ(x)/s` vanishes. The
containment of kernels is all that is used, which is why the hypothesis is an inequality rather
than the equality the chain condition supplies.

The index set of the chain is shifted to `d ↦ ker(G(m) ⟶ G(m + d))`, so that it is a monotone
function on `ℕ` as `Mathlib`'s chain condition expects; the bound `k₀` is then `m + d₀`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- **A localized map dies as soon as a map with a smaller kernel does.** If `ψ : M ⟶ P` has
kernel contained in the kernel of `φ : M ⟶ N` and the localization of `ψ` at a multiplicative
subset `S` vanishes, then so does the localization of `φ`.

A general element of `M_S` is a fraction `x/s`, which `φ` sends to `φ(x)/s`. The vanishing of
`ψ(x)/s` gives a `c ∈ S` with `c • x` in the kernel of `ψ`, hence in the kernel of `φ`; so
`c • φ(x) = 0` and `φ(x)/s = 0`. -/
theorem localizedModuleFunctor_map_eq_zero_of_ker_le (S : Submonoid A)
    {M N P : ModuleCat.{max u v} A} (φ : M ⟶ N) (ψ : M ⟶ P)
    (hker : LinearMap.ker ψ.hom ≤ LinearMap.ker φ.hom)
    (h : (ModuleCat.localizedModuleFunctor.{max u v} S).map ψ = 0) :
    (ModuleCat.localizedModuleFunctor.{max u v} S).map φ = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (M.localizedModuleMkLinearMap S) z
  have hψ : IsLocalizedModule.mk' (P.localizedModuleMkLinearMap S) (ψ.hom x) s = 0 := by
    rw [← IsLocalizedModule.map_mk' S (M.localizedModuleMkLinearMap S)
      (P.localizedModuleMkLinearMap S) ψ.hom x s]
    exact congrArg (fun g => ModuleCat.Hom.hom g
      (IsLocalizedModule.mk' (M.localizedModuleMkLinearMap S) x s)) h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.mk'_eq_zero' (P.localizedModuleMkLinearMap S) s).1 hψ
  have hcx : (c : A) • x ∈ LinearMap.ker ψ.hom := by
    have : ψ.hom ((c : A) • x) = (c : A) • ψ.hom x := map_smul _ _ _
    exact this.trans hc
  have hφ : (c : A) • φ.hom x = 0 := by
    have : φ.hom ((c : A) • x) = (c : A) • φ.hom x := map_smul _ _ _
    exact this.symm.trans (hker hcx)
  refine Eq.trans ?_ ((IsLocalizedModule.mk'_eq_zero'
    (N.localizedModuleMkLinearMap S) s).2 ⟨c, hφ⟩)
  exact IsLocalizedModule.map_mk' S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) φ.hom x s

/-- A functor out of `ℕ` sends `a ≤ c` to the composite of its values at `a ≤ b` and `b ≤ c`. -/
private theorem map_homOfLE_eq_comp {C : Type*} [Category C] (F : ℕ ⥤ C) {a b c : ℕ}
    (h : a ≤ b) (h' : a ≤ c) (hbc : b ≤ c) :
    F.map (homOfLE h') = F.map (homOfLE h) ≫ F.map (homOfLE hbc) := by
  rw [← F.map_comp, homOfLE_comp]

/-- **The kernels of the transition maps out of a fixed term increase.** For `m ≤ k ≤ k'` the
kernel of `G(m) ⟶ G(k)` is contained in the kernel of `G(m) ⟶ G(k')`, because the second map is
the first followed by `G(k) ⟶ G(k')`. -/
theorem ker_map_le_ker_map (G : ℕ ⥤ ModuleCat.{max u v} A) {m k k' : ℕ}
    (h : m ≤ k) (h' : m ≤ k') (hkk' : k ≤ k') :
    LinearMap.ker (G.map (homOfLE h)).hom ≤ LinearMap.ker (G.map (homOfLE h')).hom := by
  intro x hx
  show (G.map (homOfLE h')).hom x = 0
  rw [map_homOfLE_eq_comp G h h' hkk']
  show (G.map (homOfLE hkk')).hom ((G.map (homOfLE h)).hom x) = 0
  rw [show (G.map (homOfLE h)).hom x = 0 from hx, map_zero]

/-- A transition map out of a fixed term stays zero after localization once it is zero: the map
with the larger target factors through it. -/
theorem localized_map_eq_zero_of_le (G : ℕ ⥤ ModuleCat.{max u v} A) (S : Submonoid A)
    {m k k' : ℕ} (h : m ≤ k) (h' : m ≤ k') (hkk' : k ≤ k')
    (hz : (G ⋙ ModuleCat.localizedModuleFunctor.{max u v} S).map (homOfLE h) = 0) :
    (G ⋙ ModuleCat.localizedModuleFunctor.{max u v} S).map (homOfLE h') = 0 := by
  rw [map_homOfLE_eq_comp _ h h' hkk', hz, Limits.zero_comp]

/-- **One index serves every prime at once.** Let `G` be a direct system of `A`-modules whose
term at `m` is Noetherian, and let `T` be a set of primes of `A` such that at every `𝔭 ∈ T`
some transition map `G(m) ⟶ G(k)` vanishes after localization at `𝔭`. Then there is a `k₀ ≥ m`
such that the localization at `𝔭` of `G(m) ⟶ G(k)` vanishes for **every** `k ≥ k₀` and every
`𝔭 ∈ T`.

The kernels of the transition maps out of `G(m)` form an increasing chain of submodules of the
Noetherian module `G(m)`, hence are constant from some index `k₀` on. Given `k ≥ k₀` and
`𝔭 ∈ T`, choose an index `k₁` at which the localized map vanishes; past `max k k₁` the map still
vanishes, and its kernel agrees with that of `G(m) ⟶ G(k)`, so the latter vanishes too.

This is the uniformity the last paragraph of the proof of [Stacks, Tag 0EFX] needs, in the form
in which the finite Ext modules `Ext^j_A(IⁿM, ω_A^•)` supply it. -/
theorem exists_forall_localized_map_eq_zero (G : ℕ ⥤ ModuleCat.{max u v} A) (m : ℕ)
    (hnoeth : IsNoetherian A (G.obj m)) (T : Set (PrimeSpectrum A))
    (hex : ∀ p ∈ T, ∃ (k : ℕ) (h : m ≤ k),
      (G ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl).map
        (homOfLE h) = 0) :
    ∃ (k₀ : ℕ) (h₀ : m ≤ k₀), ∀ (k : ℕ) (hk : k₀ ≤ k), ∀ p ∈ T,
      (G ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl).map
        (homOfLE (h₀.trans hk)) = 0 := by
  obtain ⟨d₀, hd₀⟩ := monotone_stabilizes_iff_noetherian.2 hnoeth
    (⟨fun d => LinearMap.ker (G.map (homOfLE (Nat.le_add_right m d))).hom,
      fun d d' hdd' => ker_map_le_ker_map.{u, v} G (Nat.le_add_right m d)
        (Nat.le_add_right m d') (by omega)⟩ : ℕ →o Submodule A (G.obj m))
  refine ⟨m + d₀, Nat.le_add_right m d₀, fun k hk p hp => ?_⟩
  obtain ⟨k₁, h₁, hk₁⟩ := hex p hp
  obtain ⟨e, rfl⟩ : ∃ e, k = m + e := ⟨k - m, by omega⟩
  have hd₀e : d₀ ≤ e := by omega
  have hmk₂ : m ≤ m + (e + k₁) := Nat.le_add_right _ _
  have h1k₂ : k₁ ≤ m + (e + k₁) := by omega
  have hzero₂ : (G ⋙ ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl).map
      (homOfLE hmk₂) = 0 :=
    localized_map_eq_zero_of_le.{u, v} G _ h₁ hmk₂ h1k₂ hk₁
  have hkereq : LinearMap.ker (G.map (homOfLE hmk₂)).hom ≤
      LinearMap.ker (G.map (homOfLE (Nat.le_add_right m e))).hom :=
    (((hd₀ (e + k₁) (by omega)).symm.trans (hd₀ e hd₀e)) :
      LinearMap.ker (G.map (homOfLE (Nat.le_add_right m (e + k₁)))).hom =
        LinearMap.ker (G.map (homOfLE (Nat.le_add_right m e))).hom).le
  exact localizedModuleFunctor_map_eq_zero_of_ker_le.{u, v} p.asIdeal.primeCompl
    (G.map (homOfLE (Nat.le_add_right m e))) (G.map (homOfLE hmk₂)) hkereq hzero₂

end Stacks.LocalCohomology

end
