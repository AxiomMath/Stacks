module

public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.Noetherian.DirectSystemTransitionImageRange

/-!
# The vanishing of transition images of kernels at the primes of `V(I)`

Let `G` be a direct system of `A`-modules and `β n : G n → L` a family of maps compatible with its
transition maps. The image of `ker (β n)` in a later term `G m` lies in `ker (β m)`, so it is
unsupported at every prime at which `ker (β m)` is. When every term of `G` is annihilated by a
power of an ideal `I`, these images are unsupported at every prime not containing `I`. Hence the
hypothesis of `Stacks.exists_range_transitionMap_eq_of_forall_prime` on these images needs only to
be checked at the primes of `V(I)`.

## Main results

* `Stacks.range_comp_ker_le_ker_cocone`: the image of `ker (β n)` in `G m` lies in `ker (β m)`.
* `Stacks.notMem_support_range_comp_ker_of_notMem_support_ker`: the image of `ker (β n)` in `G m`
  is unsupported at every prime at which `ker (β m)` is.
* `Stacks.notMem_support_range_comp_ker_of_notMem_zeroLocus`: if the terms of `G` are annihilated
  by powers of `I`, the image of `ker (β n)` in `G m` is unsupported at every prime not containing
  `I`.
* `Stacks.exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus`: the transition images are
  eventually equal as soon as, at each prime of `V(I)`, the image of each `ker (β n)` in some later
  term is unsupported.
* `Stacks.exists_range_transitionMap_eq_of_notMem_support_ker`: the transition images are
  eventually equal as soon as, at each prime of `V(I)`, the kernel of some later `β m` is
  unsupported.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [Stacks Project, Tag 05E6](https://stacks.math.columbia.edu/tag/05E6)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks

variable {A : Type u} [CommRing A]

/-- Let `β n : G n → L` be compatible with the transition maps of a direct system `G` and let
`n ≤ m`. Then the image of `ker (β n)` under `G (n ≤ m)` is contained in `ker (β m)`. -/
theorem range_comp_ker_le_ker_cocone (G : ℕ ⥤ ModuleCat.{v} A) {L : Type w} [AddCommGroup L]
    [Module A L] (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    {n m : ℕ} (h : n ≤ m) :
    LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ (LinearMap.ker (β n)).subtype) ≤
      LinearMap.ker (β m) := by
  rintro - ⟨x, rfl⟩
  exact (LinearMap.congr_fun (hβ n m h) x).trans x.2

/-- If the kernel of `β m` is unsupported at `p` for some `m ≥ n`, then the image of `ker (β n)`
in `G m` is unsupported at `p`. -/
theorem notMem_support_range_comp_ker_of_notMem_support_ker (G : ℕ ⥤ ModuleCat.{v} A)
    {L : Type w} [AddCommGroup L] [Module A L] (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    {n m : ℕ} (h : n ≤ m) {p : PrimeSpectrum A}
    (hp : p ∉ Module.support A (LinearMap.ker (β m) : Type v)) :
    p ∉ Module.support A
      (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
        (LinearMap.ker (β n)).subtype) : Type v) := fun hmem =>
  hp (Module.support_subset_of_injective
    (Submodule.inclusion (range_comp_ker_le_ker_cocone G β hβ h))
    (Submodule.inclusion_injective _) hmem)

/-- If the kernel of some `β m` with `m ≥ n` is unsupported at `p`, then for some `m ≥ n` the
image of `ker (β n)` in `G m` is unsupported at `p`. -/
theorem exists_notMem_support_range_comp_ker_of_exists_notMem_support_ker
    (G : ℕ ⥤ ModuleCat.{v} A) {L : Type w} [AddCommGroup L] [Module A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m) (n : ℕ)
    {p : PrimeSpectrum A}
    (hp : ∃ (m : ℕ) (_ : n ≤ m),
      p ∉ Module.support A (LinearMap.ker (β m) : Type v)) :
    ∃ (m : ℕ) (h : n ≤ m), p ∉ Module.support A
      (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
        (LinearMap.ker (β n)).subtype) : Type v) := by
  obtain ⟨m, h, hm⟩ := hp
  exact ⟨m, h, notMem_support_range_comp_ker_of_notMem_support_ker G β hβ h hm⟩

/-- If every term of the direct system `G` is annihilated by a power of `I`, then at a prime not
containing `I` the image of `ker (β n)` in any later term is unsupported. -/
theorem notMem_support_range_comp_ker_of_notMem_zeroLocus (G : ℕ ⥤ ModuleCat.{v} A)
    {I : Ideal A} (hann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (G.obj n)) = ⊥)
    {L : Type w} [AddCommGroup L] [Module A L] (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    {n m : ℕ} (h : n ≤ m) {p : PrimeSpectrum A} (hp : ¬ I ≤ p.asIdeal) :
    p ∉ Module.support A
      (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
        (LinearMap.ker (β n)).subtype) : Type v) := by
  obtain ⟨k, hk⟩ := hann m
  have htor : IsIPowerTorsion A (G.obj m) I := by
    refine fun x => ⟨k + 1, k.succ_pos, fun a ha => ?_⟩
    have hmem := Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ k) ha)
      (Submodule.mem_top (R := A) (x := x))
    rw [hk] at hmem
    exact (Submodule.mem_bot A).mp hmem
  exact fun hmem => hp ((PrimeSpectrum.mem_zeroLocus _ _).mp
    (support_subset_zeroLocus_of_isIPowerTorsion htor
      (Module.support_subset_of_injective _ (Submodule.injective_subtype _) hmem)))

/-- Let `G` be a direct system of Noetherian modules, each annihilated by a power of `I`, and let
`β n : G n → L` be a compatible family of maps into a Noetherian module. Assume that for every
index `n` and every prime `p` containing `I` the image of `ker (β n)` in some later term is
unsupported at `p`. Then there is an index `a` such that for every `m ≥ a` and all `n ≫ m` the
images of `G m → G n` and `G a → G n` coincide. -/
theorem exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus (G : ℕ ⥤ ModuleCat.{v} A)
    (hG : ∀ n : ℕ, IsNoetherian A (G.obj n)) (I : Ideal A)
    (hann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (G.obj n)) = ⊥)
    {L : Type w} [AddCommGroup L] [Module A L] [IsNoetherian A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    (hzero : ∀ (n : ℕ) (p : PrimeSpectrum A), I ≤ p.asIdeal →
      ∃ (m : ℕ) (h : n ≤ m), p ∉ Module.support A
        (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
          (LinearMap.ker (β n)).subtype) : Type v)) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range (G.map (homOfLE hmn)).hom =
        LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom := by
  refine exists_range_transitionMap_eq_of_forall_prime G hG β hβ fun n p => ?_
  by_cases hI : I ≤ p.asIdeal
  · exact hzero n p hI
  · exact ⟨n, le_refl n,
      notMem_support_range_comp_ker_of_notMem_zeroLocus G hann β (le_refl n) hI⟩

/-- Let `G` be a direct system of Noetherian modules over a commutative ring, each annihilated by a
power of `I`, and let `β n : G n → L` be a compatible family of maps into a Noetherian module.
Assume that for every index `n` and every prime `p` containing `I` some later `β m` has kernel
unsupported at `p`, that is, becomes injective over `A_p`. Then there is an index `a` such that for
every `m ≥ a` and all `n ≫ m` the images of `G m → G n` and `G a → G n` coincide. -/
theorem exists_range_transitionMap_eq_of_notMem_support_ker (G : ℕ ⥤ ModuleCat.{v} A)
    (hG : ∀ n : ℕ, IsNoetherian A (G.obj n)) (I : Ideal A)
    (hann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (G.obj n)) = ⊥)
    {L : Type w} [AddCommGroup L] [Module A L] [IsNoetherian A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    (hker : ∀ (n : ℕ) (p : PrimeSpectrum A), I ≤ p.asIdeal →
      ∃ (m : ℕ) (_ : n ≤ m), p ∉ Module.support A (LinearMap.ker (β m) : Type v)) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range (G.map (homOfLE hmn)).hom =
        LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom :=
  exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus G hG I hann β hβ
    fun n p hp =>
      exists_notMem_support_range_comp_ker_of_exists_notMem_support_ker G β hβ n (hker n p hp)

end Stacks

end
