module

public import StacksFrontier.RingTheory.Noetherian.DirectSystemTransitionImagePrimeKernel

/-!
# The hypothesis `hzero` may be checked at any submodule containing the kernel

The hypothesis `hzero` of `Stacks.exists_range_transitionMap_eq_of_forall_prime` is about the
submodule `ker (β n)` of `G n`, for the one compatible family `β` whose images supply the index
`a`. A per-point argument, however, does not in general produce the vanishing for *that*
submodule: it produces it for the kernel of whatever map the local argument has, and the two are
only related by an inclusion.

This file states the hypothesis for an arbitrary submodule `K n ⊇ ker (β n)` of `G n`. Nothing
is lost: the proof of `Stacks.exists_range_transitionMap_eq_of_forall_prime` uses `hzero` only
through `Stacks.exists_subsingleton_transitionImage`, which takes an arbitrary submodule, and the
larger submodule's vanishing implies the smaller one's.

## Main results

* `Stacks.notMem_support_range_comp_subtype_of_le` — the monotonicity: the vanishing at a
  submodule implies it at every smaller submodule.
* `Stacks.exists_range_transitionMap_eq_of_forall_prime_of_ker_le` — the stabilisation of
  transition images with `hzero` read at `K n`.
* `Stacks.exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus_of_ker_le` — the same with
  the hypothesis restricted to the primes of `V(I)`.
* `Stacks.exists_range_transitionMap_eq_of_cocone_ker_le` — the case the route of
  [Stacks, Tag 0EHK] wants: `K n = ker (γ n)` for a *second* compatible family `γ`, so that the
  family supplying the index and the family supplying the vanishing need not be the same one.

## Implementation notes

**Why the route needs this.** Over the completed chart ring `B = (A_f)^∧_I` the family that
supplies the index `a` is `Stacks.Algebraization.dualizingExtSystemToLimit`, because its target
`Stacks.Algebraization.dualizingExtLimit` is the only finite `B`-module receiving the whole
system. The family that supplies the vanishing is a different one: at a prime `𝔮 ⊃ IB` the
vanishing comes from a pro-witness on the local cohomology side through
`Stacks.Algebraization.exists_notMem_support_range_comp_ker_matlisEvaluation`, whose family is
`matlisEvaluationSystem` followed by a coprojection of
`Stacks.Algebraization.matlisBidualCocone`, and whose vertex is the Matlis dual of the
pro-object's own value. Identifying the two families is the value identification of
[Stacks, Tag 0EFR] with local duality, and what the stabilisation actually needs of it is only
the inclusion of kernels `ker (β n) ≤ ker (γ n)` — which is what the last result below asks for.

`Stacks.range_comp_ker_subtype_eq_bot_iff` is the same inclusion read as a vanishing, and is the
form in which a descent along a flat extension delivers it.

**The monotonicity is in the submodule argument and not in the index.**
`Stacks.ker_comp_subtype_mono` is monotone in the index `j` of the transition map, which is a
different statement; nothing in the library was monotone in the submodule.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks

variable {A : Type u} [CommRing A]

/-- **The vanishing hypothesis is monotone in the submodule.** If `K ≤ K'` are submodules of `X`
and the image of `K'` under `f` is unsupported at `p`, then so is the image of `K`.

The containment of the two images is immediate — an element of `K` is an element of `K'` — and
the support of a submodule is contained in the support of the module containing it. -/
theorem notMem_support_range_comp_subtype_of_le {X Y : Type v} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : X →ₗ[A] Y) {K K' : Submodule A X} (hle : K ≤ K')
    {p : PrimeSpectrum A}
    (hp : p ∉ Module.support A (LinearMap.range (f ∘ₗ K'.subtype) : Type v)) :
    p ∉ Module.support A (LinearMap.range (f ∘ₗ K.subtype) : Type v) := by
  have hrange : LinearMap.range (f ∘ₗ K.subtype) ≤ LinearMap.range (f ∘ₗ K'.subtype) := by
    rintro - ⟨x, rfl⟩
    exact ⟨⟨x.1, hle x.2⟩, rfl⟩
  exact fun hmem => hp (Module.support_subset_of_injective (Submodule.inclusion hrange)
    (Submodule.inclusion_injective _) hmem)

/-- **The transition images are eventually equal, with `hzero` checked at submodules containing
the kernels.** `Stacks.exists_range_transitionMap_eq_of_forall_prime` with its hypothesis read at
an arbitrary family of submodules `K n` of `G n` containing `ker (β n)`.

The family `β` still has to be compatible with the transition maps and land in a Noetherian
module — that is what produces the index `a` — but the vanishing may be supplied for a larger
submodule, which is what a per-point argument with a different map produces. -/
theorem exists_range_transitionMap_eq_of_forall_prime_of_ker_le (G : ℕ ⥤ ModuleCat.{v} A)
    (hG : ∀ n : ℕ, IsNoetherian A (G.obj n))
    {L : Type w} [AddCommGroup L] [Module A L] [IsNoetherian A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    (K : ∀ n : ℕ, Submodule A (G.obj n)) (hK : ∀ n : ℕ, LinearMap.ker (β n) ≤ K n)
    (hzero : ∀ (n : ℕ) (p : PrimeSpectrum A), ∃ (m : ℕ) (h : n ≤ m),
      p ∉ Module.support A (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
        (K n).subtype) : Type v)) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range (G.map (homOfLE hmn)).hom =
        LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom := by
  refine exists_range_transitionMap_eq_of_forall_prime G hG β hβ fun n p => ?_
  obtain ⟨m, h, hm⟩ := hzero n p
  exact ⟨m, h, notMem_support_range_comp_subtype_of_le _ (hK n) hm⟩

/-- **The same, with the vanishing asked only at the primes of `V(I)`.**
`Stacks.exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus` with its hypothesis read at
submodules containing the kernels. The primes outside `V(I)` impose no condition, the terms of
the system being annihilated by powers of `I`. -/
theorem exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus_of_ker_le
    (G : ℕ ⥤ ModuleCat.{v} A) (hG : ∀ n : ℕ, IsNoetherian A (G.obj n)) (I : Ideal A)
    (hann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (G.obj n)) = ⊥)
    {L : Type w} [AddCommGroup L] [Module A L] [IsNoetherian A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    (K : ∀ n : ℕ, Submodule A (G.obj n)) (hK : ∀ n : ℕ, LinearMap.ker (β n) ≤ K n)
    (hzero : ∀ (n : ℕ) (p : PrimeSpectrum A), I ≤ p.asIdeal →
      ∃ (m : ℕ) (h : n ≤ m), p ∉ Module.support A
        (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ (K n).subtype) : Type v)) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range (G.map (homOfLE hmn)).hom =
        LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom := by
  refine exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus G hG I hann β hβ
    fun n p hp => ?_
  obtain ⟨m, h, hm⟩ := hzero n p hp
  exact ⟨m, h, notMem_support_range_comp_subtype_of_le _ (hK n) hm⟩

/-- **The transition images are eventually equal when the index and the vanishing come from two
different compatible families.** Let `β` be a compatible family into a Noetherian module — this
is what makes the images of `β` stabilise — and let `γ` be a second family whose kernels contain
those of `β` and for which the vanishing holds at every prime of `V(I)`. Then the transition
images of `G` are eventually equal.

**This is the shape the route of [Stacks, Tag 0EHK] delivers.** Over the completed chart ring the
family supplying the index is `Stacks.Algebraization.dualizingExtSystemToLimit`, whose target is
the only finite module receiving the system; the family supplying the vanishing at a prime
`𝔮 ⊃ IB` is the Matlis bidual coprojection of
`Stacks.Algebraization.exists_notMem_support_range_comp_ker_matlisEvaluation`, whose vertex is
the Matlis dual of the value of the pro-object. What the source's value identification is needed
for is exactly the hypothesis `hker` below, and **not** an isomorphism of the two families: an
inclusion of kernels in one direction suffices.

`γ` is not asked to be compatible with the transition maps, nor to land in a Noetherian module;
only its kernels are used. -/
theorem exists_range_transitionMap_eq_of_cocone_ker_le (G : ℕ ⥤ ModuleCat.{v} A)
    (hG : ∀ n : ℕ, IsNoetherian A (G.obj n)) (I : Ideal A)
    (hann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (G.obj n)) = ⊥)
    {L : Type w} [AddCommGroup L] [Module A L] [IsNoetherian A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    {L' : Type w} [AddCommGroup L'] [Module A L'] (γ : ∀ n : ℕ, G.obj n →ₗ[A] L')
    (hker : ∀ n : ℕ, LinearMap.ker (β n) ≤ LinearMap.ker (γ n))
    (hzero : ∀ (n : ℕ) (p : PrimeSpectrum A), I ≤ p.asIdeal →
      ∃ (m : ℕ) (h : n ≤ m), p ∉ Module.support A
        (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
          (LinearMap.ker (γ n)).subtype) : Type v)) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range (G.map (homOfLE hmn)).hom =
        LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom :=
  exists_range_transitionMap_eq_of_forall_prime_mem_zeroLocus_of_ker_le G hG I hann β hβ
    (fun n => LinearMap.ker (γ n)) hker hzero

end Stacks

end
