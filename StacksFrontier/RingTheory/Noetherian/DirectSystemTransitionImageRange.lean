module

public import StacksFrontier.RingTheory.Noetherian.DirectSystemRangeStabilization
public import StacksFrontier.RingTheory.Noetherian.DirectSystemTransitionImageSupport

/-!
# The transition images of a direct system stop growing, on the nose

Let `G` be a direct system of modules over a commutative ring `A`, indexed by `ℕ`, and let
`β n : G n → L` be a compatible family of maps into one Noetherian `A`-module. Past the index `a`
at which the images of the `β n` stop growing, the image of `G m` in a later term `G n` differs
from the image of `G a` only by the image of `ker (β m)`: an element of `G m` may be corrected,
modulo that kernel, by an element coming from `G a`. So if the image of `ker (β m)` in `G n`
vanishes then the images of `G m → G n` and `G a → G n` *coincide*.

That vanishing is a statement about one submodule of one term, so
`Stacks.exists_subsingleton_transitionImage` supplies it from a hypothesis checked prime by
prime, with the index exchanged for a uniform one. The conclusion is therefore an equality of
transition images obtained from a purely local hypothesis — which is what the route of
[Stacks, Tag 0EHK] needs over a chart of the punctured spectrum, where the hypothesis holds at
*every* prime of the chart ring and the ring is not local.

## Main results

* `Stacks.range_mkQ_comp_map_eq_range_comp_ker` — the correction step: past the index at which
  the images of `β` stabilise, the image of `G m` in `G n ⧸ im(G a → G n)` is the image of
  `ker (β m)` there.
* `Stacks.exists_range_transitionMap_eq_of_forall_prime` — the globalisation: from the
  per-prime vanishing, one index past which the transition images are equal.

## Implementation notes

`Stacks.range_mkQ_comp_map_eq_range_comp_ker` is the `hsub` step of the proof of
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_support`, which is stated here
and consumed there rather than carried out twice. It needs no finiteness and no commutativity:
the hypothesis is the equality `im(β a) = im(β m)` of two submodules of `L`, which
`Stacks.exists_range_stabilizes` provides for `m ≥ a`.

`Stacks.exists_range_transitionMap_eq_of_forall_prime` asks for the per-prime vanishing at
*every* prime, and in return concludes an equality of images rather than finite length of their
quotient. Over a local ring the hypothesis is only available away from the closed point and the
conclusion is accordingly weaker; that is
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_support`, and the two are not
comparable — neither hypothesis implies the other.

The receiving module `L` is Noetherian rather than finite, and its universe is free of the
system's, for the reason recorded in the implementation notes of
`StacksFrontier.RingTheory.Noetherian.DirectSystemRangeStabilization`: on the route of
[Stacks, Tag 0EHK] the vertex of the cocone is a module over a larger ring.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks

/-- **Past the index at which the images of `β` stabilise, the image of `G m` in
`G n ⧸ im(G a → G n)` is the image of `ker (β m)`.** Let `β n : G n → L` be compatible with the
transition maps of a direct system `G`, let `a ≤ m ≤ n`, and suppose `im(β a) = im(β m)`. Then
the image of the composite `G m → G n → G n ⧸ im(G a → G n)` is the image of its restriction to
`ker (β m)`.

*Argument.* One containment is restriction. For the other, given `x : G m`, the equality of
images gives `y : G a` with `β a y = β m x`; compatibility of `β` turns this into
`β m (y|_m) = β m x`, so `x - y|_m` lies in `ker (β m)`, and `y|_m` dies in
`G n ⧸ im(G a → G n)` because `a ⟶ m ⟶ n` is `a ⟶ n`. -/
theorem range_mkQ_comp_map_eq_range_comp_ker {R : Type u} [Ring R] (G : ℕ ⥤ ModuleCat.{v} R)
    {L : Type w} [AddCommGroup L] [Module R L] (β : ∀ n : ℕ, G.obj n →ₗ[R] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    {a m n : ℕ} (hm : a ≤ m) (hmn : m ≤ n)
    (hrange : LinearMap.range (β a) = LinearMap.range (β m)) :
    LinearMap.range ((LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ ∘ₗ
        (G.map (homOfLE hmn)).hom) =
      LinearMap.range (((LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ ∘ₗ
        (G.map (homOfLE hmn)).hom) ∘ₗ (LinearMap.ker (β m)).subtype) := by
  refine le_antisymm ?_ (LinearMap.range_comp_le_range _ _)
  rintro - ⟨x, rfl⟩
  obtain ⟨y, hy⟩ : β m x ∈ LinearMap.range (β a) := by
    rw [hrange]
    exact ⟨x, rfl⟩
  have hβy : β m ((G.map (homOfLE hm)).hom y) = β a y := by
    rw [← hβ a m hm, LinearMap.comp_apply]
  have hz : x - (G.map (homOfLE hm)).hom y ∈ LinearMap.ker (β m) := by
    rw [LinearMap.mem_ker, map_sub, hβy, hy, sub_self]
  have hq : (LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ
      ((G.map (homOfLE hmn)).hom ((G.map (homOfLE hm)).hom y)) = 0 := by
    rw [directSystem_map_comp_apply G hm hmn (hm.trans hmn)]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  refine ⟨⟨x - (G.map (homOfLE hm)).hom y, hz⟩, ?_⟩
  have hval : ((LinearMap.ker (β m)).subtype ⟨x - (G.map (homOfLE hm)).hom y, hz⟩) =
      x - (G.map (homOfLE hm)).hom y := rfl
  simp only [LinearMap.comp_apply, hval, map_sub, hq, sub_zero]

/-- **The transition images of a direct system are eventually equal, from a vanishing checked
prime by prime.** Let `G` be a direct system of Noetherian modules over a commutative ring `A`,
and let `β n : G n → L` be a compatible family of maps into a Noetherian `A`-module. Assume that
for every index `n` and every prime `p` of `A` the kernel of `β n` has vanishing image in some
later term of the system after localising at `p`. Then there is an index `a` such that for every
`m ≥ a` and all `n ≫ m` the images of `G m → G n` and of `G a → G n` coincide.

*Argument.* `Stacks.exists_range_stabilizes` gives the index `a` past which the images of `β` do
not grow. Fix `m ≥ a`. By `Stacks.range_mkQ_comp_map_eq_range_comp_ker` the image of `G m` in
`G n ⧸ im(G a → G n)` is the image of `ker (β m)` there, and by
`Stacks.exists_subsingleton_transitionImage` — which exchanges the per-prime index for one index
serving every prime — the image of `ker (β m)` in `G n` is already zero for `n ≫ m`. So
`im(G m → G n) ≤ im(G a → G n)`; the reverse containment is free, `G a → G n` factoring through
`G m → G n` because `a ≤ m ≤ n`.

No local hypothesis on `A` appears, and the hypothesis is asked at every prime: this is the
statement available over a chart of the punctured spectrum, where the `A`-module `L` receiving
the system exists and the vanishing holds everywhere. The ring being local is what makes the
hypothesis unavailable at the closed point, and then only finite length can be concluded —
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_support`. -/
theorem exists_range_transitionMap_eq_of_forall_prime {A : Type u} [CommRing A]
    (G : ℕ ⥤ ModuleCat.{v} A) (hG : ∀ n : ℕ, IsNoetherian A (G.obj n))
    {L : Type w} [AddCommGroup L] [Module A L] [IsNoetherian A L]
    (β : ∀ n : ℕ, G.obj n →ₗ[A] L)
    (hβ : ∀ (m n : ℕ) (h : m ≤ n), β n ∘ₗ (G.map (homOfLE h)).hom = β m)
    (hzero : ∀ (n : ℕ) (p : PrimeSpectrum A), ∃ (m : ℕ) (h : n ≤ m),
      p ∉ Module.support A (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ
        (LinearMap.ker (β n)).subtype))) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range (G.map (homOfLE hmn)).hom =
        LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom := by
  obtain ⟨a, ha⟩ := exists_range_stabilizes G β hβ
  refine ⟨a, fun m hm => ?_⟩
  have := hG m
  obtain ⟨c, hc⟩ := exists_subsingleton_transitionImage G (LinearMap.ker (β m)) inferInstance
    (hzero m)
  refine ⟨c, fun n hmn hcn => le_antisymm ?_ ?_⟩
  swap
  · -- the earlier image is reached from `G m`, since `G a → G n` factors through it
    rintro - ⟨x, rfl⟩
    exact ⟨(G.map (homOfLE hm)).hom x, directSystem_map_comp_apply G hm hmn (hm.trans hmn) x⟩
  -- the image of `ker (β m)` in `G n` has vanished by the index `c`
  have := hc n hmn hcn
  have hvanish : ((LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ ∘ₗ
      (G.map (homOfLE hmn)).hom) ∘ₗ (LinearMap.ker (β m)).subtype = 0 := by
    refine LinearMap.ext fun y => ?_
    have hmem : (G.map (homOfLE hmn)).hom ((LinearMap.ker (β m)).subtype y) ∈
        LinearMap.range ((G.map (homOfLE hmn)).hom ∘ₗ (LinearMap.ker (β m)).subtype) := ⟨y, rfl⟩
    have h0 : (G.map (homOfLE hmn)).hom ((LinearMap.ker (β m)).subtype y) = 0 := by
      simpa using congrArg Subtype.val (Subsingleton.elim
        (⟨_, hmem⟩ : LinearMap.range ((G.map (homOfLE hmn)).hom ∘ₗ
          (LinearMap.ker (β m)).subtype)) 0)
    simp only [LinearMap.comp_apply, h0, map_zero, LinearMap.zero_apply]
  intro w hw
  obtain ⟨x, rfl⟩ := hw
  have hmem : ((LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ ∘ₗ
      (G.map (homOfLE hmn)).hom) x ∈
      LinearMap.range ((LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ ∘ₗ
        (G.map (homOfLE hmn)).hom) := ⟨x, rfl⟩
  rw [range_mkQ_comp_map_eq_range_comp_ker G β hβ hm hmn (ha m hm), hvanish,
    LinearMap.range_zero] at hmem
  have hzeroq : (LinearMap.range (G.map (homOfLE (hm.trans hmn))).hom).mkQ
      ((G.map (homOfLE hmn)).hom x) = 0 := (Submodule.mem_bot A).mp hmem
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzeroq
  exact hzeroq

end Stacks

end
