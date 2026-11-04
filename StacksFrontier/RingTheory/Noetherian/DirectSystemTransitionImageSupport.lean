module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Support

/-!
# The transition images of a submodule of a direct system

Let `G` be a direct system of modules over a commutative ring `A`, indexed by `ℕ`, let `n : ℕ`
and let `P` be a submodule of `G n`. The image of `P` in a later term `G j` is the quotient of
`P` by the kernel of the composite `P → G n → G j`, and those kernels increase with `j`. If `P`
is Noetherian they stabilise, and past the index where they do all the images of `P` are the
same module. So a prime at which *one* transition image of `P` vanishes lies outside the support
of *every* sufficiently late one, with the index at which "sufficiently late" begins depending
only on `P`.

That exchanges the quantifiers in a vanishing statement proved prime by prime: a hypothesis
`∀ p, ∃ m` becomes a conclusion `∃ c, ∀ p`, with no quasi-compactness and no finiteness beyond
Noetherianness of `P`. If every prime of `A` is such a prime the late transition images have
empty support, hence vanish.

## Main results

* `Stacks.exists_notMem_support_transitionImage` — one index past which no transition image of
  `P` is supported at a prime at which some transition image of `P` vanishes.
* `Stacks.exists_subsingleton_transitionImage` — if every prime of `A` is such a prime, the
  transition images of `P` eventually vanish.

## Implementation notes

The receiving module of the system plays no part: what is stabilised is a chain of submodules
of `P`, so Noetherianness of `P` is the only hypothesis, and the terms `G j` for `j > n` are not
assumed finite. Where this is applied `P` is the kernel of a map `β n : G n → L` of a cocone on
`G`, and `L` carries the separate argument that the images of `β` stabilise; neither that
argument nor the compatibility of `β` with the transition maps is needed here.

`Stacks.exists_subsingleton_transitionImage` is the form the route of [Stacks, Tag 0EHK] needs
over a chart of the punctured spectrum, where the hypothesis holds at *every* prime of the chart
ring. Over the base ring itself it holds only away from the closed point, and the corresponding
conclusion is finite length rather than vanishing; that is
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_of_support`, which consumes
`Stacks.exists_notMem_support_transitionImage` directly.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Stacks

section Ring

variable {A : Type u} [Ring A]

/-- The transition maps of a direct system indexed by the natural numbers compose. -/
theorem directSystem_map_comp_apply (G : ℕ ⥤ ModuleCat.{v} A) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c) (x : G.obj a) :
    (G.map (homOfLE hbc)).hom ((G.map (homOfLE hab)).hom x) =
      (G.map (homOfLE hac)).hom x := by
  have h := G.map_comp (homOfLE hab) (homOfLE hbc)
  have hcomp : homOfLE hab ≫ homOfLE hbc = homOfLE hac := Subsingleton.elim _ _
  rw [hcomp] at h
  exact (congrArg (fun g => ModuleCat.Hom.hom g x) h).symm

/-- The kernels of the composites `P → G a → G j`, for `P` a submodule of `G a`, increase with
`j`. -/
theorem ker_comp_subtype_mono (G : ℕ ⥤ ModuleCat.{v} A) {a : ℕ}
    (P : Submodule A (G.obj a)) {j j' : ℕ} (hj : a ≤ j) (hj' : a ≤ j') (hjj' : j ≤ j') :
    LinearMap.ker ((G.map (homOfLE hj)).hom ∘ₗ P.subtype) ≤
      LinearMap.ker ((G.map (homOfLE hj')).hom ∘ₗ P.subtype) := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
  rw [← directSystem_map_comp_apply G hj hjj' hj', hx, map_zero]

end Ring

section CommRing

variable {A : Type u} [CommRing A]

/-- Dividing by a larger submodule produces a quotient of the quotient, so the support
shrinks. -/
theorem support_quotient_subset {X : Type v} [AddCommGroup X] [Module A X]
    {P Q : Submodule A X} (h : P ≤ Q) :
    Module.support A (X ⧸ Q) ⊆ Module.support A (X ⧸ P) :=
  Module.support_subset_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

/-- **One index serves every prime at once.** Let `P` be a Noetherian submodule of the term
`G n` of a direct system of `A`-modules. There is an index `c` such that for every `j ≥ c` and
every prime `p` of `A`, if the image of `P` in *some* term `G m` with `m ≥ n` is not supported
at `p`, then the image of `P` in `G j` is not supported at `p` either.

The images of `P` are the quotients of `P` by the kernels of the composites `P → G n → G j`,
which increase with `j`, so by Noetherianness of `P` they are constant from some index `n + c₀`
on; `c` is that index. The image in `G j` for `j ≥ n + c₀` is then a quotient of the image in
`G (n + c₀)`, which has the same kernel as — hence is isomorphic to — the image in
`G (n + (c₀ + m))`, itself a quotient of the image in `G m`. Supports only shrink along
surjections, so `p` is in none of them. -/
theorem exists_notMem_support_transitionImage (G : ℕ ⥤ ModuleCat.{v} A) {n : ℕ}
    (P : Submodule A (G.obj n)) (hP : IsNoetherian A P) :
    ∃ c : ℕ, ∀ (j : ℕ) (h : n ≤ j), c ≤ j → ∀ p : PrimeSpectrum A,
      (∃ (m : ℕ) (hm : n ≤ m), p ∉ Module.support A
        (LinearMap.range ((G.map (homOfLE hm)).hom ∘ₗ P.subtype))) →
      p ∉ Module.support A
        (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ P.subtype)) := by
  have heq : ∀ (j : ℕ) (hj : n ≤ j),
      (P ⧸ LinearMap.ker ((G.map (homOfLE hj)).hom ∘ₗ P.subtype)) ≃ₗ[A]
        LinearMap.range ((G.map (homOfLE hj)).hom ∘ₗ P.subtype) :=
    fun _ _ => LinearMap.quotKerEquivRange _
  obtain ⟨c₀, hc₀⟩ := monotone_stabilizes_iff_noetherian.mpr hP
    ⟨fun c => LinearMap.ker ((G.map (homOfLE (Nat.le_add_right n c))).hom ∘ₗ P.subtype),
      fun _ _ h => ker_comp_subtype_mono G P (Nat.le_add_right n _)
        (Nat.le_add_right n _) (Nat.add_le_add_left h n)⟩
  refine ⟨n + c₀, fun j hj hcj p hp hmem => ?_⟩
  obtain ⟨m, hm, hpm⟩ := hp
  have hker : LinearMap.ker ((G.map (homOfLE (Nat.le_add_right n c₀))).hom ∘ₗ P.subtype) =
      LinearMap.ker ((G.map (homOfLE (Nat.le_add_right n (c₀ + m)))).hom ∘ₗ P.subtype) :=
    hc₀ (c₀ + m) (by omega)
  rw [← (heq j hj).support_eq] at hmem
  rw [← (heq m hm).support_eq] at hpm
  refine hpm (support_quotient_subset (ker_comp_subtype_mono G P hm
    (Nat.le_add_right n (c₀ + m)) (by omega)) ?_)
  rw [← hker]
  exact support_quotient_subset (ker_comp_subtype_mono G P (Nat.le_add_right n c₀) hj hcj) hmem

/-- **The transition images of a submodule eventually vanish, when at every prime one of them
does.** Let `P` be a Noetherian submodule of the term `G n` of a direct system of `A`-modules,
and suppose that for every prime `p` of `A` the image of `P` in some later term is not supported
at `p`. Then the image of `P` in `G j` vanishes for all large `j`.

This is `Stacks.exists_notMem_support_transitionImage` with the hypothesis available at every
prime: the late images then have empty support, and a module with empty support is zero. No
finiteness is needed for that last step, `Module.support_eq_empty_iff` holding for every
module. -/
theorem exists_subsingleton_transitionImage (G : ℕ ⥤ ModuleCat.{v} A) {n : ℕ}
    (P : Submodule A (G.obj n)) (hP : IsNoetherian A P)
    (hzero : ∀ p : PrimeSpectrum A, ∃ (m : ℕ) (hm : n ≤ m), p ∉ Module.support A
      (LinearMap.range ((G.map (homOfLE hm)).hom ∘ₗ P.subtype))) :
    ∃ c : ℕ, ∀ (j : ℕ) (h : n ≤ j), c ≤ j →
      Subsingleton (LinearMap.range ((G.map (homOfLE h)).hom ∘ₗ P.subtype) : Type v) := by
  obtain ⟨c, hc⟩ := exists_notMem_support_transitionImage G P hP
  exact ⟨c, fun j h hcj => Module.support_eq_empty_iff.mp
    (Set.eq_empty_iff_forall_notMem.mpr fun p => hc j h hcj p (hzero p))⟩

end CommRing

end Stacks

end
