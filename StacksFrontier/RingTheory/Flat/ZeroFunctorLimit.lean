module

public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of a base-changed module map descends to a finitely generated subalgebra

Let `A` be a commutative ring, `B` an `A`-algebra, and `u : M ⟶ N` a homomorphism of
`B`-modules whose source is a finite `B`-module. For an `A`-algebra `T` write `u_T` for the
base change `T ⊗_A M ⟶ T ⊗_A N` of `u`.

The condition `u_T = 0` is *limit preserving* in `T`: if `u_T = 0` then already `u_C = 0` for a
finitely generated `A`-subalgebra `C ⊆ T`, and consequently, for every directed family of
`A`-subalgebras whose union is `T`, the base change of `u` to one of its members is zero.

## Main results

* `Stacks.Flattening.lTensor_eq_zero_iff`: the base change `u_T` vanishes exactly when it
  kills the elements `1 ⊗ u m`.
* `Stacks.Flattening.lTensor_eq_zero_iff_of_span`: a generating set of `M` over `B` suffices.
* `Stacks.Flattening.exists_adjoin_lTensor_eq_zero`: vanishing of `u_T` descends to a finitely
  generated `A`-subalgebra of `T`.
* `Stacks.Flattening.exists_lTensor_eq_zero_of_directed`: hence to a member of any directed
  family of `A`-subalgebras exhausting `T`.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flattening

variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

section Unit

variable (T : Type*) [CommRing T] [Algebra A T]

/-- The `B`-submodule of `N` consisting of the elements `n` with `1 ⊗ n = 0` in `T ⊗_A N`. -/
def unitTensorKernel : Submodule B N where
  carrier := {n : N | (1 : T) ⊗ₜ[A] n = 0}
  zero_mem' := TensorProduct.tmul_zero _ _
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [TensorProduct.tmul_add, ha, hb, add_zero]
  smul_mem' b n hn := by
    simp only [Set.mem_ofPred_eq] at hn ⊢
    simpa using congrArg (LinearMap.lTensor T ((LinearMap.lsmul B N b).restrictScalars A)) hn

/-- Membership in `Stacks.Flattening.unitTensorKernel` is the vanishing of `1 ⊗ n`. -/
theorem mem_unitTensorKernel_iff {n : N} :
    n ∈ unitTensorKernel (A := A) (B := B) T ↔ (1 : T) ⊗ₜ[A] n = 0 :=
  Iff.rfl

/-- The base change of `u : M →ₗ[B] N` along an `A`-algebra `T` vanishes exactly when it kills
every element of the form `1 ⊗ m`. -/
theorem lTensor_eq_zero_iff (u : M →ₗ[B] N) :
    LinearMap.lTensor T (u.restrictScalars A) = 0 ↔ ∀ m : M, (1 : T) ⊗ₜ[A] u m = 0 := by
  refine ⟨fun h m => by simpa using LinearMap.congr_fun h ((1 : T) ⊗ₜ[A] m), fun h => ?_⟩
  refine TensorProduct.ext' fun t m => ?_
  rw [LinearMap.lTensor_tmul, LinearMap.zero_apply, LinearMap.coe_restrictScalars, ← mul_one t,
    ← smul_eq_mul, ← smul_tmul', h m, smul_zero]

/-- Vanishing of the base change of `u : M →ₗ[B] N` need only be tested on a generating set of
`M` over `B`. -/
theorem lTensor_eq_zero_iff_of_span (u : M →ₗ[B] N) {s : Set M}
    (hs : Submodule.span B s = ⊤) :
    LinearMap.lTensor T (u.restrictScalars A) = 0 ↔ ∀ m ∈ s, (1 : T) ⊗ₜ[A] u m = 0 := by
  rw [lTensor_eq_zero_iff]
  refine ⟨fun h m _ => h m, fun h m => ?_⟩
  have hle : Submodule.span B s ≤ (unitTensorKernel T).comap u :=
    Submodule.span_le.2 fun x hx => h x hx
  rw [hs] at hle
  exact hle Submodule.mem_top

end Unit

section Descent

variable {T : Type*} [CommRing T] [Algebra A T]

/-- Vanishing of `1 ⊗ n` over a subalgebra persists in any larger subalgebra. -/
theorem tmul_one_eq_zero_of_le {C D : Subalgebra A T} (hCD : C ≤ D) {n : N}
    (h : (1 : C) ⊗ₜ[A] n = 0) : (1 : D) ⊗ₜ[A] n = 0 := by
  simpa using congrArg (LinearMap.rTensor N (Subalgebra.inclusion hCD).toLinearMap) h

/-- If `1 ⊗ n` vanishes in `T ⊗_A N` then it already vanishes over a finitely generated
`A`-subalgebra of `T`. -/
theorem exists_adjoin_tmul_one_eq_zero {n : N} (hn : (1 : T) ⊗ₜ[A] n = 0) :
    ∃ t : Finset T, (1 : Algebra.adjoin A (t : Set T)) ⊗ₜ[A] n = 0 := by
  classical
  set N₀ : Submodule A T := Submodule.span A {(1 : T)}
  have h1 : (1 : T) ∈ N₀ := Submodule.mem_span_singleton_self _
  have hfg : N₀.FG := Submodule.fg_span_singleton _
  have key : LinearMap.rTensor N N₀.subtype ((⟨1, h1⟩ : N₀) ⊗ₜ[A] n)
      = LinearMap.rTensor N N₀.subtype (0 : N₀ ⊗[A] N) := by
    simpa using hn
  obtain ⟨N', hN'fg, hle, heq⟩ := hfg.exists_rTensor_fg_inclusion_eq key
  obtain ⟨t, ht⟩ := hN'fg
  refine ⟨t, ?_⟩
  have hsub : N' ≤ Subalgebra.toSubmodule (Algebra.adjoin A (t : Set T)) := by
    rw [← ht, Submodule.span_le]
    exact fun x hx => Algebra.subset_adjoin hx
  rw [map_zero, LinearMap.rTensor_tmul] at heq
  have heq' : (⟨1, hle h1⟩ : N') ⊗ₜ[A] n = 0 := heq
  have hpush := congrArg (LinearMap.rTensor N (Submodule.inclusion hsub)) heq'
  rwa [map_zero, LinearMap.rTensor_tmul] at hpush

/-- **The algebraic content of the "zero" clause of Stacks 05MJ.** If the base change of a
homomorphism `u : M →ₗ[B] N` of `B`-modules with `M` a finite `B`-module to an `A`-algebra `T`
is zero, then its base change to a finitely generated `A`-subalgebra of `T` is already zero. -/
theorem exists_adjoin_lTensor_eq_zero (u : M →ₗ[B] N) [Module.Finite B M]
    (h : LinearMap.lTensor T (u.restrictScalars A) = 0) :
    ∃ t : Finset T,
      LinearMap.lTensor (Algebra.adjoin A (t : Set T)) (u.restrictScalars A) = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule B M).FG)
  have hspan : Submodule.span B (s : Set M) = ⊤ := hs
  have hzero : ∀ m ∈ s, (1 : T) ⊗ₜ[A] u m = 0 :=
    (lTensor_eq_zero_iff_of_span T u hspan).1 h
  choose gen hgen using fun m (hm : m ∈ s) => exists_adjoin_tmul_one_eq_zero (hzero m hm)
  refine ⟨s.attach.biUnion fun m => gen m.1 m.2, ?_⟩
  refine (lTensor_eq_zero_iff_of_span _ u hspan).2 fun m hm => ?_
  refine tmul_one_eq_zero_of_le ?_ (hgen m hm)
  refine Algebra.adjoin_mono fun x hx => ?_
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨m, hm⟩, Finset.mem_attach _ _, hx⟩)

/-- **The "zero" clause of Stacks 05MJ in directed-union form.** Let `(C i)` be a monotone
family of `A`-subalgebras of `T`, indexed by a nonempty directed preorder, whose union is all
of `T`. If the base change of `u : M →ₗ[B] N` to `T` is zero and `M` is a finite `B`-module,
then its base change to some `C i` is already zero. -/
theorem exists_lTensor_eq_zero_of_directed {ι : Type*} [Nonempty ι] [Preorder ι]
    [IsDirectedOrder ι] (C : ι → Subalgebra A T) (hmono : Monotone C)
    (hex : ∀ x : T, ∃ i, x ∈ C i) (u : M →ₗ[B] N) [Module.Finite B M]
    (h : LinearMap.lTensor T (u.restrictScalars A) = 0) :
    ∃ i, LinearMap.lTensor (C i) (u.restrictScalars A) = 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_adjoin_lTensor_eq_zero u h
  choose idx hidx using hex
  obtain ⟨i, hi⟩ := Finset.exists_le (t.image idx)
  refine ⟨i, ?_⟩
  have hsub : Algebra.adjoin A (t : Set T) ≤ C i := by
    refine Algebra.adjoin_le fun x hx => ?_
    exact hmono (hi (idx x) (Finset.mem_image_of_mem idx hx)) (hidx x)
  refine (lTensor_eq_zero_iff (C i) u).2 fun m => ?_
  exact tmul_one_eq_zero_of_le hsub ((lTensor_eq_zero_iff _ u).1 ht m)

end Descent

end Stacks.Flattening

end
