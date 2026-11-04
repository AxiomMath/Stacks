module

public import Mathlib.RingTheory.AdicCompletion.Completeness
import StacksFrontier.RingTheory.GradedAlgebra.Nakayama
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Limits of inverse systems of modules

Let `A` be a commutative ring and `I ⊆ A` an ideal.  This file computes the `I`-adic behaviour of
the limit `M = lim_n Mₙ` of an inverse system of `A`-modules `(Mₙ, t n : M (n + 1) → Mₙ)` in the
situations where the system already remembers its own `I`-adic filtration.

If `I` is finitely generated and each `t n` is surjective with kernel `Iⁿ M (n + 1)`, so that
`Mₙ = M (n + 1) / Iⁿ M (n + 1)`, then the limit projections `M → Mₙ` are surjective with kernel
`Iⁿ M`, so that `M / Iⁿ M ≅ Mₙ`, and `M` is `I`-adically complete [StacksProject 09B8].  For
completeness alone the weaker hypothesis `Iⁿ Mₙ = 0` suffices [StacksProject 0G1Q]: the
projections then factor through `M / Iⁿ M` and assemble into a retraction of `M → M^∧`, which
exhibits `M` as a direct summand of the complete module `M^∧`.

The graded analogue [StacksProject 0EKC] needs no finiteness assumption on `I`.  For a graded ring
`A = ⨁_{i ≥ 0} 𝒜 i`, a homogeneous ideal `I ⊆ 𝒜₊ = ⨁_{i > 0} 𝒜 i` and an inverse system `(Nₙ)` of
*finite graded* `A`-modules whose graded transition maps exhibit `Nₙ = N (n+1) / Iⁿ N (n+1)`,
there is a single finite graded `A`-module `M` and graded surjections `f n : M → Nₙ`, compatible
with the transition maps, with `ker (f n) = Iⁿ M`; that is, `Nₙ = M / Iⁿ M` as graded modules, as
an isomorphism of inverse systems.  What replaces finite generation of `I` is that the degrees of
a finite set of homogeneous generators bound how far down `M / Iⁿ M` can differ from `M`: as `I`
is generated in positive degrees, `Iᵐ Nₙ` vanishes in degrees `< δ + m` for `δ` the least degree
of a generator, so `Nₙ → Nₘ` is an isomorphism in degrees `< δ + m` and the inverse system of
degree-`d` parts stabilises.  Here `M` is the module of compatible sequences that are homogeneous
of one and the same degree at every level.

## Main definitions

* `Stacks.AdicCompletion.InverseLimit.InverseSystem`: a bundled inverse system with `Mₙ = M (n + 1)
  / Iⁿ M (n + 1)`.
* `invLimit`: the limit of an inverse system of `A`-modules, realised as the submodule of the
  compatible families in the product.
* `Stacks.AdicCompletion.InverseLimit.InverseSystem.limit`: the limit of a bundled inverse system.

## Main results

* `invLimit.proj_surjective`: Mittag-Leffler — the projections from the limit of a tower of
  surjections are surjective.
* `Stacks.AdicCompletion.InverseLimit.InverseSystem.quotientEquiv`: `M / Iⁿ M ≅ Mₙ`.
* `Stacks.AdicCompletion.InverseLimit.InverseSystem.isAdicComplete`: the limit is `I`-adically
  complete.
* `invLimit_isAdicComplete`: the limit of a system with `Iⁿ Mₙ = 0` is `I`-adically complete.
* `Ideal.IsHomogeneous.exists_finite_graded_forall_ker_eq_pow_smul_top`: an inverse system of
  finite graded modules with `Nₙ = N (n+1) / Iⁿ N (n+1)` is the system of `Iⁿ`-quotients of a
  single finite graded module.

## Implementation notes

`Iⁿ N` is written `I ^ n • (⊤ : Submodule A N)`; `I`-adic completeness is Mathlib's
`IsAdicComplete I N`, which bundles `IsHausdorff` with `IsPrecomplete`, and the completion
`M^∧ = lim_k M / Iᵏ M` is `AdicCompletion I M`.

Surjectivity of the limit projections in the ungraded case is Mittag-Leffler and needs nothing of
`I`: it runs on chosen sections of a tower of surjections, lifting an element to a level above and
pushing it back down, and is applied both to `(Mₙ)` and to the subsystem `(Iᵏ Mₙ)`.  Finite
generation of `I` enters only in the kernel computation, where the error
`x - ∑ⱼ aⱼ • vⱼ` is improved one power of `I` at a time along a finite generating set of `Iⁿ`.

In the graded case the ring is graded by `ℕ` and the modules by `ℤ`, as in the source
[StacksProject 00JL].  Mathlib supplies no degree shift `VAdd ℕ ℤ`, so the graded action
`𝒜 i · N_d ⊆ N_{i + d}` cannot be a `SetLike.GradedSMul 𝒜 𝒩` instance and is carried as a
hypothesis; the shift needed to apply the graded Nakayama lemma
`Submodule.IsHomogeneous.le_of_le_smul_of_le_irrelevant`, which is stated for an arbitrary
`AddAction ιA ιM`, is supplied by a local instance.

The source of [StacksProject 0EKC] assumes `A` Noetherian.  The argument uses only that each `Nₙ`
is a finite module — homogeneous generators of `N₁`, compatible homogeneous lifts of them, and
graded Nakayama — so that hypothesis is dropped, which has content: the statement applies to
`A = k[x₁, x₂, …]` with every `xᵢ` of degree `1`, `I = 𝒜₊` and `Nₙ = A / Iⁿ`.  The ungraded
analogue does need `I` finitely generated, through the `I`-adic completeness of `lim Nₙ`.

The graded system is indexed by all of `ℕ`, which forces nothing: `I⁰ = A`, so the relation
`N₀ = N₁ / I⁰N₁` says `N₀ = 0`, and both hypothesis and conclusion are vacuous there; a system
indexed by `n ≥ 1` is extended by the zero module.

## References

* [StacksProject 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [StacksProject 0G1Q](https://stacks.math.columbia.edu/tag/0G1Q)
* [StacksProject 0EKC](https://stacks.math.columbia.edu/tag/0EKC)
-/

@[expose] public section

/-! ### Lifting along a tower of surjections -/

section Tower

open Function

variable {A : Type*} [CommRing A] {T : ℕ → Type*} [∀ m, AddCommGroup (T m)] [∀ m, Module A (T m)]
  (ρ : ∀ m, T (m + 1) →ₗ[A] T m)

/-- Descend from level `n` of a tower to a level `m ≤ n` by iterating the transition maps. -/
private def descend {m : ℕ} : ∀ {n : ℕ}, m ≤ n → T n → T m :=
  Nat.leRec id fun k _ f => f ∘ ρ k

private lemma descend_self {m : ℕ} (h : m ≤ m) (x : T m) : descend ρ h x = x :=
  congrFun (Nat.leRec_self (motive := fun n (_ : m ≤ n) => T n → T m) id _) x

private lemma descend_succ {m n : ℕ} (h : m ≤ n) (h' : m ≤ n + 1) (x : T (n + 1)) :
    descend ρ h' x = descend ρ h (ρ n x) :=
  congrFun (Nat.leRec_succ (motive := fun n (_ : m ≤ n) => T n → T m) id _ h) x

/-- Descending to level `m + 1` and applying `ρ m` is descending to level `m`. -/
private lemma descend_transition {m n : ℕ} (h : m + 1 ≤ n) (h' : m ≤ n) (x : T n) :
    ρ m (descend ρ h x) = descend ρ h' x := by
  induction n, h using Nat.le_induction with
  | base => rw [descend_self, descend_succ ρ le_rfl, descend_self]
  | succ n h ih =>
    rw [descend_succ ρ h, ih (Nat.le_of_succ_le h), descend_succ ρ (Nat.le_of_succ_le h) h']

/-- Ascend from level `m` of a tower of surjections to a level `n ≥ m`, using chosen sections of
the transition maps. -/
private noncomputable def ascend (hρ : ∀ m, Surjective (ρ m)) {m n : ℕ} (h : m ≤ n) (x : T m) :
    T n :=
  Nat.leRec x (fun k _ z => surjInv (hρ k) z) h

variable (hρ : ∀ m, Surjective (ρ m))

private lemma ascend_self {m : ℕ} (h : m ≤ m) (x : T m) : ascend ρ hρ h x = x :=
  Nat.leRec_self (motive := fun n (_ : m ≤ n) => T n) x _

/-- Applying `ρ n` to the ascent to level `n + 1` gives the ascent to level `n`. -/
private lemma transition_ascend {m n : ℕ} (h : m ≤ n) (h' : m ≤ n + 1) (x : T m) :
    ρ n (ascend ρ hρ h' x) = ascend ρ hρ h x := by
  rw [ascend, Nat.leRec_succ (motive := fun n (_ : m ≤ n) => T n) x _ h]
  exact surjInv_eq (hρ n) _

/-- Ascending to level `n` and descending back to level `m` does not depend on `n`. -/
private lemma descend_ascend {a m n n' : ℕ} (han : a ≤ n) (hmn : m ≤ n) (hnn' : n ≤ n')
    (x : T a) : descend ρ (hmn.trans hnn') (ascend ρ hρ (han.trans hnn') x)
      = descend ρ hmn (ascend ρ hρ han x) := by
  induction n', hnn' using Nat.le_induction with
  | base => rfl
  | succ n' hnn' ih =>
    rw [descend_succ ρ (hmn.trans hnn'), transition_ascend ρ hρ (han.trans hnn'), ih]

/-- A compatible family in a tower of surjections taking the prescribed value `x` at level `a`:
at level `m`, ascend `x` to a level above both `m` and `a`, then descend to `m`. -/
private noncomputable def family {a : ℕ} (x : T a) (m : ℕ) : T m :=
  descend ρ (le_max_left m a) (ascend ρ hρ (le_max_right m a) x)

private lemma family_self {a : ℕ} (x : T a) : family ρ hρ x a = x := by
  rw [family, descend_ascend ρ hρ le_rfl le_rfl (le_max_right a a), descend_self, ascend_self]

private lemma transition_family {a : ℕ} (x : T a) (m : ℕ) :
    ρ m (family ρ hρ x (m + 1)) = family ρ hρ x m := by
  rw [family, family,
    ← descend_ascend ρ hρ (le_max_right m a) (le_max_left m a) (max_le_max m.le_succ le_rfl),
    descend_transition ρ (le_max_left (m + 1) a) (m.le_succ.trans (le_max_left _ _))]

end Tower

/-! ### The limit of an inverse system -/

section InvLimit

variable {A : Type*} [CommRing A] (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
  (t : ∀ n, M (n + 1) →ₗ[A] M n)

/-- The inverse limit `lim_n Mₙ`, realised as the submodule of the product `∏_n Mₙ` consisting of
the compatible families `(xₙ)` satisfying `t n (x (n + 1)) = x n`. -/
@[ega "0 13.1.1", ega "IV 18.3.2.1"]
def invLimit : Submodule A (∀ n, M n) where
  carrier := { x | ∀ n, t n (x (n + 1)) = x n }
  add_mem' := by intro x y hx hy n; simp [hx n, hy n]
  zero_mem' := by intro n; simp
  smul_mem' := by intro c x hx n; simp [hx n]

/-- The canonical projection `lim_n Mₙ → Mₙ`, sending a compatible family to its `n`-th
component. -/
def invLimit.proj (n : ℕ) : invLimit M t →ₗ[A] M n where
  toFun x := (x : ∀ k, M k) n
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-- The projections are compatible with the transition maps, `t n ∘ proj (n + 1) = proj n`; that
is, they form a cone over the inverse system. -/
theorem invLimit.proj_comp_transition (n : ℕ) (x : invLimit M t) :
    t n (invLimit.proj M t (n + 1) x) = invLimit.proj M t n x :=
  x.property n

/-- Mittag-Leffler: if every transition map is surjective then so is every projection from the
limit.  Nothing beyond surjectivity of the tower is used. -/
theorem invLimit.proj_surjective (ht : ∀ n, Function.Surjective (t n)) (n : ℕ) :
    Function.Surjective (invLimit.proj M t n) := fun y =>
  ⟨⟨family t ht y, transition_family t ht y⟩, family_self t ht y⟩

end InvLimit

section SmulTop

variable {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
  [Module A N]

/-- A surjection `f : M → N` of `A`-modules carries `J M` onto `J N`. -/
private theorem map_smul_top (J : Ideal A) (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Submodule.map f (J • ⊤) = (J • ⊤ : Submodule A N) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- The restriction of a surjection `f : M → N` of `A`-modules to a map `J M → J N`. -/
private noncomputable def restrictSmulTop (J : Ideal A) (f : M →ₗ[A] N)
    (hf : Function.Surjective f) : (J • ⊤ : Submodule A M) →ₗ[A] (J • ⊤ : Submodule A N) :=
  f.restrict fun x hx => (map_smul_top J f hf).le ⟨x, hx, rfl⟩

/-- If `J • ⊤ = ⊥` in `N`, a linear map `f : M → N` kills `J • ⊤ ⊆ M`. -/
private theorem smul_top_le_ker (J : Ideal A) (f : M →ₗ[A] N)
    (h : J • (⊤ : Submodule A N) = ⊥) : J • (⊤ : Submodule A M) ≤ LinearMap.ker f := fun _ hx => by
  simpa [h] using Submodule.smul_top_le_comap_smul_top J f hx

private theorem restrictSmulTop_surjective (J : Ideal A) (f : M →ₗ[A] N)
    (hf : Function.Surjective f) : Function.Surjective (restrictSmulTop J f hf) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := (map_smul_top J f hf).ge hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- An element of `(Ideal.span t) • P`, for a finite set `t`, can be written as `∑ j ∈ t, j • c j`
with every `c j` in `P`. -/
private theorem exists_eq_sum_smul (t : Finset A) (P : Submodule A M) (r : M)
    (hr : r ∈ (Ideal.span (t : Set A)) • P) :
    ∃ c : A → M, (∀ j, c j ∈ P) ∧ r = ∑ j ∈ t, j • c j := by
  classical
  refine Submodule.smul_induction_on hr ?_ ?_
  · intro a ha p hp
    rw [Ideal.span, Submodule.mem_span_finset] at ha
    obtain ⟨f, hf⟩ := ha
    refine ⟨fun j => f j • p, fun j => P.smul_mem _ hp, ?_⟩
    rw [← hf.right, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_assoc, smul_smul, smul_smul, mul_comm]
  · rintro x y ⟨cx, hcx, hxeq⟩ ⟨cy, hcy, hyeq⟩
    refine ⟨fun j => cx j + cy j, fun j => P.add_mem (hcx j) (hcy j), ?_⟩
    rw [hxeq, hyeq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_add]

end SmulTop

/-! ### Inverse systems with `Mₙ = M (n + 1) / Iⁿ M (n + 1)`

What follows uses only surjectivity of the transition maps and the tower relation
`ker (t n) = Iⁿ M (n + 1)`; it is shared by the ungraded and the graded halves of this file. -/

section System

variable {A : Type*} [CommRing A] {I : Ideal A} {N : ℕ → Type*} [∀ n, AddCommGroup (N n)]
  [∀ n, Module A (N n)] (t : ∀ n, N (n + 1) →ₗ[A] N n)
  (htsurj : ∀ n, Function.Surjective (t n))
  (htker : ∀ n, LinearMap.ker (t n) = I ^ n • (⊤ : Submodule A (N (n + 1))))

include htsurj htker in
/-- `Iⁿ N_{m+1}` is the preimage of `Iⁿ N_m` for `n ≤ m`: the kernel `I^m N_{m+1}` of the
transition map is already contained in `Iⁿ N_{m+1}`. -/
private lemma comap_pow_smul_top {n m : ℕ} (hnm : n ≤ m) :
    Submodule.comap (t m) (I ^ n • (⊤ : Submodule A (N m)))
      = I ^ n • (⊤ : Submodule A (N (m + 1))) := by
  rw [← map_smul_top (I ^ n) (t m) (htsurj m), Submodule.comap_map_eq, htker m]
  exact sup_eq_left.2 (Submodule.smul_le.2 fun r hr n hn =>
    Submodule.smul_mem_smul (Ideal.pow_le_pow_right hnm hr) hn)

include htsurj htker in
/-- `Iⁿ` annihilates `Nₙ`, since `Nₙ = N_{n+1}/Iⁿ N_{n+1}`. -/
private lemma pow_smul_top_eq_bot (n : ℕ) : I ^ n • (⊤ : Submodule A (N n)) = ⊥ := by
  rw [← map_smul_top (I ^ n) (t n) (htsurj n), ← htker n, eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  simpa using hy

include htsurj htker in
/-- A compatible sequence vanishing at level `n` lies in `Iⁿ` at every later level. -/
private lemma mem_pow_smul_top_of_eq_zero {u : ∀ n, N n} (hu : ∀ n, t n (u (n + 1)) = u n)
    {n : ℕ} (hn : u n = 0) (k : ℕ) : u (n + k) ∈ I ^ n • (⊤ : Submodule A (N (n + k))) := by
  induction k with
  | zero => rw [show u (n + 0) = u n from rfl, hn]; exact Submodule.zero_mem _
  | succ k ih =>
    have hc : u (n + k + 1) ∈
        Submodule.comap (t (n + k)) (I ^ n • (⊤ : Submodule A (N (n + k)))) := by
      simpa [hu (n + k)] using ih
    rw [comap_pow_smul_top t htsurj htker (Nat.le_add_right n k)] at hc
    exact hc

/-- A compatible sequence vanishing at a later level vanishes at level `n`. -/
private lemma eq_zero_of_later_eq_zero {u : ∀ n, N n} (hu : ∀ n, t n (u (n + 1)) = u n) {n : ℕ} :
    ∀ k, u (n + k) = 0 → u n = 0
  | 0, h => h
  | k + 1, h => eq_zero_of_later_eq_zero hu k
      (by rw [← hu (n + k), show u (n + k + 1) = 0 from h, map_zero])

include htsurj htker in
/-- A compatible sequence vanishing at level `n` lies in `Iⁿ` at every level: below `n` it
vanishes outright, at and above `n` it is `mem_pow_smul_top_of_eq_zero`. -/
private lemma forall_mem_pow_smul_top_of_eq_zero {u : ∀ n, N n}
    (hu : ∀ n, t n (u (n + 1)) = u n) {n : ℕ} (hn : u n = 0) (m : ℕ) :
    u m ∈ I ^ n • (⊤ : Submodule A (N m)) := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact mem_pow_smul_top_of_eq_zero t htsurj htker hu hn k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [eq_zero_of_later_eq_zero t hu k hn]
    exact Submodule.zero_mem _

end System

namespace Stacks.AdicCompletion.InverseLimit

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- A bundled inverse system `(M n, π n)` of `A`-modules satisfying the hypothesis of Stacks
tag 09B8: each transition map `π n : M (n+1) → M n` is surjective with kernel exactly
`Iⁿ M (n+1)`, equivalently `M n = M (n+1) / Iⁿ M (n+1)`. -/
structure InverseSystem where
  /-- The family of `A`-modules. -/
  M : ℕ → Type*
  /-- Each `M n` is an additive commutative group. -/
  [addCommGroup : ∀ n, AddCommGroup (M n)]
  /-- Each `M n` is an `A`-module. -/
  [module : ∀ n, Module A (M n)]
  /-- The transition maps `π n : M (n+1) → M n`. -/
  π : ∀ n, M (n + 1) →ₗ[A] M n
  /-- The transition maps are surjective. -/
  surjective : ∀ n, Function.Surjective (π n)
  /-- The kernel of `π n` is exactly `Iⁿ M (n+1)`, i.e. `M n = M (n+1) / Iⁿ M (n+1)`. -/
  ker_π : ∀ n, LinearMap.ker (π n) = I ^ n • (⊤ : Submodule A (M (n + 1)))

attribute [instance] InverseSystem.addCommGroup InverseSystem.module

namespace InverseSystem

variable {I}
variable (S : InverseSystem I)

/-- The limit `M = lim_n M n` of the system. -/
def limit : Submodule A (∀ n, S.M n) := invLimit S.M S.π

/-- The canonical projection `p n : M → M n` from the limit to the `n`-th module. -/
def proj (n : ℕ) : S.limit →ₗ[A] S.M n := invLimit.proj S.M S.π n

/-- Each limit projection `p n : M → M n` is surjective; this is Mittag-Leffler and does not
require finite generation of `I`. -/
theorem proj_surjective (n : ℕ) : Function.Surjective (S.proj n) :=
  invLimit.proj_surjective S.M S.π S.surjective n

/-! ### Structural consequences of the tower relation -/

/-- `Iⁿ` annihilates `Mₙ`: as `π n` is surjective, `Iⁿ Mₙ` is the image of
`Iⁿ M_{n+1} = ker (π n)`, hence zero. -/
private theorem smul_top_self (n : ℕ) : I ^ n • (⊤ : Submodule A (S.M n)) = ⊥ :=
  pow_smul_top_eq_bot S.π S.surjective S.ker_π n

/-- Elements of `Mₘ` whose difference lies in `Iᵏ Mₘ` for some `k ≥ m` are equal. -/
private theorem eq_of_sub_mem_pow_smul_top {m k : ℕ} (hmk : m ≤ k) {a b : S.M m}
    (h : a - b ∈ I ^ k • (⊤ : Submodule A (S.M m))) : a = b := by
  rw [← sub_eq_zero, ← Submodule.mem_bot A, ← S.smul_top_self m]
  exact Submodule.smul_mono (Ideal.pow_le_pow_right hmk) le_rfl h

/-- A compatible family in the limit vanishing at level `a` has every component in `Iᵃ`. -/
private theorem mem_pow_smul_top_of_apply_eq_zero {x : ∀ m, S.M m} (hx : x ∈ S.limit) {a : ℕ}
    (ha : x a = 0) (m : ℕ) : x m ∈ I ^ a • (⊤ : Submodule A (S.M m)) :=
  forall_mem_pow_smul_top_of_eq_zero S.π S.surjective S.ker_π hx ha m

/-! ### The kernel of the limit projection

The kernel of `p n : M → M n` is exactly `Iⁿ M`, so that with surjectivity the induced map
`M / Iⁿ M → M n` is an isomorphism.  The inclusion `Iⁿ M ⊆ ker p_n` holds because `p_n` sends
`Iⁿ M` into `Iⁿ M_n`, which is `0`.  The converse needs `I.FG`: an `x` with `x n = 0` must be
exhibited as a *finite* combination `∑ aⱼ • vⱼ` with `aⱼ ∈ Iⁿ` and `vⱼ` in the limit, and a
finite generating set of `Iⁿ` is what the error `x - ∑ⱼ aⱼ • vⱼ` is improved along, one power of
`I` at a time. -/

/-- The components of a combination `∑_{j ∈ t} j • g j` of limit elements, level by level. -/
private theorem coe_sum_smul_apply (t : Finset A) (g : A → S.limit) (m : ℕ) :
    ((∑ j ∈ t, j • g j : S.limit) : ∀ m, S.M m) m = ∑ j ∈ t, j • (g j : ∀ m, S.M m) m := by
  simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply]

/-- An element of `Iᵏ Mₐ` extends to a compatible family in the limit all of whose components
lie in `Iᵏ`: Mittag-Leffler for the subsystem `(Iᵏ Mₘ)`, whose transition maps are again
surjective. -/
private theorem exists_mem_limit_forall_mem_pow_smul_top (k a : ℕ) (c : S.M a)
    (hc : c ∈ I ^ k • (⊤ : Submodule A (S.M a))) :
    ∃ v : S.limit, (v : ∀ m, S.M m) a = c ∧
      ∀ m, (v : ∀ m, S.M m) m ∈ I ^ k • (⊤ : Submodule A (S.M m)) := by
  let T : ℕ → Type _ := fun m => (I ^ k • ⊤ : Submodule A (S.M m))
  let ρ : ∀ m, T (m + 1) →ₗ[A] T m :=
    fun m => restrictSmulTop (I ^ k) (S.π m) (S.surjective m)
  have hρ : ∀ m, Function.Surjective (ρ m) :=
    fun m => restrictSmulTop_surjective (I ^ k) (S.π m) (S.surjective m)
  let cc : T a := ⟨c, hc⟩
  refine ⟨⟨fun m => ((family ρ hρ cc m : T m) : S.M m), fun m => ?_⟩, ?_,
    fun m => (family ρ hρ cc m).property⟩
  · have hco : ((ρ m (family ρ hρ cc (m + 1)) : T m) : S.M m)
        = S.π m ((family ρ hρ cc (m + 1) : T (m + 1)) : S.M (m + 1)) := rfl
    rw [← hco, transition_family ρ hρ cc m]
  · change ((family ρ hρ cc a : T a) : S.M a) = c
    rw [family_self]

/-- One improvement step: given a finite generating set `t` of `Iⁿ` and a limit element `r` with
all components in `I^{n+k}`, there are coefficients `h j` in the limit with all components in `Iᵏ`
such that `r - ∑_{j ∈ t} j • h j` has all components in `I^{n+k+1}`. -/
private theorem exists_sub_sum_smul_mem_pow_succ_smul_top (n k : ℕ) (t : Finset A)
    (ht : Ideal.span (t : Set A) = I ^ n) (r : S.limit)
    (hr : ∀ m, (r : ∀ m, S.M m) m ∈ I ^ (n + k) • (⊤ : Submodule A (S.M m))) :
    ∃ h : A → S.limit,
      (∀ j m, (h j : ∀ m, S.M m) m ∈ I ^ k • (⊤ : Submodule A (S.M m))) ∧
      ∀ m, ((r : ∀ m, S.M m) m - ∑ j ∈ t, j • (h j : ∀ m, S.M m) m)
        ∈ I ^ (n + k + 1) • (⊤ : Submodule A (S.M m)) := by
  have hr' : (r : ∀ m, S.M m) (n + k + 1)
      ∈ Ideal.span (t : Set A) • (I ^ k • (⊤ : Submodule A (S.M (n + k + 1)))) := by
    rw [ht, ← mul_smul, ← pow_add]
    exact hr (n + k + 1)
  obtain ⟨c, hc, hceq⟩ := exists_eq_sum_smul t _ _ hr'
  choose h hval hsmall using fun j =>
    S.exists_mem_limit_forall_mem_pow_smul_top k (n + k + 1) (c j) (hc j)
  refine ⟨h, hsmall, fun m => ?_⟩
  have hd0 : ((r - ∑ j ∈ t, j • h j : S.limit) : ∀ m, S.M m) (n + k + 1) = 0 := by
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, S.coe_sum_smul_apply, hceq, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [hval j]
  have hmem := S.mem_pow_smul_top_of_apply_eq_zero (r - ∑ j ∈ t, j • h j).property hd0 m
  rwa [AddSubgroupClass.coe_sub, Pi.sub_apply, S.coe_sum_smul_apply] at hmem

/-- The improvement process converges: for a finite generating set `t` of `Iⁿ` and an `x` all of
whose components lie in `Iⁿ`, there are coefficient families `seq k : A → M` with
`x - ∑_{j ∈ t} j • seq k j` componentwise in `I^{n+k}` and `seq (k+1) j - seq k j` componentwise
in `Iᵏ`. -/
private theorem exists_seq_forall_sub_sum_smul_mem (n : ℕ) (t : Finset A)
    (ht : Ideal.span (t : Set A) = I ^ n) (x : S.limit)
    (hx : ∀ m, (x : ∀ m, S.M m) m ∈ I ^ n • (⊤ : Submodule A (S.M m))) :
    ∃ seq : ℕ → A → S.limit,
      (∀ k m, ((x : ∀ m, S.M m) m - ∑ j ∈ t, j • (seq k j : ∀ m, S.M m) m)
        ∈ I ^ (n + k) • (⊤ : Submodule A (S.M m))) ∧
      ∀ k j m, ((seq (k + 1) j : ∀ m, S.M m) m - (seq k j : ∀ m, S.M m) m)
        ∈ I ^ k • (⊤ : Submodule A (S.M m)) := by
  set Inv : ℕ → (A → S.limit) → Prop := fun k g => ∀ m,
    ((x : ∀ m, S.M m) m - ∑ j ∈ t, j • (g j : ∀ m, S.M m) m)
      ∈ I ^ (n + k) • (⊤ : Submodule A (S.M m))
  have step : ∀ (k : ℕ) (g : A → S.limit), Inv k g →
      ∃ h : A → S.limit, (∀ j m, (h j : ∀ m, S.M m) m ∈ I ^ k • (⊤ : Submodule A (S.M m))) ∧
        Inv (k + 1) fun j => g j + h j := by
    intro k g hg
    obtain ⟨h, hsmall, herr⟩ := S.exists_sub_sum_smul_mem_pow_succ_smul_top n k t ht
      (x - ∑ j ∈ t, j • g j) fun m => by
        rw [AddSubgroupClass.coe_sub, Pi.sub_apply, S.coe_sum_smul_apply]; exact hg m
    refine ⟨h, hsmall, fun m => ?_⟩
    have he := herr m
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, S.coe_sum_smul_apply] at he
    simp only [show ∀ j, ((g j + h j : S.limit) : ∀ m, S.M m) m
      = (g j : ∀ m, S.M m) m + (h j : ∀ m, S.M m) m from fun _ => rfl, smul_add,
      Finset.sum_add_distrib, ← sub_sub]
    exact he
  have hbase : Inv 0 fun _ => 0 := fun m => by simpa using hx m
  choose up hup hupInv using step
  let F : ∀ k, {g : A → S.limit // Inv k g} := fun k => Nat.rec ⟨fun _ => 0, hbase⟩
    (fun k p => ⟨fun j => p.1 j + up k p.1 p.2 j, hupInv k p.1 p.2⟩) k
  refine ⟨fun k => (F k).1, fun k => (F k).2, fun k j m => ?_⟩
  rw [show ((F (k + 1)).1 j : ∀ m, S.M m) m
      = ((F k).1 j : ∀ m, S.M m) m + (up k (F k).1 (F k).2 j : ∀ m, S.M m) m from rfl,
    add_sub_cancel_left]
  exact hup k (F k).1 (F k).2 j m

/-- The diagonal `m ↦ v (m+1) m` of a family of limit elements whose successive differences lie
in `Iᵏ` at step `k` is again a compatible family: since `Iᵏ Mₘ = 0` for `m ≤ k`, the family is
constant at level `m` from step `m` on. -/
private theorem diagonal_mem_limit (v : ℕ → S.limit)
    (hv : ∀ k m, ((v (k + 1) : ∀ m, S.M m) m - (v k : ∀ m, S.M m) m)
      ∈ I ^ k • (⊤ : Submodule A (S.M m))) :
    (fun m => (v (m + 1) : ∀ m, S.M m) m) ∈ S.limit := by
  have hstab : ∀ k m, m ≤ k → (v (k + 1) : ∀ m, S.M m) m = (v k : ∀ m, S.M m) m := by
    intro k m hmk
    exact S.eq_of_sub_mem_pow_smul_top hmk (hv k m)
  refine fun m => ?_
  change S.π m ((v (m + 1 + 1) : ∀ k, S.M k) (m + 1)) = (v (m + 1) : ∀ k, S.M k) m
  rw [(v (m + 1 + 1)).property m]
  exact hstab (m + 1) m m.le_succ

/-- A limit element whose `n`-th component vanishes lies in `Iⁿ M`: the hard inclusion
`ker p_n ⊆ Iⁿ M`, and the only step using that `I` is finitely generated. -/
private theorem mem_pow_smul_top_of_proj_eq_zero (hI : I.FG) (n : ℕ) (x : S.limit)
    (hx : (x : ∀ m, S.M m) n = 0) : x ∈ I ^ n • (⊤ : Submodule A S.limit) := by
  obtain ⟨t, ht⟩ := Ideal.FG.pow (n := n) hI
  obtain ⟨seq, hinv, hstep⟩ := S.exists_seq_forall_sub_sum_smul_mem n t ht x
    (S.mem_pow_smul_top_of_apply_eq_zero x.property hx)
  set v : A → S.limit := fun j =>
    ⟨_, S.diagonal_mem_limit (fun k => seq k j) fun k m => hstep k j m⟩
  have hxeq : x = ∑ j ∈ t, j • v j := by
    refine Subtype.ext (funext fun m => ?_)
    rw [S.coe_sum_smul_apply]
    exact S.eq_of_sub_mem_pow_smul_top (k := n + (m + 1)) (by omega) (hinv (m + 1) m)
  rw [hxeq]
  exact Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem_smul (ht ▸ Ideal.subset_span hj) Submodule.mem_top

/-- The kernel of the limit projection `p n : M → M n` is exactly `Iⁿ M`.  With
`proj_surjective` this identifies `M / Iⁿ M` with `M n`. -/
theorem ker_proj (hI : I.FG) (n : ℕ) :
    LinearMap.ker (S.proj n) = I ^ n • (⊤ : Submodule A S.limit) := by
  refine le_antisymm (fun x hx => S.mem_pow_smul_top_of_proj_eq_zero hI n x hx) ?_
  exact smul_top_le_ker _ _ (S.smul_top_self n)

/-- Identification of the quotients: the map `M / Iⁿ M → M n` induced by the limit projection
`p n` is an isomorphism of `A`-modules. -/
@[stacks 09B8 "(1)"]
noncomputable def quotientEquiv (hI : I.FG) (n : ℕ) :
    (S.limit ⧸ (I ^ n • (⊤ : Submodule A S.limit))) ≃ₗ[A] S.M n :=
  (Submodule.quotEquivOfEq _ _ (S.ker_proj hI n).symm).trans
    ((S.proj n).quotKerEquivOfSurjective (S.proj_surjective n))

/-! ### `I`-adic completeness -/

/-- The limit is `I`-adically separated: an `x` in `⋂_k Iᵏ M` lies in `Iᵏ M = ker p_k` for every
`k`, so all its components vanish. -/
theorem isHausdorff (hI : I.FG) : IsHausdorff I S.limit := by
  refine ⟨fun x h => Subtype.ext (funext fun k => ?_)⟩
  have hmem : x ∈ LinearMap.ker (S.proj k) := by
    rw [S.ker_proj hI k]; exact SModEq.zero.mp (h k)
  exact hmem

/-- The limit is `I`-adically precomplete: an `I`-adically Cauchy family `f : ℕ → M`, so that
`f (k+1) ≡ f k [SMOD Iᵏ M]`, has the compatible family `k ↦ p_k (f k)` as a limit. -/
theorem isPrecomplete (hI : I.FG) : IsPrecomplete I S.limit := by
  refine ⟨fun f hcau => ?_⟩
  have hmem : (fun m => (f m : ∀ j, S.M j) m) ∈ S.limit := fun m => by
    change S.π m ((f (m + 1) : ∀ j, S.M j) (m + 1)) = (f m : ∀ j, S.M j) m
    rw [(f (m + 1)).property m]
    have hker : f m - f (m + 1) ∈ LinearMap.ker (S.proj m) := by
      rw [S.ker_proj hI m]; exact SModEq.sub_mem.mp (hcau m.le_succ)
    have hval : ((f m - f (m + 1) : S.limit) : ∀ j, S.M j) m = 0 := hker
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, sub_eq_zero] at hval
    exact hval.symm
  refine ⟨⟨_, hmem⟩, fun n => ?_⟩
  rw [SModEq.sub_mem, ← S.ker_proj hI n]
  change ((f n - ⟨_, hmem⟩ : S.limit) : ∀ j, S.M j) n = 0
  rw [AddSubgroupClass.coe_sub, Pi.sub_apply, sub_eq_zero]

/-- The limit `M = lim_n M n` is `I`-adically complete: the canonical map `M → lim_k M / Iᵏ M`
is an isomorphism. -/
@[stacks 09B8 "(2)"]
theorem isAdicComplete (hI : I.FG) : IsAdicComplete I S.limit :=
  { toIsHausdorff := S.isHausdorff hI
    toIsPrecomplete := S.isPrecomplete hI }

end InverseSystem

end Stacks.AdicCompletion.InverseLimit

/-! ### Adic completeness of a limit annihilated by the powers of `I`

Only `Iⁿ Mₙ = 0` is assumed here, and no relation between consecutive terms of the system: the
limit is still `I`-adically complete, being a direct summand of its own completion. -/

section

open AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)
variable (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
variable (t : ∀ n, M (n + 1) →ₗ[A] M n)

section Retract

/-- The projection to level `k` kills `Iᵏ (lim Mₙ)`, since it lands in `Iᵏ Mₖ = 0`. -/
private theorem proj_factors (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ) :
    I ^ k • (⊤ : Submodule A (invLimit M t)) ≤ LinearMap.ker (invLimit.proj M t k) := by
  exact smul_top_le_ker _ _ (hM k)

/-- The map `(lim Mₙ) ⧸ Iᵏ (lim Mₙ) → Mₖ` induced by the projection to level `k`. -/
private noncomputable def barProj (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ) :
    invLimit M t ⧸ (I ^ k • (⊤ : Submodule A (invLimit M t))) →ₗ[A] M k :=
  Submodule.liftQ _ (invLimit.proj M t k) (proj_factors I M t hM k)

/-- `barProj k` sends the class of a compatible family to its `k`-th component. -/
private theorem barProj_mk (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ)
    (x : invLimit M t) :
    barProj I M t hM k (Submodule.Quotient.mk x) = invLimit.proj M t k x :=
  rfl

/-- The maps `barProj k` are compatible with the transition maps `t k` of the inverse system,
through the adic-completion transition maps. -/
private theorem barProj_compat (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ)
    (c : invLimit M t ⧸ (I ^ (k + 1) • (⊤ : Submodule A (invLimit M t)))) :
    t k (barProj I M t hM (k + 1) c)
      = barProj I M t hM k (AdicCompletion.transitionMap I (invLimit M t) (Nat.le_succ k) c) := by
  induction c using Submodule.Quotient.induction_on with
  | _ x =>
    change t k (barProj I M t hM (k + 1) (Submodule.Quotient.mk x))
      = barProj I M t hM k (Submodule.Quotient.mk x)
    rw [barProj_mk, barProj_mk]
    exact invLimit.proj_comp_transition M t k x

/-- The `k`-th evaluation `(lim Mₙ)^∧ → Mₖ`, the composite of `barProj k` with the completion's
`eval`. -/
private noncomputable def ev (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ) :
    AdicCompletion I (invLimit M t) →ₗ[A] M k :=
  barProj I M t hM k ∘ₗ AdicCompletion.eval I (invLimit M t) k

/-- The family `(ev k)` is compatible with the transition maps `t k`. -/
private theorem ev_compat (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ)
    (y : AdicCompletion I (invLimit M t)) :
    t k (ev I M t hM (k + 1) y) = ev I M t hM k y := by
  have hev : AdicCompletion.transitionMap I (invLimit M t) (Nat.le_succ k)
      (AdicCompletion.eval I (invLimit M t) (k + 1) y)
      = AdicCompletion.eval I (invLimit M t) k y := by
    rw [← LinearMap.comp_apply, AdicCompletion.transitionMap_comp_eval]
  simp only [ev, LinearMap.comp_apply]
  rw [barProj_compat I M t hM k (AdicCompletion.eval I (invLimit M t) (k + 1) y), hev]

/-- The retraction `(lim Mₙ)^∧ → lim Mₙ`, the limit of the maps
`(lim Mₙ)^∧ → (lim Mₙ) ⧸ Iᵏ (lim Mₙ) → Mₖ`. -/
private noncomputable def retract (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) :
    AdicCompletion I (invLimit M t) →ₗ[A] invLimit M t :=
  LinearMap.codRestrict (invLimit M t) (LinearMap.pi fun k => ev I M t hM k) fun y k => by
    change t k (ev I M t hM (k + 1) y) = ev I M t hM k y
    exact ev_compat I M t hM k y

/-- The `k`-th component of `retract y` is `ev k y`. -/
private theorem proj_retract (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (k : ℕ)
    (y : AdicCompletion I (invLimit M t)) :
    invLimit.proj M t k (retract I M t hM y) = ev I M t hM k y := rfl

/-- `retract` is a left inverse of `AdicCompletion.of`, exhibiting `lim Mₙ` as a direct summand
of its completion. -/
private theorem retract_of (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (x : invLimit M t) :
    retract I M t hM (AdicCompletion.of I (invLimit M t) x) = x :=
  Subtype.ext <| funext fun k => by
    change barProj I M t hM k
        (AdicCompletion.eval I (invLimit M t) k (AdicCompletion.of I (invLimit M t) x))
      = invLimit.proj M t k x
    rw [AdicCompletion.eval_of]
    rfl

/-- `retract` sends `Iᵐ (lim Mₙ)^∧` into `Iᵐ (lim Mₙ)`. -/
private theorem retract_smul (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) (m : ℕ)
    (z : AdicCompletion I (invLimit M t))
    (hz : z ∈ I ^ m • (⊤ : Submodule A (AdicCompletion I (invLimit M t)))) :
    retract I M t hM z ∈ I ^ m • (⊤ : Submodule A (invLimit M t)) :=
  Submodule.smul_top_le_comap_smul_top _ (retract I M t hM) hz

end Retract

/-- **Stacks 0G1Q**.  For a finitely generated ideal `I` of a commutative ring `A` and an
inverse system `(M_n)` of `A`-modules with `I^n M_n = 0` for all `n`, the inverse limit
`M = lim_n M_n` is `I`-adically complete: it is a direct summand of its own completion, which
is `I`-adically complete because `I` is finitely generated. -/
@[stacks 0G1Q]
theorem invLimit_isAdicComplete (hI : I.FG)
    (hM : ∀ n, I ^ n • (⊤ : Submodule A (M n)) = ⊥) :
    IsAdicComplete I (invLimit M t) := by
  have hausdorff : IsHausdorff I (invLimit M t) := by
    refine ⟨fun x hx => ?_⟩
    refine Subtype.ext <| funext fun k => ?_
    change invLimit.proj M t k x = invLimit.proj M t k (0 : invLimit M t)
    rw [_root_.map_zero]
    exact LinearMap.mem_ker.mp (proj_factors I M t hM k (SModEq.zero.mp (hx k)))
  have precomplete : IsPrecomplete I (invLimit M t) := by
    refine ⟨fun f hf => ?_⟩
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        AdicCompletion.of I (invLimit M t) (f m) ≡ AdicCompletion.of I (invLimit M t) (f n)
          [SMOD I ^ m • (⊤ : Submodule A (AdicCompletion I (invLimit M t)))] := by
      intro m n hmn
      rw [SModEq.sub_mem, ← map_sub]
      exact Submodule.smul_top_le_comap_smul_top _ (AdicCompletion.of I (invLimit M t))
        (SModEq.sub_mem.mp (hf hmn))
    obtain ⟨Y, hY⟩ := (AdicCompletion.isAdicComplete hI).toIsPrecomplete.prec hcauchy
    refine ⟨retract I M t hM Y, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have h := retract_smul I M t hM n _ (SModEq.sub_mem.mp (hY n))
    rwa [map_sub, retract_of] at h
  exact { toIsHausdorff := hausdorff, toIsPrecomplete := precomplete }

end

/-! ### Algebraizing an inverse system of finite graded modules

The witness is built as `gradedLimit`, the submodule of `∀ n, N n` generated by the compatible
sequences `Lm d` that are homogeneous of a single degree `d` at every level; the whole
construction is private to this file, and the algebraization is the theorem that closes it. -/

section

universe u v
open DirectSum

namespace GradedInverseSystem

attribute [local instance] Classical.propDecidable

/-! ### The degree shift `ℕ ↷ ℤ` -/

/-- The action of the degrees of an `ℕ`-graded ring on the degrees of a `ℤ`-graded module. -/
@[instance_reducible] private def natVAddInt : AddAction ℕ ℤ where
  vadd i d := (i : ℤ) + d
  zero_vadd d := by
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd i j d := by
    change ((i + j : ℕ) : ℤ) + d = (i : ℤ) + ((j : ℤ) + d)
    push_cast
    ring

attribute [local instance] natVAddInt

private lemma natVAddInt_vadd (i : ℕ) (d : ℤ) : i +ᵥ d = (i : ℤ) + d := rfl

/-- A degree of a `ℤ`-graded module is shifted by a degree in `ℕ` order preservingly and
cancellatively: the hypothesis under which the graded Nakayama lemma is stated. -/
private lemma isOrderedCancelVAdd_nat_int : IsOrderedCancelVAdd ℕ ℤ where
  vadd_le_vadd_left b c h a := by simp only [natVAddInt_vadd]; omega
  vadd_le_vadd_right c d h a := by simp only [natVAddInt_vadd]; omega
  le_of_vadd_le_vadd_left a b c h := by simp only [natVAddInt_vadd] at h; omega
  le_of_vadd_le_vadd_right a b c h := by simp only [natVAddInt_vadd] at h; omega

attribute [local instance] isOrderedCancelVAdd_nat_int

/-! ### Homogeneous components -/

section Components

variable {ι M τ : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike τ M]
  [AddSubmonoidClass τ M] (ℳ : ι → τ) [DirectSum.Decomposition ℳ]

/-- The `i`-th homogeneous component of an element of a graded module, as an additive map. -/
private noncomputable def cpt (i : ι) : M →+ M where
  toFun x := (decompose ℳ x i : M)
  map_zero' := by simp
  map_add' x y := by
    simp only [decompose_add, DirectSum.add_apply, AddMemClass.coe_add]

private lemma cpt_apply (i : ι) (x : M) : cpt ℳ i x = (decompose ℳ x i : M) := rfl

private lemma cpt_mem (i : ι) (x : M) : cpt ℳ i x ∈ ℳ i := (decompose ℳ x i).2

private lemma cpt_of_mem_same {i : ι} {x : M} (hx : x ∈ ℳ i) : cpt ℳ i x = x :=
  decompose_of_mem_same ℳ hx

private lemma cpt_of_mem_ne {i j : ι} {x : M} (hx : x ∈ ℳ i) (h : i ≠ j) : cpt ℳ j x = 0 :=
  decompose_of_mem_ne ℳ hx h

private lemma sum_cpt (x : M) : ∑ i ∈ (decompose ℳ x).support, cpt ℳ i x = x :=
  sum_support_decompose ℳ x

private lemma cpt_eq_zero_iff_notMem_support {i : ι} {x : M} :
    cpt ℳ i x = 0 ↔ i ∉ (decompose ℳ x).support := by
  rw [cpt_apply, ZeroMemClass.coe_eq_zero, DFinsupp.notMem_support_iff]

end Components

section SmulComponents

variable {ι κ σ τ A M : Type*} [DecidableEq ι] [AddMonoid ι] [Semiring A] [SetLike σ A]
  [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜] [AddCommMonoid M] [Module A M]
  [DecidableEq κ] [SetLike τ M] [AddSubmonoidClass τ M] (ℳ : κ → τ)
  [DirectSum.Decomposition ℳ]

/-- The homogeneous expansion of the scalar in a product `a • x`. -/
private lemma smul_eq_sum_cpt_smul (a : A) (x : M) :
    a • x = ∑ i ∈ (decompose 𝒜 a).support, cpt 𝒜 i a • x := by
  rw [← Finset.sum_smul, sum_cpt]

/-- The homogeneous expansion of the module element in a product `a • x`. -/
private lemma smul_eq_sum_smul_cpt (a : A) (x : M) :
    a • x = ∑ d ∈ (decompose ℳ x).support, a • cpt ℳ d x := by
  rw [← Finset.smul_sum, sum_cpt]

end SmulComponents

/-! ### Low-degree vanishing and graded Nakayama -/

section GradedModule

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] {I : Ideal A} {N : Type*} [AddCommGroup N] [Module A N]
  {𝒩 : ℤ → AddSubgroup N} [DirectSum.Decomposition 𝒩]

/-- The elements of a `ℤ`-graded module whose homogeneous components in degrees `< c` vanish. -/
private def degGE (𝒩 : ℤ → AddSubgroup N) [DirectSum.Decomposition 𝒩] (c : ℤ) :
    AddSubgroup N where
  carrier := {x | ∀ d : ℤ, d < c → cpt 𝒩 d x = 0}
  zero_mem' := fun d _ => map_zero _
  add_mem' := fun ha hb d hd => by rw [map_add, ha d hd, hb d hd, add_zero]
  neg_mem' := fun ha d hd => by rw [map_neg, ha d hd, neg_zero]

private lemma mem_degGE_of_mem_grade {c d : ℤ} {x : N} (hx : x ∈ 𝒩 d) (h : c ≤ d) :
    x ∈ degGE 𝒩 c := fun e he => cpt_of_mem_ne 𝒩 hx (by omega)

private lemma degGE_mono {c c' : ℤ} (h : c' ≤ c) : degGE 𝒩 c ≤ degGE 𝒩 c' :=
  fun _ hx d hd => hx d (lt_of_lt_of_le hd h)

/-- A power of a homogeneous ideal is homogeneous. -/
private lemma isHomogeneous_pow {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (n : ℕ) :
    (J ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero => simpa using (⊤ : HomogeneousIdeal 𝒜).isHomogeneous
  | succ n ih => rw [pow_succ]; exact ih.mul hJ

variable (h𝒩 : ∀ (i : ℕ) (d : ℤ) (a : A) (x : N), a ∈ 𝒜 i → x ∈ 𝒩 d → a • x ∈ 𝒩 (i + d))

include h𝒩

omit [AddSubmonoidClass σ A] [GradedRing 𝒜] in
private lemma smul_mem_degGE_of_mem_grade {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) {c : ℤ} {x : N}
    (hx : x ∈ degGE 𝒩 c) : a • x ∈ degGE 𝒩 ((i : ℤ) + c) := by
  rw [smul_eq_sum_smul_cpt 𝒩 a x]
  refine sum_mem fun d hd => ?_
  have hcd : c ≤ d := by
    by_contra hlt
    exact (cpt_eq_zero_iff_notMem_support 𝒩).1 (hx d (by omega)) hd
  exact mem_degGE_of_mem_grade (h𝒩 i d a _ ha (cpt_mem 𝒩 d x)) (by omega)

private lemma smul_mem_degGE (a : A) {c : ℤ} {x : N} (hx : x ∈ degGE 𝒩 c) :
    a • x ∈ degGE 𝒩 c := by
  rw [smul_eq_sum_cpt_smul (𝒜 := 𝒜) a x]
  refine sum_mem fun i _ => ?_
  exact degGE_mono (by omega) (smul_mem_degGE_of_mem_grade h𝒩 (cpt_mem 𝒜 i a) hx)

/-- One step of the vanishing: an element of `𝒜₊` raises the degree bound by one. -/
private lemma smul_mem_degGE_succ (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {a : A} (ha : a ∈ I) {c : ℤ} {x : N}
    (hx : x ∈ degGE 𝒩 c) : a • x ∈ degGE 𝒩 (1 + c) := by
  rw [smul_eq_sum_cpt_smul (𝒜 := 𝒜) a x]
  refine sum_mem fun i _ => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · have hmem : cpt 𝒜 0 a ∈ HomogeneousIdeal.irrelevant 𝒜 := hI (hIhom 0 ha)
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hmem
    rw [show cpt 𝒜 0 a = 0 from (cpt_of_mem_same 𝒜 (cpt_mem 𝒜 0 a)).symm.trans hmem, zero_smul]
    exact (degGE 𝒩 (1 + c)).zero_mem
  · exact degGE_mono (by omega) (smul_mem_degGE_of_mem_grade h𝒩 (cpt_mem 𝒜 i a) hx)

/-- `Iᵐ` raises the degree bound by `m`. -/
private lemma smul_mem_degGE_pow (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (m : ℕ) {a : A} (ha : a ∈ I ^ m)
    {c : ℤ} {x : N} (hx : x ∈ degGE 𝒩 c) : a • x ∈ degGE 𝒩 ((m : ℤ) + c) := by
  induction m generalizing a c x with
  | zero => simpa using smul_mem_degGE h𝒩 a hx
  | succ m ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb a' ha' => ?_) fun u v hu hv => ?_
    · rw [mul_smul]
      exact degGE_mono (by push_cast; omega)
        (ih hb (smul_mem_degGE_succ h𝒩 hIhom hI ha' hx))
    · rw [add_smul]
      exact (degGE 𝒩 _).add_mem hu hv

/-- `Iᵐ N` vanishes in degrees `< c + m` when `N` lives in degrees `≥ c`. -/
private lemma pow_smul_top_le_degGE (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) (m : ℕ) {c : ℤ}
    (htop : ∀ y : N, y ∈ degGE 𝒩 c) {x : N} (hx : x ∈ I ^ m • (⊤ : Submodule A N)) :
    x ∈ degGE 𝒩 ((m : ℤ) + c) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    exact smul_mem_degGE_pow h𝒩 hIhom hI m ha (htop y)
  · intro u v hu hv
    exact (degGE 𝒩 _).add_mem hu hv

/-- **Graded Nakayama** [StacksProject 0EKB], in the form used to see that a compatible system of
lifts of generators generates: a homogeneous submodule `P` of a finite graded module `N` with
`P ⊔ I • N = N`, for a homogeneous `I ≤ 𝒜₊`, is `N`.

This is `Submodule.IsHomogeneous.le_of_le_smul_of_le_irrelevant` at `N' = ⊤`; the graded action
`h𝒩` is what supplies the `SetLike.GradedSMul 𝒜 𝒩` instance that lemma asks for. -/
private lemma eq_top_of_sup_smul_eq_top [Module.Finite A N]
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {P : Submodule A N}
    (hP : P.IsHomogeneous 𝒩) (hPI : P ⊔ I • (⊤ : Submodule A N) = ⊤) : P = ⊤ :=
  let _ : SetLike.GradedSMul 𝒜 𝒩 := ⟨fun {i d a x} ha hx => h𝒩 i d a x ha hx⟩
  le_antisymm le_top (hP.le_of_le_smul_of_le_irrelevant (fun _ _ _ => Submodule.mem_top)
    (Module.finite_def.mp ‹Module.Finite A N›) hI hPI.ge)


/-- The `d`-th homogeneous component of `a • x` for homogeneous `x` of degree `e`: only the
degree-`(d - e)` part of `a` contributes. -/
private lemma cpt_smul_of_mem {e d : ℤ} {x : N} (hx : x ∈ 𝒩 e) (a : A) :
    cpt 𝒩 d (a • x) = (if e ≤ d then cpt 𝒜 (d - e).toNat a else 0) • x := by
  have hterm : ∀ i ∈ (decompose 𝒜 a).support,
      cpt 𝒩 d (cpt 𝒜 i a • x) = if (i : ℤ) + e = d then cpt 𝒜 i a • x else 0 := by
    intro i _
    have hmem : cpt 𝒜 i a • x ∈ 𝒩 ((i : ℤ) + e) := h𝒩 i e _ _ (cpt_mem 𝒜 i a) hx
    by_cases h : (i : ℤ) + e = d
    · rw [ite_eq_left h]
      exact cpt_of_mem_same 𝒩 (h ▸ hmem)
    · rw [ite_eq_right h]
      exact cpt_of_mem_ne 𝒩 hmem h
  rw [smul_eq_sum_cpt_smul (𝒜 := 𝒜) a x, map_sum, Finset.sum_congr rfl hterm]
  by_cases hle : e ≤ d
  · rw [ite_eq_left hle]
    by_cases hmem : (d - e).toNat ∈ (decompose 𝒜 a).support
    · rw [Finset.sum_eq_single_of_mem _ hmem fun i _ hne => ite_eq_right (by omega),
        ite_eq_left (by omega)]
    · rw [Finset.sum_eq_zero, (cpt_eq_zero_iff_notMem_support 𝒜).2 hmem, zero_smul]
      intro i hi
      have hne : i ≠ (d - e).toNat := fun h => hmem (h ▸ hi)
      exact ite_eq_right (by omega)
  · rw [ite_eq_right hle, zero_smul, Finset.sum_eq_zero]
    intro i _
    exact ite_eq_right (by omega)

/-- An element of the span of a set living in degrees `≥ c` has no component in degree `< c`. -/
private lemma mem_degGE_of_mem_span {S : Set N} {c : ℤ} (hS : ∀ y ∈ S, y ∈ degGE 𝒩 c) {y : N}
    (hy : y ∈ Submodule.span A S) : y ∈ degGE 𝒩 c := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact hS z hz
  | zero => exact zero_mem _
  | add z w _ _ ihz ihw => exact add_mem ihz ihw
  | smul a z _ ihz => exact smul_mem_degGE h𝒩 a ihz

/-- A module generated by homogeneous elements of degrees `≥ δ` lives in degrees `≥ δ`. -/
private lemma forall_mem_degGE_of_span_range {ι : Type*} {x : ι → N} {dd : ι → ℤ} {δ : ℤ}
    (hx : ∀ i, x i ∈ 𝒩 (dd i)) (hδ : ∀ i, δ ≤ dd i)
    (hspan : Submodule.span A (Set.range x) = ⊤) (y : N) : y ∈ degGE 𝒩 δ :=
  mem_degGE_of_mem_span h𝒩 (S := Set.range x)
    (by rintro z ⟨i, rfl⟩; exact mem_degGE_of_mem_grade (hx i) (hδ i)) (by rw [hspan]; trivial)

/-- A submodule generated by finitely many homogeneous elements is homogeneous. -/
private lemma isHomogeneous_span_range {ι : Type*} [Finite ι] {x : ι → N} {dd : ι → ℤ}
    (hx : ∀ i, x i ∈ 𝒩 (dd i)) : (Submodule.span A (Set.range x)).IsHomogeneous 𝒩 := by
  have : Fintype ι := Fintype.ofFinite ι
  intro d y hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hy
  rw [← cpt_apply 𝒩 d y, ← hc, map_sum]
  refine sum_mem fun i _ => ?_
  rw [cpt_smul_of_mem h𝒩 (hx i)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Homogeneous coefficients: an element of degree `d` in the span of homogeneous elements `x i` of
degrees `dd i` is a combination `∑ b i • x i` in which each nonzero `b i` is homogeneous of
degree `d - dd i`. -/
private lemma exists_homogeneous_coeff_of_mem_span {ι : Type*} [Fintype ι] {x : ι → N}
    {dd : ι → ℤ} (hx : ∀ i, x i ∈ 𝒩 (dd i)) {d : ℤ} {y : N} (hy : y ∈ 𝒩 d)
    (hspan : y ∈ Submodule.span A (Set.range x)) :
    ∃ (b : ι → A) (j : ι → ℕ), (∀ i, b i ∈ 𝒜 (j i)) ∧
      (∀ i, (j i : ℤ) + dd i = d ∨ b i = 0) ∧ y = ∑ i, b i • x i := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hspan
  refine ⟨fun i => if dd i ≤ d then cpt 𝒜 (d - dd i).toNat (c i) else 0,
    fun i => (d - dd i).toNat, fun i => ?_, fun i => ?_, ?_⟩
  · change (if dd i ≤ d then cpt 𝒜 (d - dd i).toNat (c i) else 0) ∈ 𝒜 (d - dd i).toNat
    split
    · exact cpt_mem 𝒜 _ (c i)
    · exact zero_mem _
  · change ((d - dd i).toNat : ℤ) + dd i = d ∨ (if dd i ≤ d then _ else _) = 0
    by_cases h : dd i ≤ d
    · exact Or.inl (by omega)
    · exact Or.inr (ite_eq_right h)
  · rw [← cpt_of_mem_same 𝒩 hy, ← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => cpt_smul_of_mem h𝒩 (hx i) (c i)

/-- `J • ⊤` is a homogeneous submodule when the ideal `J` is homogeneous. -/
private lemma isHomogeneous_smul_top {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) :
    (J • (⊤ : Submodule A N)).IsHomogeneous 𝒩 := by
  intro d y hy
  rw [← cpt_apply 𝒩 d y]
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha z _
    rw [smul_eq_sum_smul_cpt 𝒩 a z, map_sum]
    refine sum_mem fun e _ => ?_
    rw [cpt_smul_of_mem h𝒩 (cpt_mem 𝒩 e z)]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    split
    · exact hJ _ ha
    · exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv

end GradedModule

/-! ### Degree-preserving maps -/

section Maps

variable {A : Type*} [CommRing A] {N N' : Type*} [AddCommGroup N] [Module A N]
  [AddCommGroup N'] [Module A N'] {𝒩 : ℤ → AddSubgroup N} [DirectSum.Decomposition 𝒩]
  {𝒩' : ℤ → AddSubgroup N'} [DirectSum.Decomposition 𝒩']

/-- A degree-preserving map commutes with taking homogeneous components. -/
private lemma cpt_comp (f : N →ₗ[A] N') (hf : ∀ (d : ℤ) (x : N), x ∈ 𝒩 d → f x ∈ 𝒩' d)
    (d : ℤ) (x : N) : cpt 𝒩' d (f x) = f (cpt 𝒩 d x) := by
  have hx : f x = ∑ e ∈ (decompose 𝒩 x).support, f (cpt 𝒩 e x) := by
    rw [← map_sum, sum_cpt]
  rw [hx, map_sum]
  by_cases hd : d ∈ (decompose 𝒩 x).support
  · rw [Finset.sum_eq_single_of_mem d hd
      fun e _ hne => cpt_of_mem_ne 𝒩' (hf e _ (cpt_mem 𝒩 e x)) hne]
    exact cpt_of_mem_same 𝒩' (hf d _ (cpt_mem 𝒩 d x))
  · rw [Finset.sum_eq_zero fun e he =>
      cpt_of_mem_ne 𝒩' (hf e _ (cpt_mem 𝒩 e x)) fun h => hd (by rw [← h]; exact he),
      (cpt_eq_zero_iff_notMem_support 𝒩).2 hd, map_zero]

/-- A degree-preserving surjection of graded modules is surjective in each degree. -/
private lemma exists_mem_grade_of_surjective (f : N →ₗ[A] N')
    (hf : ∀ (d : ℤ) (x : N), x ∈ 𝒩 d → f x ∈ 𝒩' d) (hsurj : Function.Surjective f)
    {d : ℤ} {y : N'} (hy : y ∈ 𝒩' d) : ∃ x ∈ 𝒩 d, f x = y := by
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨cpt 𝒩 d x, cpt_mem 𝒩 d x, ?_⟩
  rw [← cpt_comp f hf d x, hx, cpt_of_mem_same 𝒩' hy]

end Maps

/-! ### The graded limit -/

section Limit

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] {I : Ideal A} {N : ℕ → Type*} [∀ n, AddCommGroup (N n)]
  [∀ n, Module A (N n)] (𝒩 : ∀ n, ℤ → AddSubgroup (N n))
  [∀ n, DirectSum.Decomposition (𝒩 n)] (t : ∀ n, N (n + 1) →ₗ[A] N n)
  (h𝒩 : ∀ (n i : ℕ) (d : ℤ) (a : A) (x : N n), a ∈ 𝒜 i → x ∈ 𝒩 n d → a • x ∈ 𝒩 n (i + d))
  (ht : ∀ (n : ℕ) (d : ℤ) (x : N (n + 1)), x ∈ 𝒩 (n + 1) d → t n x ∈ 𝒩 n d)
  (htsurj : ∀ n, Function.Surjective (t n))
  (htker : ∀ n, LinearMap.ker (t n) = I ^ n • (⊤ : Submodule A (N (n + 1))))

/-- The compatible sequences that are homogeneous of degree `d` at every level: the degree-`d`
part of the graded limit of the system. -/
private def Lm (d : ℤ) : AddSubgroup (∀ n, N n) where
  carrier := {u | (∀ n, t n (u (n + 1)) = u n) ∧ ∀ n, u n ∈ 𝒩 n d}
  zero_mem' := ⟨fun n => map_zero _, fun n => zero_mem _⟩
  add_mem' := fun {u v} hu hv =>
    ⟨fun n => by simp only [Pi.add_apply, map_add, hu.1 n, hv.1 n],
      fun n => add_mem (hu.2 n) (hv.2 n)⟩
  neg_mem' := fun {u} hu =>
    ⟨fun n => by simp only [Pi.neg_apply, map_neg, hu.1 n], fun n => neg_mem (hu.2 n)⟩

omit [AddSubmonoidClass σ A] [GradedRing 𝒜] [∀ n, DirectSum.Decomposition (𝒩 n)] in
include h𝒩 in
private lemma smul_mem_Lm {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) {d : ℤ} {u : ∀ n, N n}
    (hu : u ∈ Lm 𝒩 t d) : a • u ∈ Lm 𝒩 t ((i : ℤ) + d) :=
  ⟨fun n => by simp only [Pi.smul_apply, map_smul, hu.1 n], fun n => h𝒩 n i d a _ ha (hu.2 n)⟩

omit [AddSubmonoidClass σ A] [GradedRing 𝒜] [∀ n, DirectSum.Decomposition (𝒩 n)] in
include h𝒩 in
/-- The version of `smul_mem_Lm` that a homogeneous expansion produces: the coefficient either has
the complementary degree or vanishes. -/
private lemma smul_mem_Lm' {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) {e d : ℤ} {u : ∀ n, N n}
    (hu : u ∈ Lm 𝒩 t e) (h : (i : ℤ) + e = d ∨ a = 0) : a • u ∈ Lm 𝒩 t d := by
  rcases h with h | rfl
  · exact h ▸ smul_mem_Lm 𝒩 t h𝒩 ha hu
  · rw [zero_smul]
    exact zero_mem _

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
include h𝒩 in
private lemma smul_mem_iSup_Lm (a : A) {u : ∀ n, N n} (hu : u ∈ ⨆ d, Lm 𝒩 t d) :
    a • u ∈ ⨆ d, Lm 𝒩 t d := by
  refine AddSubgroup.iSup_induction (C := fun v => a • v ∈ ⨆ d, Lm 𝒩 t d) _ hu ?_ ?_ ?_
  · intro d v hv
    rw [smul_eq_sum_cpt_smul (𝒜 := 𝒜) a v]
    exact sum_mem fun i _ =>
      AddSubgroup.mem_iSup_of_mem _ (smul_mem_Lm 𝒩 t h𝒩 (cpt_mem 𝒜 i a) hv)
  · rw [smul_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [smul_add]
    exact add_mem hu hv

/-- The graded limit of the system: the `A`-submodule of `∀ n, N n` generated by the compatible
sequences that are homogeneous at every level. -/
private def gradedLimit : Submodule A (∀ n, N n) where
  __ := (⨆ d, Lm 𝒩 t d).toAddSubmonoid
  smul_mem' := fun a _ hu => smul_mem_iSup_Lm 𝒩 t h𝒩 a hu

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
private lemma mem_gradedLimit_iff {u : ∀ n, N n} :
    u ∈ gradedLimit 𝒩 t h𝒩 ↔ u ∈ ⨆ d, Lm 𝒩 t d := Iff.rfl

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
private lemma mem_gradedLimit_of_mem_Lm {d : ℤ} {u : ∀ n, N n} (hu : u ∈ Lm 𝒩 t d) :
    u ∈ gradedLimit 𝒩 t h𝒩 := AddSubgroup.mem_iSup_of_mem d hu

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
private lemma compat_of_mem_gradedLimit {u : ∀ n, N n} (hu : u ∈ gradedLimit 𝒩 t h𝒩) (n : ℕ) :
    t n (u (n + 1)) = u n := by
  refine AddSubgroup.iSup_induction (C := fun v => ∀ n, t n (v (n + 1)) = v n) _
    ((mem_gradedLimit_iff 𝒩 t h𝒩).mp hu) (fun d v hv => hv.1) (fun n => map_zero _)
    (fun v w hv hw n => ?_) n
  simp only [Pi.add_apply, map_add, hv n, hw n]

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
/-- Every element of the graded limit is a finite sum of homogeneous ones. -/
private lemma exists_finset_sum_eq_of_mem_gradedLimit {u : ∀ n, N n}
    (hu : u ∈ gradedLimit 𝒩 t h𝒩) :
    ∃ (s : Finset ℤ) (g : ℤ → ∀ n, N n), (∀ d, g d ∈ Lm 𝒩 t d) ∧ (∀ d ∉ s, g d = 0) ∧
      u = ∑ d ∈ s, g d := by
  classical
  refine AddSubgroup.iSup_induction
    (C := fun v => ∃ (s : Finset ℤ) (g : ℤ → ∀ n, N n), (∀ d, g d ∈ Lm 𝒩 t d) ∧
      (∀ d ∉ s, g d = 0) ∧ v = ∑ d ∈ s, g d) _ ((mem_gradedLimit_iff 𝒩 t h𝒩).mp hu) ?_ ?_ ?_
  · intro d v hv
    refine ⟨{d}, fun e => if e = d then v else 0, fun e => ?_, fun e he => ?_, by simp⟩
    · change (if e = d then v else 0) ∈ Lm 𝒩 t e
      split
      · next h => rw [h]; exact hv
      · exact zero_mem _
    · change (if e = d then v else 0) = 0
      exact ite_eq_right (by simpa using he)
  · exact ⟨∅, 0, fun d => zero_mem _, fun d _ => rfl, by simp⟩
  · intro u₁ u₂ h₁ h₂
    obtain ⟨s₁, g₁, hg₁, hgs₁, rfl⟩ := h₁
    obtain ⟨s₂, g₂, hg₂, hgs₂, rfl⟩ := h₂
    refine ⟨s₁ ∪ s₂, g₁ + g₂, fun d => add_mem (hg₁ d) (hg₂ d), fun d hd => ?_, ?_⟩
    · change g₁ d + g₂ d = 0
      rw [hgs₁ d fun h => hd (Finset.mem_union_left _ h),
        hgs₂ d fun h => hd (Finset.mem_union_right _ h), add_zero]
    · rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s₂)) (fun d _ hd => hgs₁ d hd),
        Finset.sum_subset (Finset.subset_union_right (s₁ := s₁)) (fun d _ hd => hgs₂ d hd),
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => rfl

/-- The degree-`d` part of a sequence, taken level by level. -/
private noncomputable def prj (d : ℤ) (u : ∀ n, N n) : ∀ n, N n := fun n => cpt (𝒩 n) d (u n)

include ht in
private lemma prj_mem_Lm (d : ℤ) {u : ∀ n, N n} (hu : ∀ n, t n (u (n + 1)) = u n) :
    prj 𝒩 d u ∈ Lm 𝒩 t d := by
  refine ⟨fun n => ?_, fun n => cpt_mem (𝒩 n) d (u n)⟩
  change t n (cpt (𝒩 (n + 1)) d (u (n + 1))) = cpt (𝒩 n) d (u n)
  rw [← cpt_comp (t n) (ht n) d (u (n + 1)), hu n]

private lemma prj_eq_self_of_mem_Lm {d : ℤ} {u : ∀ n, N n} (hu : u ∈ Lm 𝒩 t d) :
    prj 𝒩 d u = u :=
  funext fun n => cpt_of_mem_same (𝒩 n) (hu.2 n)

private lemma prj_eq_zero_of_mem_Lm {d e : ℤ} (h : d ≠ e) {u : ∀ n, N n}
    (hu : u ∈ Lm 𝒩 t d) : prj 𝒩 e u = 0 :=
  funext fun n => cpt_of_mem_ne (𝒩 n) (hu.2 n) h

/-- The degree-`d` part of the graded limit. -/
private def gradedLimitGrading (d : ℤ) : AddSubgroup (gradedLimit 𝒩 t h𝒩) :=
  (Lm 𝒩 t d).comap (gradedLimit 𝒩 t h𝒩).subtype.toAddMonoidHom

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
private lemma mem_gradedLimitGrading_iff {d : ℤ} {x : gradedLimit 𝒩 t h𝒩} :
    x ∈ gradedLimitGrading 𝒩 t h𝒩 d ↔ (x : ∀ n, N n) ∈ Lm 𝒩 t d := Iff.rfl

include ht in
/-- The projection of the graded limit onto its degree-`d` part. -/
private noncomputable def gradedLimitPrj (d : ℤ) : gradedLimit 𝒩 t h𝒩 →+ gradedLimit 𝒩 t h𝒩 where
  toFun x := ⟨prj 𝒩 d x, mem_gradedLimit_of_mem_Lm 𝒩 t h𝒩
    (prj_mem_Lm 𝒩 t ht d (compat_of_mem_gradedLimit 𝒩 t h𝒩 x.2))⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (cpt (𝒩 n) d))
  map_add' _ _ := Subtype.ext (funext fun n => map_add (cpt (𝒩 n) d) _ _)

include ht in
private lemma gradedLimitPrj_coeAddMonoidHom (e : ℤ)
    (y : ⨁ d, gradedLimitGrading 𝒩 t h𝒩 d) :
    gradedLimitPrj 𝒩 t h𝒩 ht e (DirectSum.coeAddMonoidHom (gradedLimitGrading 𝒩 t h𝒩) y)
      = (y e : gradedLimit 𝒩 t h𝒩) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of d z =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : e = d
    · subst h
      rw [DirectSum.of_eq_same]
      exact Subtype.ext (prj_eq_self_of_mem_Lm 𝒩 t z.2)
    · rw [DirectSum.of_eq_of_ne (β := fun d => (gradedLimitGrading 𝒩 t h𝒩 d : Type _)) d e z h,
        ZeroMemClass.coe_zero]
      exact Subtype.ext (prj_eq_zero_of_mem_Lm 𝒩 t (fun h' => h h'.symm) z.2)
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv]
    simp

include ht in
private lemma isInternal_gradedLimitGrading :
    DirectSum.IsInternal (gradedLimitGrading 𝒩 t h𝒩) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => DFinsupp.ext fun e => ?_, fun x => ?_⟩
  · have key := gradedLimitPrj_coeAddMonoidHom 𝒩 t h𝒩 ht e y
    rw [hy, map_zero] at key
    exact ZeroMemClass.coe_eq_zero.mp key.symm
  · obtain ⟨s, g, hg, hgs, hxs⟩ := exists_finset_sum_eq_of_mem_gradedLimit 𝒩 t h𝒩 x.2
    refine ⟨∑ d ∈ s, DirectSum.of _ d
      ⟨⟨g d, mem_gradedLimit_of_mem_Lm 𝒩 t h𝒩 (hg d)⟩, hg d⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact Subtype.ext (by rw [AddSubmonoidClass.coe_finsetSum]; exact hxs.symm)

include ht in
/-- The graded limit is an internally graded module. -/
@[instance_reducible] private noncomputable def gradedLimitDecomposition :
    DirectSum.Decomposition (gradedLimitGrading 𝒩 t h𝒩) :=
  DirectSum.IsInternal.chooseDecomposition _ (isInternal_gradedLimitGrading 𝒩 t h𝒩 ht)

include ht htsurj in
/-- A homogeneous element of `N 1` is the value at level `1` of a compatible sequence that is
homogeneous of the same degree at every level. -/
private lemma exists_mem_Lm_apply_one_eq {d : ℤ} {z : N 1} (hz : z ∈ 𝒩 1 d) :
    ∃ u ∈ Lm 𝒩 t d, u 1 = z := by
  classical
  choose! W hW1 hW2 using fun (n : ℕ) (y : N (n + 1)) (hy : y ∈ 𝒩 (n + 1) d) =>
    exists_mem_grade_of_surjective (t (n + 1)) (ht (n + 1)) (htsurj (n + 1)) hy
  let F : ∀ n : ℕ, {y : N (n + 1) // y ∈ 𝒩 (n + 1) d} :=
    fun n => Nat.rec ⟨z, hz⟩ (fun m y => ⟨W m y.1, hW1 m y.1 y.2⟩) n
  have hFc : ∀ n, t (n + 1) (F (n + 1)).1 = (F n).1 := fun n => hW2 n (F n).1 (F n).2
  refine ⟨fun n => Nat.casesOn n (t 0 (F 0).1) fun m => (F m).1, ⟨fun n => ?_, fun n => ?_⟩, rfl⟩
  · cases n with
    | zero => rfl
    | succ m => exact hFc m
  · cases n with
    | zero => exact ht 0 d (F 0).1 (F 0).2
    | succ m => exact (F m).2

include h𝒩 htsurj htker in
/-- **Graded Nakayama** for the system [StacksProject 0EKB]: a compatible system of lifts of
homogeneous generators of `N 1` generates every `N n`. -/
private lemma span_range_eq_top [∀ n, Module.Finite A (N n)]
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {ι : Type*} [Finite ι] {dd : ι → ℤ}
    {X : ι → ∀ n, N n} (hX : ∀ i, X i ∈ Lm 𝒩 t (dd i))
    (h1 : Submodule.span A (Set.range fun i => X i 1) = ⊤) (n : ℕ) :
    Submodule.span A (Set.range fun i => X i n) = ⊤ := by
  have key : ∀ m : ℕ, Submodule.span A (Set.range fun i => X i (m + 1)) = ⊤ := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>
      have himg : (t (m + 1)) '' (Set.range fun i => X i (m + 1 + 1))
          = Set.range fun i => X i (m + 1) := by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun i => (hX i).1 (m + 1))
      have hmap : Submodule.map (t (m + 1))
          (Submodule.span A (Set.range fun i => X i (m + 1 + 1))) = ⊤ := by
        rw [Submodule.map_span, himg, ih]
      have hsup : Submodule.span A (Set.range fun i => X i (m + 1 + 1))
          ⊔ I ^ (m + 1) • (⊤ : Submodule A (N (m + 1 + 1))) = ⊤ := by
        rw [← htker (m + 1), ← Submodule.comap_map_eq, hmap, Submodule.comap_top]
      refine eq_top_of_sup_smul_eq_top (h𝒩 (m + 1 + 1)) hI
        (isHomogeneous_span_range (h𝒩 (m + 1 + 1)) (fun i => (hX i).2 (m + 1 + 1)))
        (le_antisymm le_top ?_)
      refine hsup.symm.trans_le (sup_le_sup_left ?_ _)
      exact Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero m))
  cases n with
  | zero =>
    refine Submodule.eq_top_iff'.2 fun y => ?_
    obtain ⟨w, hw⟩ := htsurj 0 y
    have hker : w ∈ LinearMap.ker (t 0) := by rw [htker 0]; simp
    rw [← hw, LinearMap.mem_ker.mp hker]
    exact zero_mem _
  | succ m => exact key m

include h𝒩 htsurj htker in
/-- Rigidity: a compatible sequence that is homogeneous of degree `d` at every level and vanishes
at level `m`, with `d < δ + m`, vanishes identically. -/
private lemma eq_zero_of_mem_Lm (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {δ : ℤ}
    (hδ : ∀ (n : ℕ) (y : N n), y ∈ degGE (𝒩 n) δ) {d : ℤ} {u : ∀ n, N n}
    (hu : u ∈ Lm 𝒩 t d) {m : ℕ} (hm : d < δ + m) (h0 : u m = 0) : u = 0 := by
  funext n
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    exact eq_zero_of_later_eq_zero t hu.1 k h0
  · obtain ⟨k, rfl⟩ := Nat.le.dest h
    have hmem := mem_pow_smul_top_of_eq_zero t htsurj htker hu.1 h0 k
    have hzero := pow_smul_top_le_degGE (h𝒩 (m + k)) hIhom hI m (hδ (m + k)) hmem d (by omega)
    rw [← cpt_of_mem_same (𝒩 (m + k)) (hu.2 (m + k))]
    exact hzero

include h𝒩 htsurj htker in
/-- A homogeneous element of the graded limit is a combination of the lifts `Xel`.  This is where
the stabilisation of the system is used: at a level `m` so deep that `d < δ + m` the value in
degree `d` is a combination of the `X i` with homogeneous coefficients, and rigidity
(`eq_zero_of_mem_Lm`) promotes that agreement at level `m` to an identity of sequences. -/
private lemma mem_span_range_of_mem_Lm (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {δ : ℤ}
    (hδ : ∀ (n : ℕ) (y : N n), y ∈ degGE (𝒩 n) δ) {ι : Type*} [Finite ι] {dd : ι → ℤ}
    {X : ι → ∀ n, N n} (hX : ∀ i, X i ∈ Lm 𝒩 t (dd i))
    (hgen : ∀ n, Submodule.span A (Set.range fun i => X i n) = ⊤)
    (Xel : ι → gradedLimit 𝒩 t h𝒩) (hXel : ∀ i, (Xel i : ∀ n, N n) = X i)
    {d : ℤ} {v : ∀ n, N n} (hv : v ∈ Lm 𝒩 t d) :
    (⟨v, mem_gradedLimit_of_mem_Lm 𝒩 t h𝒩 hv⟩ : gradedLimit 𝒩 t h𝒩) ∈
      Submodule.span A (Set.range Xel) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d < δ + m := ⟨(d - δ).toNat + 1, by push_cast; omega⟩
  obtain ⟨b, j, hb, hbj, hbv⟩ := exists_homogeneous_coeff_of_mem_span (h𝒩 m)
    (fun i => (hX i).2 m) (hv.2 m) (by rw [hgen m]; trivial)
  have hv' : v = ∑ i, b i • X i := by
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_Lm 𝒩 t h𝒩 htsurj htker hIhom hI hδ (d := d)
      (sub_mem hv (sum_mem fun i _ => smul_mem_Lm' 𝒩 t h𝒩 (hb i) (hX i) (hbj i))) hm ?_
    change (v - ∑ i, b i • X i) m = 0
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, sub_eq_zero]
    exact hbv
  rw [show (⟨v, mem_gradedLimit_of_mem_Lm 𝒩 t h𝒩 hv⟩ : gradedLimit 𝒩 t h𝒩) = ∑ i, b i • Xel i from
    Subtype.ext (by
      rw [AddSubmonoidClass.coe_finsetSum]
      simpa only [SetLike.val_smul, hXel] using hv')]
  exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

include h𝒩 htsurj htker in
/-- The graded limit is generated by the compatible systems of lifts of generators of `N 1`:
decompose into homogeneous parts and apply `mem_span_range_of_mem_Lm` to each. -/
private lemma mem_span_range_of_mem_gradedLimit (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {δ : ℤ}
    (hδ : ∀ (n : ℕ) (y : N n), y ∈ degGE (𝒩 n) δ) {ι : Type*} [Finite ι] {dd : ι → ℤ}
    {X : ι → ∀ n, N n} (hX : ∀ i, X i ∈ Lm 𝒩 t (dd i))
    (hgen : ∀ n, Submodule.span A (Set.range fun i => X i n) = ⊤)
    (Xel : ι → gradedLimit 𝒩 t h𝒩) (hXel : ∀ i, (Xel i : ∀ n, N n) = X i)
    (w : gradedLimit 𝒩 t h𝒩) : w ∈ Submodule.span A (Set.range Xel) := by
  obtain ⟨s, g, hg, -, hws⟩ := exists_finset_sum_eq_of_mem_gradedLimit 𝒩 t h𝒩 w.2
  rw [show w = ∑ d ∈ s, (⟨g d, mem_gradedLimit_of_mem_Lm 𝒩 t h𝒩 (hg d)⟩ : gradedLimit 𝒩 t h𝒩) from
    Subtype.ext (by rw [AddSubmonoidClass.coe_finsetSum]; exact hws)]
  exact sum_mem fun d _ =>
    mem_span_range_of_mem_Lm 𝒩 t h𝒩 htsurj htker hIhom hI hδ hX hgen Xel hXel (hg d)

/-- Taking the degree-`d` homogeneous component of an element of the graded limit commutes with
evaluation at level `m`: the decomposition of the graded limit is computed level by level.  Indeed
evaluation at level `m` is a degree-preserving linear map, so `cpt_comp` applies. -/
private lemma coe_cpt_apply [DirectSum.Decomposition (gradedLimitGrading 𝒩 t h𝒩)] (d : ℤ) (m : ℕ)
    (x : gradedLimit 𝒩 t h𝒩) :
    ((cpt (gradedLimitGrading 𝒩 t h𝒩) d x : gradedLimit 𝒩 t h𝒩) : ∀ k, N k) m
      = cpt (𝒩 m) d ((x : ∀ k, N k) m) :=
  (cpt_comp ((LinearMap.proj m).comp (gradedLimit 𝒩 t h𝒩).subtype)
    (fun _ _ hy => ((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hy).2 m) d x).symm

omit [∀ n, DirectSum.Decomposition (𝒩 n)] in
/-- Evaluation of the graded limit at level `m` is surjective: it carries a compatible system of
lifts of generators to a generating set of `Nₘ`. -/
private lemma surjective_apply {ι : Type*} [Finite ι] {X : ι → ∀ n, N n}
    (hgen : ∀ n, Submodule.span A (Set.range fun i => X i n) = ⊤)
    (Xel : ι → gradedLimit 𝒩 t h𝒩) (hXel : ∀ i, (Xel i : ∀ n, N n) = X i) (m : ℕ) :
    Function.Surjective fun (y : gradedLimit 𝒩 t h𝒩) => (y : ∀ k, N k) m := by
  have : Fintype ι := Fintype.ofFinite ι
  intro y
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp
    (show y ∈ Submodule.span A (Set.range fun i => X i m) by rw [hgen m]; trivial)
  refine ⟨∑ i, c i • Xel i, ?_⟩
  change ((∑ i, c i • Xel i : gradedLimit 𝒩 t h𝒩) : ∀ k, N k) m = y
  rw [AddSubmonoidClass.coe_finsetSum, ← hc, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [SetLike.val_smul, hXel i, Pi.smul_apply]

include h𝒩 htsurj htker in
/-- The homogeneous case of `mem_pow_smul_top_of_apply_eq_zero`, and the whole of its content: a
homogeneous element `v` of the graded limit that vanishes at level `n` agrees, at a level `n + k`
deep enough that `d < δ + (n + k)`, with the degree-`d` part `u'` of an element of
`Iⁿ · gradedLimit`, and rigidity (`eq_zero_of_mem_Lm`) then forces `v = u'`. -/
private lemma mem_pow_smul_top_of_mem_gradedLimitGrading
    [DirectSum.Decomposition (gradedLimitGrading 𝒩 t h𝒩)] (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {δ : ℤ}
    (hδ : ∀ (n : ℕ) (y : N n), y ∈ degGE (𝒩 n) δ) {ι : Type*} [Finite ι]
    {X : ι → ∀ n, N n}
    (hgen : ∀ n, Submodule.span A (Set.range fun i => X i n) = ⊤)
    (Xel : ι → gradedLimit 𝒩 t h𝒩) (hXel : ∀ i, (Xel i : ∀ n, N n) = X i)
    {n : ℕ} {d : ℤ} {v : gradedLimit 𝒩 t h𝒩} (hv : v ∈ gradedLimitGrading 𝒩 t h𝒩 d)
    (hv0 : (v : ∀ k, N k) n = 0) : v ∈ I ^ n • (⊤ : Submodule A (gradedLimit 𝒩 t h𝒩)) := by
  have hsurj := surjective_apply 𝒩 t h𝒩 hgen Xel hXel
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d < δ + (n + k : ℕ) := ⟨(d - δ).toNat + 1, by push_cast; omega⟩
  have h1 : (v : ∀ k, N k) (n + k) ∈ I ^ n • (⊤ : Submodule A (N (n + k))) :=
    mem_pow_smul_top_of_eq_zero t htsurj htker
      (compat_of_mem_gradedLimit 𝒩 t h𝒩 v.2) hv0 k
  obtain ⟨u, hu, hu2⟩ : ∃ u ∈ I ^ n • (⊤ : Submodule A (gradedLimit 𝒩 t h𝒩)),
      (u : ∀ k, N k) (n + k) = (v : ∀ k, N k) (n + k) :=
    (map_smul_top (I ^ n) ((LinearMap.proj (n + k)).comp (gradedLimit 𝒩 t h𝒩).subtype)
      (hsurj (n + k))).ge h1
  set u' := cpt (gradedLimitGrading 𝒩 t h𝒩) d u with hu'def
  have hu'grade : u' ∈ gradedLimitGrading 𝒩 t h𝒩 d := cpt_mem _ d u
  have hu'val : (u' : ∀ k, N k) (n + k) = (v : ∀ k, N k) (n + k) := by
    rw [hu'def, coe_cpt_apply 𝒩 t h𝒩 d (n + k) u, hu2,
      cpt_of_mem_same (𝒩 (n + k)) (((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hv).2 (n + k))]
  have hvu' : v = u' := by
    rw [← sub_eq_zero]
    refine Subtype.ext (eq_zero_of_mem_Lm 𝒩 t h𝒩 htsurj htker hIhom hI hδ (d := d) (m := n + k)
      (sub_mem ((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hv)
        ((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hu'grade)) hk ?_)
    change (v : ∀ k, N k) (n + k) - (u' : ∀ k, N k) (n + k) = 0
    rw [hu'val, sub_self]
  rw [hvu']
  exact isHomogeneous_smul_top (fun i e a x ha hx => (mem_gradedLimitGrading_iff 𝒩 t h𝒩).2
    (smul_mem_Lm 𝒩 t h𝒩 ha ((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hx)))
    (isHomogeneous_pow hIhom n) d hu

include h𝒩 ht htsurj htker in
/-- The kernel of the map to level `n` is `Iⁿ` times the graded limit: decompose into homogeneous
parts, each of which still vanishes at level `n`, and apply
`mem_pow_smul_top_of_mem_gradedLimitGrading`. -/
private lemma mem_pow_smul_top_of_apply_eq_zero (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) {δ : ℤ}
    (hδ : ∀ (n : ℕ) (y : N n), y ∈ degGE (𝒩 n) δ) {ι : Type*} [Finite ι]
    {X : ι → ∀ n, N n}
    (hgen : ∀ n, Submodule.span A (Set.range fun i => X i n) = ⊤)
    (Xel : ι → gradedLimit 𝒩 t h𝒩) (hXel : ∀ i, (Xel i : ∀ n, N n) = X i)
    {n : ℕ} {w : gradedLimit 𝒩 t h𝒩} (hw : (w : ∀ k, N k) n = 0) :
    w ∈ I ^ n • (⊤ : Submodule A (gradedLimit 𝒩 t h𝒩)) := by
  let _inst := gradedLimitDecomposition 𝒩 t h𝒩 ht
  rw [← sum_cpt (gradedLimitGrading 𝒩 t h𝒩) w]
  refine sum_mem fun d _ => mem_pow_smul_top_of_mem_gradedLimitGrading 𝒩 t h𝒩 htsurj htker
    hIhom hI hδ hgen Xel hXel (cpt_mem _ d w) ?_
  rw [coe_cpt_apply 𝒩 t h𝒩 d n w, hw, map_zero]

end Limit

end GradedInverseSystem

namespace Ideal.IsHomogeneous

open GradedInverseSystem in
/-- **Stacks 0EKC**. Let `A = ⨁_{i ≥ 0} 𝒜 i` be a graded ring, let `I ⊆ 𝒜₊ = ⨁_{i > 0} 𝒜 i` be a
homogeneous ideal, and let `(Nₙ)` be an inverse system of finite graded `A`-modules whose
transition maps `t n : N_{n+1} → Nₙ` are graded and exhibit `Nₙ = N_{n+1}/Iⁿ N_{n+1}`. Then there
is a finite graded `A`-module `M` and a compatible system of graded surjections `f n : M → Nₙ`
with `ker (f n) = Iⁿ M`, i.e. `Nₙ = M/Iⁿ M` as graded modules for all `n`.

The source assumes `A` Noetherian; the argument uses only that each `Nₙ` is a finite `A`-module,
so that hypothesis is omitted. -/
@[stacks 0EKC]
public theorem exists_finite_graded_forall_ker_eq_pow_smul_top
    {A : Type u} {σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {I : Ideal A} (hIhom : I.IsHomogeneous 𝒜)
    (hI : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    {N : ℕ → Type v} [∀ n, AddCommGroup (N n)] [∀ n, Module A (N n)]
    [∀ n, Module.Finite A (N n)]
    (𝒩 : ∀ n, ℤ → AddSubgroup (N n)) [∀ n, DirectSum.Decomposition (𝒩 n)]
    (h𝒩 : ∀ (n i : ℕ) (d : ℤ) (a : A) (x : N n), a ∈ 𝒜 i → x ∈ 𝒩 n d → a • x ∈ 𝒩 n (i + d))
    (t : ∀ n, N (n + 1) →ₗ[A] N n)
    (ht : ∀ (n : ℕ) (d : ℤ) (x : N (n + 1)), x ∈ 𝒩 (n + 1) d → t n x ∈ 𝒩 n d)
    (htsurj : ∀ n, Function.Surjective (t n))
    (htker : ∀ n, LinearMap.ker (t n) = I ^ n • (⊤ : Submodule A (N (n + 1)))) :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module A M) (ℳ : ℤ → AddSubgroup M)
        (_ : DirectSum.Decomposition ℳ) (f : ∀ n, M →ₗ[A] N n),
      Module.Finite A M ∧
      (∀ (i : ℕ) (d : ℤ) (a : A) (x : M), a ∈ 𝒜 i → x ∈ ℳ d → a • x ∈ ℳ (i + d)) ∧
      (∀ (n : ℕ) (d : ℤ) (x : M), x ∈ ℳ d → f n x ∈ 𝒩 n d) ∧
      (∀ n, Function.Surjective (f n)) ∧
      (∀ n, LinearMap.ker (f n) = I ^ n • (⊤ : Submodule A M)) ∧
      (∀ n, (t n).comp (f (n + 1)) = f n) := by
  -- A finite homogeneous generating set of `N 1`, reindexed by `↥T` and lifted to compatible
  -- systems.
  obtain ⟨T, hT, hspanT⟩ := Module.Finite.exists_finset_homogeneous_span_eq_top (A := A) (𝒩 1)
  rw [Set.image_eq_range] at hspanT
  choose X hXmem hX1 using fun (p : {q : ℤ × N 1 // q ∈ T}) =>
    exists_mem_Lm_apply_one_eq 𝒩 t ht htsurj (hT p.1 p.2)
  -- Graded Nakayama: the lifts generate every level, in the degrees of the generators.
  have hgen := span_range_eq_top 𝒩 t h𝒩 htsurj htker hI
    (dd := fun p : {q : ℤ × N 1 // q ∈ T} => (p.1).1) hXmem
    (by rw [← hspanT]; exact congrArg (Submodule.span A) (congrArg Set.range (funext hX1)))
  -- A lower bound on the degrees of the generators bounds the degrees of every level.
  obtain ⟨δ, hddδ⟩ := (Set.finite_range fun p : {q : ℤ × N 1 // q ∈ T} => (p.1).1).bddBelow
  have hδ : ∀ (n : ℕ) (y : N n), y ∈ degGE (𝒩 n) δ := fun n =>
    forall_mem_degGE_of_span_range (h𝒩 n) (fun p => (hXmem p).2 n)
      (fun p => hddδ ⟨p, rfl⟩) (hgen n)
  -- The graded limit, and the elements of it that the lifts assemble into.
  set Xel : {q : ℤ × N 1 // q ∈ T} → gradedLimit 𝒩 t h𝒩 :=
    fun p => ⟨X p, mem_gradedLimit_of_mem_Lm 𝒩 t h𝒩 (hXmem p)⟩
  have hXel : ∀ p, (Xel p : ∀ n, N n) = X p := fun p => rfl
  have hspanXel : Submodule.span A (Set.range Xel) = ⊤ :=
    Submodule.eq_top_iff'.2 fun w =>
      mem_span_range_of_mem_gradedLimit 𝒩 t h𝒩 htsurj htker hIhom hI hδ hXmem hgen Xel hXel w
  have hsurjf := surjective_apply 𝒩 t h𝒩 hgen Xel hXel
  refine ⟨↥(gradedLimit 𝒩 t h𝒩), inferInstance, inferInstance, gradedLimitGrading 𝒩 t h𝒩,
    gradedLimitDecomposition 𝒩 t h𝒩 ht,
    fun n => (LinearMap.proj n).comp (gradedLimit 𝒩 t h𝒩).subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Module.finite_def.2 (Submodule.fg_def.2 ⟨_, Set.finite_range Xel, hspanXel⟩)
  · intro i d a x ha hx
    exact (mem_gradedLimitGrading_iff 𝒩 t h𝒩).2
      (smul_mem_Lm 𝒩 t h𝒩 ha ((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hx))
  · exact fun n d x hx => ((mem_gradedLimitGrading_iff 𝒩 t h𝒩).1 hx).2 n
  · exact hsurjf
  · intro n
    refine le_antisymm ?_ ?_
    · intro w hw
      exact mem_pow_smul_top_of_apply_eq_zero 𝒩 t h𝒩 ht htsurj htker hIhom hI hδ hgen
        Xel hXel (LinearMap.mem_ker.mp hw)
    · exact smul_top_le_ker _ _ (pow_smul_top_eq_bot t htsurj htker n)
  · exact fun n => LinearMap.ext fun w => compat_of_mem_gradedLimit 𝒩 t h𝒩 w.2 n

end Ideal.IsHomogeneous

end
