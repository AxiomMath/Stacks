module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksFrontier.Algebra.DirectSum.GradedQuotient
public import StacksFrontier.RingTheory.AdicCompletion.LadderStableImage

/-!
# The reindexed stable images are a graded adic tower

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a graded ring and `I` a homogeneous ideal. Let `(H_j)` be an inverse
system of `ℤ`-graded `A`-modules with degree-preserving transitions and `I^{j+1} H_j = 0`, and
suppose `(H_j)` is pro-isomorphic to an adic tower `(W_j)` of finite `A`-modules — the situation
of [Stacks, Tag 0EL4], where `H_j` is the module of sections on `U = Spec(A) ∖ V(𝔞)` of the
coherent formal module and `(W_j)` is the canonical extension.

This file builds from that data the graded inverse system that the graded limit theorem of
[Stacks, Tag 0EKC] consumes. Its `k`-th term is

`N_k = H_{nn k} ⧸ (I^k H_{nn k} + ker(H_{nn k} → H_{mm k}))`,

a quotient of `H_{nn k}` by a homogeneous submodule — hence a graded module — which is the stable
image `P_{mm k}` modulo `I^k P_{mm k}`. The two reindexings are chosen so that the image of
`H_{nn k} → H_{mm k}` is already the stable image and so that the adic quotients of the stable
images have stabilized by level `mm k`. The transition maps are then degree-preserving
surjections whose kernel is *exactly* `I^k`, which is what Tag 0EKC asks for and what the source
obtains instead from the `𝐆ₘ`-equivariant structure on the canonical extension.

## Main definitions

* `Stacks.ProObject.stabIndex` and `Stacks.ProObject.coverIndex` — the two reindexings.
* `Stacks.ProObject.LadderData.stableQuotKer` — the homogeneous submodule by which `N_k` is the
  quotient.
* `Stacks.ProObject.LadderData.stableQuotTr` — the transition map `N_{k+1} → N_k`.
* `Stacks.ProObject.LadderData.stableQuotSystem` — the tower as an `ℕᵒᵖ`-indexed inverse system,
  shifted so that the kernel of its one-step transition at level `k` is `I^{k+1}`.
* `Stacks.ProObject.LadderData.stableQuotDown` — level `k + 1` of the tower mapping to level `k`
  of `H`.

## Main results

* `Stacks.ProObject.LadderData.isHomogeneous_stableQuotKer` — the submodule is homogeneous, so
  `N_k` is graded; `Stacks.ProObject.LadderData.stableQuotPiece` is the grading and
  `Stacks.ProObject.LadderData.stableQuotDecomposition` its decomposition, with
  `Stacks.ProObject.LadderData.stableQuotTr_mem_stableQuotPiece` and
  `Stacks.ProObject.LadderData.stableQuotDown_mem` the degree preservation of the two families of
  maps out of it.
* `Stacks.ProObject.LadderData.finite_stableQuot` — `N_k` is a finite `A`-module.
* `Stacks.ProObject.LadderData.surjective_stableQuotTr`,
  `Stacks.ProObject.LadderData.ker_stableQuotTr`,
  `Stacks.ProObject.LadderData.isAdicTower_stableQuotSystem` — **the transitions are surjective
  with kernel exactly `I^k`**: the system is an adic tower.
* `Stacks.ProObject.LadderData.stableQuotLadderData` and
  `Stacks.ProObject.LadderData.hasProLadder_stableQuotSystem` — **the tower is linked to `H` by a
  ladder**, both composites being transition maps on the nose, so the two have the same inverse
  limit.

## Implementation notes

The reindexings are top-level recursive definitions, not choices made inside a proof, so that
their monotonicity and the inequalities relating them are available as lemmas. `stabIndex` is
fast enough that the adic quotients have stabilized by it and that `k ≤ stabIndex k`;
`coverIndex` is fast enough that the image of a transition map into level `stabIndex k` is already
the stable image.

## References

* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0EKC](https://stacks.math.columbia.edu/tag/0EKC)
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace Stacks.ProObject

/-! ### The reindexings -/

/-- The reindexing of the stable images: fast enough that the adic quotients at level `k` have
stabilized by `stabIndex m₀ k`, and that `k ≤ stabIndex m₀ k`. -/
public def stabIndex (m₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => m₀ 0
  | (k + 1) => max (max (stabIndex m₀ k + 1) (m₀ (k + 1))) (k + 1)

/-- The level from which the image of a transition map into level `stabIndex m₀ k` is already the
stable image. -/
public def coverIndex (m₀ m₁ : ℕ → ℕ) : ℕ → ℕ
  | 0 => max (m₁ (stabIndex m₀ 0)) (stabIndex m₀ 0)
  | (k + 1) => max (coverIndex m₀ m₁ k)
      (max (m₁ (stabIndex m₀ (k + 1))) (stabIndex m₀ (k + 1)))

public theorem stabIndex_lt_succ (m₀ : ℕ → ℕ) (k : ℕ) :
    stabIndex m₀ k < stabIndex m₀ (k + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans (le_max_left _ _))

public theorem stabIndex_mono (m₀ : ℕ → ℕ) : Monotone (stabIndex m₀) :=
  monotone_nat_of_le_succ fun k => (stabIndex_lt_succ m₀ k).le

public theorem le_stabIndex (m₀ : ℕ → ℕ) : ∀ k : ℕ, k ≤ stabIndex m₀ k
  | 0 => Nat.zero_le _
  | (_ + 1) => le_max_right _ _

public theorem m₀_le_stabIndex (m₀ : ℕ → ℕ) : ∀ k : ℕ, m₀ k ≤ stabIndex m₀ k
  | 0 => le_refl _
  | (_ + 1) => (le_max_right _ _).trans (le_max_left _ _)

public theorem coverIndex_mono (m₀ m₁ : ℕ → ℕ) : Monotone (coverIndex m₀ m₁) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

public theorem m₁_le_coverIndex (m₀ m₁ : ℕ → ℕ) :
    ∀ k : ℕ, m₁ (stabIndex m₀ k) ≤ coverIndex m₀ m₁ k
  | 0 => le_max_left _ _
  | (_ + 1) => (le_max_left _ _).trans (le_max_right _ _)

public theorem stabIndex_le_coverIndex (m₀ m₁ : ℕ → ℕ) :
    ∀ k : ℕ, stabIndex m₀ k ≤ coverIndex m₀ m₁ k
  | 0 => le_max_right _ _
  | (_ + 1) => (le_max_right _ _).trans (le_max_right _ _)

/-! ### The graded adic tower of reindexed stable images -/

namespace LadderData

variable {A : Type u} [CommRing A] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {H W : ℕᵒᵖ ⥤ ModuleCat.{v} A} (m₀ m₁ : ℕ → ℕ) (I : Ideal A)

/-- The homogeneous submodule of `H_{coverIndex k}` by which the reindexed stable image modulo
`I^k` is the quotient: `I^k` times everything, plus the kernel of the transition to level
`stabIndex k`. -/
public def stableQuotKer (k : ℕ) :
    Submodule A (H.obj (op (coverIndex m₀ m₁ k))) :=
  I ^ k • (⊤ : Submodule A (H.obj (op (coverIndex m₀ m₁ k)))) ⊔
    LinearMap.ker (tr H (stabIndex_le_coverIndex m₀ m₁ k))

/-- The `k`-th term of the graded adic tower: the stable image at level `stabIndex k`, modulo
`I^k`, presented as a quotient of `H_{coverIndex k}`. -/
public abbrev stableQuot (k : ℕ) : Type v :=
  H.obj (op (coverIndex m₀ m₁ k)) ⧸ stableQuotKer (H := H) m₀ m₁ I k

section Homog

variable (𝒜) (𝓗 : ∀ j : ℕ, ℤ → AddSubgroup (H.obj (op j)))
  [∀ j : ℕ, DirectSum.Decomposition (𝓗 j)]

/-- The submodule defining the `k`-th term is homogeneous, so the term is a graded module. -/
public theorem isHomogeneous_stableQuotKer
    (h𝓗 : ∀ (j i : ℕ) (d : ℤ) (a : A) (x : H.obj (op j)), a ∈ 𝒜 i → x ∈ 𝓗 j d →
      a • x ∈ 𝓗 j ((i : ℤ) + d))
    (hHtr : ∀ (j j' : ℕ) (h : j ≤ j') (d : ℤ) (x : H.obj (op j')), x ∈ 𝓗 j' d →
      tr H h x ∈ 𝓗 j d)
    (hIhom : I.IsHomogeneous 𝒜) (k : ℕ) :
    (stableQuotKer (H := H) m₀ m₁ I k).IsHomogeneous (𝓗 (coverIndex m₀ m₁ k)) :=
  Submodule.IsHomogeneous.sup _
    (Submodule.isHomogeneous_smul_top 𝒜 _ (fun i d a x => h𝓗 _ i d a x)
      (Ideal.IsHomogeneous.pow 𝒜 hIhom k))
    (Submodule.isHomogeneous_ker _ (𝓗 (stabIndex m₀ k)) (tr H _)
      (fun d x hx => hHtr _ _ _ d x hx))

end Homog

/-! ### The transition maps -/

variable (L : LadderData H W)

/-- The image of the transition map `H_{coverIndex k} → H_{stabIndex k}` is the stable image, for
the reindexings of this file. -/
public theorem range_tr_coverIndex
    (hm₁ : ∀ j m : ℕ, m₁ j ≤ m → ∀ h : j ≤ m, LinearMap.range (tr H h) = L.stable j)
    {k j : ℕ} (hj : coverIndex m₀ m₁ k ≤ j) (h : stabIndex m₀ k ≤ j) :
    LinearMap.range (tr H h) = L.stable (stabIndex m₀ k) :=
  hm₁ _ _ ((m₁_le_coverIndex m₀ m₁ k).trans hj) h

/-- The image of the transition map `H_{coverIndex k} → H_{stabIndex k}` is the stable image. -/
private theorem range_tr_stabIndex_le_coverIndex
    (hm₁ : ∀ j m : ℕ, m₁ j ≤ m → ∀ h : j ≤ m, LinearMap.range (tr H h) = L.stable j) (k : ℕ) :
    LinearMap.range (tr H (stabIndex_le_coverIndex m₀ m₁ k)) = L.stable (stabIndex m₀ k) :=
  range_tr_coverIndex m₀ m₁ L hm₁ (le_refl _) _

/-- A linear map sends `J • ⊤` into `J • ⊤`. -/
private theorem map_mem_smul_top {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (f : M →ₗ[A] N) {x : M} (hx : x ∈ J • (⊤ : Submodule A M)) :
    f x ∈ J • (⊤ : Submodule A N) := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul'', Submodule.map_top] at this
  exact Submodule.smul_mono le_rfl le_top this

/-- If an element dies at an intermediate level, it dies at any lower level. -/
private theorem tr_eq_zero_of_tr_eq_zero (D : ℕᵒᵖ ⥤ ModuleCat.{v} A) {a b c : ℕ} (h₁ : a ≤ b)
    (h₂ : b ≤ c) (h₃ : a ≤ c) {x : D.obj (op c)} (hx : tr D h₂ x = 0) : tr D h₃ x = 0 := by
  rw [← tr_tr D h₁ h₂ x, hx, map_zero]

/-- The transition maps respect the defining submodules, at any gap. -/
public theorem stableQuotKer_le_comap {k k' : ℕ} (h : k ≤ k') :
    stableQuotKer (H := H) m₀ m₁ I k' ≤
      Submodule.comap (tr H (coverIndex_mono m₀ m₁ h))
        (stableQuotKer (H := H) m₀ m₁ I k) := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · exact Submodule.mem_comap.2 (Submodule.mem_sup_left (map_mem_smul_top _ _
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right h) hx)))
  · refine Submodule.mem_comap.2 (Submodule.mem_sup_right ?_)
    rw [LinearMap.mem_ker, tr_tr H (stabIndex_le_coverIndex m₀ m₁ k) (coverIndex_mono m₀ m₁ h) x]
    exact tr_eq_zero_of_tr_eq_zero H (stabIndex_mono m₀ h) (stabIndex_le_coverIndex m₀ m₁ k') _ hx

/-- The transition map of the graded adic tower. -/
public def stableQuotTr (k : ℕ) :
    stableQuot (H := H) m₀ m₁ I (k + 1) →ₗ[A] stableQuot (H := H) m₀ m₁ I k :=
  Submodule.mapQ _ _ (tr H (coverIndex_mono m₀ m₁ (Nat.le_succ k)))
    (stableQuotKer_le_comap m₀ m₁ I (Nat.le_succ k))

public theorem stableQuotTr_mk (k : ℕ) (x : H.obj (op (coverIndex m₀ m₁ (k + 1)))) :
    stableQuotTr m₀ m₁ I k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (tr H (coverIndex_mono m₀ m₁ (Nat.le_succ k)) x) :=
  rfl

variable (hm₁ : ∀ j m : ℕ, m₁ j ≤ m → ∀ h : j ≤ m, LinearMap.range (tr H h) = L.stable j)

include hm₁

/-- **The transitions of the graded adic tower are surjective.** -/
public theorem surjective_stableQuotTr (k : ℕ) :
    Function.Surjective (stableQuotTr (H := H) m₀ m₁ I k) := by
  intro z
  obtain ⟨y, rfl⟩ := (stableQuotKer (H := H) m₀ m₁ I k).mkQ_surjective z
  have hrange : tr H (stabIndex_le_coverIndex m₀ m₁ k) y ∈
      LinearMap.range (tr H ((stabIndex_le_coverIndex m₀ m₁ k).trans
        (coverIndex_mono m₀ m₁ (Nat.le_succ k)))) := by
    rw [range_tr_coverIndex m₀ m₁ L hm₁ (coverIndex_mono m₀ m₁ (Nat.le_succ k)) _,
      ← range_tr_stabIndex_le_coverIndex m₀ m₁ L hm₁ k]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hrange
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rw [Submodule.mkQ_apply, stableQuotTr_mk]
  refine (Submodule.Quotient.eq _).2 (Submodule.mem_sup_right ?_)
  rw [LinearMap.mem_ker, map_sub,
    tr_tr H (stabIndex_le_coverIndex m₀ m₁ k) (coverIndex_mono m₀ m₁ (Nat.le_succ k)) x, hx,
    sub_self]

variable (hm₀ : ∀ (k : ℕ) (m m' : ℕ), m₀ k ≤ m → ∀ h : m ≤ m', ∀ x : H.obj (op m'),
    x ∈ L.stable m' → tr H h x ∈ I ^ k • (⊤ : Submodule A (H.obj (op m))) →
      x ∈ I ^ k • L.stable m')

include hm₀

/-- **The kernel of a transition of the graded adic tower is exactly `I^k`.** This is the
substance: the containment `I^k ⊆ ker` is formal, and the reverse is the stabilization of the
adic quotients of the stable images. -/
public theorem ker_stableQuotTr (k : ℕ) :
    LinearMap.ker (stableQuotTr (H := H) m₀ m₁ I k) =
      I ^ k • (⊤ : Submodule A (stableQuot (H := H) m₀ m₁ I (k + 1))) := by
  have hmap : I ^ k • (⊤ : Submodule A (stableQuot (H := H) m₀ m₁ I (k + 1))) =
      Submodule.map (stableQuotKer (H := H) m₀ m₁ I (k + 1)).mkQ
        (I ^ k • (⊤ : Submodule A (H.obj (op (coverIndex m₀ m₁ (k + 1)))))) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2
      (stableQuotKer (H := H) m₀ m₁ I (k + 1)).mkQ_surjective]
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨x, rfl⟩ := (stableQuotKer (H := H) m₀ m₁ I (k + 1)).mkQ_surjective z
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, stableQuotTr_mk,
      Submodule.Quotient.mk_eq_zero] at hz
    -- the transition of `x` to level `stabIndex k` lies in `I ^ k`
    have hdown : tr H ((stabIndex_le_coverIndex m₀ m₁ k).trans
        (coverIndex_mono m₀ m₁ (Nat.le_succ k))) x ∈
        I ^ k • (⊤ : Submodule A (H.obj (op (stabIndex m₀ k)))) := by
      rw [← tr_tr H (stabIndex_le_coverIndex m₀ m₁ k)
        (coverIndex_mono m₀ m₁ (Nat.le_succ k)) x]
      obtain ⟨y, hy1, w, hw, hxw⟩ := Submodule.mem_sup.1 hz
      rw [← hxw, map_add]
      rw [LinearMap.mem_ker.1 hw, add_zero]
      exact map_mem_smul_top _ _ hy1
    -- so the transition of `x` to level `stabIndex (k+1)` lies in `I ^ k` of the stable image
    have hstable : tr H (stabIndex_le_coverIndex m₀ m₁ (k + 1)) x ∈
        L.stable (stabIndex m₀ (k + 1)) := by
      rw [← range_tr_stabIndex_le_coverIndex m₀ m₁ L hm₁ (k + 1)]
      exact ⟨x, rfl⟩
    have hmem : tr H (stabIndex_le_coverIndex m₀ m₁ (k + 1)) x ∈
        I ^ k • L.stable (stabIndex m₀ (k + 1)) := by
      refine hm₀ k (stabIndex m₀ k) (stabIndex m₀ (k + 1)) (m₀_le_stabIndex m₀ k)
        (stabIndex_mono m₀ (Nat.le_succ k)) _ hstable ?_
      rw [tr_tr H (stabIndex_mono m₀ (Nat.le_succ k))
        (stabIndex_le_coverIndex m₀ m₁ (k + 1)) x]
      exact hdown
    -- rewrite that as the image of `I ^ k` times everything one level up
    have hmap' : I ^ k • L.stable (stabIndex m₀ (k + 1)) =
        Submodule.map (tr H (stabIndex_le_coverIndex m₀ m₁ (k + 1)))
          (I ^ k • (⊤ : Submodule A (H.obj (op (coverIndex m₀ m₁ (k + 1)))))) := by
      rw [Submodule.map_smul'', Submodule.map_top,
        range_tr_stabIndex_le_coverIndex m₀ m₁ L hm₁ (k + 1)]
    rw [hmap' ] at hmem
    obtain ⟨y, hy, hxy⟩ := hmem
    rw [hmap]
    refine ⟨y, hy, ?_⟩
    refine ((Submodule.Quotient.eq _).2 (Submodule.mem_sup_right ?_)).symm
    rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  · rw [hmap, Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_ker, Submodule.mkQ_apply, stableQuotTr_mk,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_sup_left (map_mem_smul_top _ _ hx)

omit hm₀ in
/-- Each term of the graded adic tower is a finite `A`-module: it is a quotient of the stable
image, which is a quotient of a term of the adic tower. -/
public theorem finite_stableQuot [∀ j : ℕ, Module.Finite A (W.obj (op j))] (k : ℕ) :
    Module.Finite A (stableQuot (H := H) m₀ m₁ I k) := by
  have hker : LinearMap.ker (tr H (stabIndex_le_coverIndex m₀ m₁ k)) ≤
      stableQuotKer (H := H) m₀ m₁ I k := le_sup_right
  have hfinq : Module.Finite A
      (H.obj (op (coverIndex m₀ m₁ k)) ⧸ LinearMap.ker (tr H (stabIndex_le_coverIndex m₀ m₁ k)))
      := by
    have hrange : Module.Finite A
        (LinearMap.range (tr H (stabIndex_le_coverIndex m₀ m₁ k))) := by
      rw [range_tr_stabIndex_le_coverIndex m₀ m₁ L hm₁ k]
      exact Module.Finite.of_surjective (L.g (stabIndex m₀ k)).hom.rangeRestrict
        (LinearMap.surjective_rangeRestrict _)
    exact Module.Finite.of_surjective
      (LinearMap.quotKerEquivRange (tr H (stabIndex_le_coverIndex m₀ m₁ k))).symm.toLinearMap
      (LinearMap.quotKerEquivRange (tr H (stabIndex_le_coverIndex m₀ m₁ k))).symm.surjective
  refine Module.Finite.of_surjective
    (Submodule.mapQ (LinearMap.ker (tr H (stabIndex_le_coverIndex m₀ m₁ k)))
      (stableQuotKer (H := H) m₀ m₁ I k) LinearMap.id (by simpa using hker)) ?_
  intro z
  obtain ⟨x, rfl⟩ := (stableQuotKer (H := H) m₀ m₁ I k).mkQ_surjective z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-! ### The tower as an inverse system -/

omit hm₁ hm₀ in
/-- `k ≤ coverIndex m₀ m₁ k`, the inequality that lets a term of the tower map down to the same
level of `H`. -/
public theorem le_coverIndex (k : ℕ) : k ≤ coverIndex m₀ m₁ k :=
  (le_stabIndex m₀ k).trans (stabIndex_le_coverIndex m₀ m₁ k)

omit hm₁ hm₀ in
/-- The graded adic tower as an `ℕᵒᵖ`-indexed inverse system of `A`-modules. Its level `k` is the
tower's level `k + 1`, so that the kernel of its one-step transition is the `(k+1)`-st power of
`I`: that is the indexing convention of `Stacks.ProObject.IsAdicTower`. Every transition map is
the transition of `H` read on the quotients, so `tr_stableQuotSystem_mk` holds by definition. -/
public def stableQuotSystem : ℕᵒᵖ ⥤ ModuleCat.{v} A where
  obj k := ModuleCat.of A (stableQuot (H := H) m₀ m₁ I (k.unop + 1))
  map {_ _} φ := ModuleCat.ofHom
    (Submodule.mapQ _ _
      (tr H (coverIndex_mono m₀ m₁ (Nat.add_le_add_right (leOfHom φ.unop) 1)))
      (stableQuotKer_le_comap m₀ m₁ I (Nat.add_le_add_right (leOfHom φ.unop) 1)))
  map_id k := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    obtain ⟨x, rfl⟩ := (stableQuotKer (H := H) m₀ m₁ I (k.unop + 1)).mkQ_surjective z
    change Submodule.Quotient.mk (tr H _ x) = Submodule.Quotient.mk x
    rw [tr_self]
  map_comp {k k' k''} φ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    obtain ⟨x, rfl⟩ := (stableQuotKer (H := H) m₀ m₁ I (k.unop + 1)).mkQ_surjective z
    change Submodule.Quotient.mk (tr H _ x) =
      Submodule.Quotient.mk (tr H _ (tr H _ x))
    rw [tr_tr]

omit hm₁ hm₀ in
/-- **The transitions of the system are the transitions of `H`, read on the quotients.** -/
public theorem tr_stableQuotSystem_mk {k k' : ℕ} (h : k ≤ k')
    (x : H.obj (op (coverIndex m₀ m₁ (k' + 1)))) :
    tr (stableQuotSystem (H := H) m₀ m₁ I) h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (tr H (coverIndex_mono m₀ m₁ (Nat.add_le_add_right h 1)) x) :=
  rfl

omit hm₁ hm₀ in
/-- The one-step transition of the system is the transition map of the tower. -/
public theorem tr_stableQuotSystem_succ (k : ℕ) :
    tr (stableQuotSystem (H := H) m₀ m₁ I) (Nat.le_succ k) =
      stableQuotTr (H := H) m₀ m₁ I (k + 1) :=
  rfl

/-- **The system of reindexed stable images is an adic tower**: its transitions are surjective
and the kernel of the one-step transition at level `k` is the `(k+1)`-st power of `I`. -/
public theorem isAdicTower_stableQuotSystem :
    IsAdicTower I (stableQuotSystem (H := H) m₀ m₁ I) where
  surjective k := by
    rw [tr_stableQuotSystem_succ]
    exact surjective_stableQuotTr m₀ m₁ I L hm₁ (k + 1)
  ker k := by
    rw [tr_stableQuotSystem_succ]
    exact ker_stableQuotTr m₀ m₁ I L hm₁ hm₀ (k + 1)

/-! ### The ladder between the tower and `H`

The tower maps down to `H` whenever the level drops by one: the kernel of the quotient
presentation of level `k + 1` consists of `I^{k+1}`-multiples, which `H` kills at level `k`, and
of elements dying at level `stabIndex (k+1)`, which is above `k`. Together with the quotient maps
`H_{coverIndex (k+1)} → N_{k+1}` this is a ladder, with both composites *equal* to transition
maps; so the tower and `H` have the same inverse limit. -/

omit hm₁ hm₀ in
/-- The kernel of the quotient presentation of level `k + 1` dies under the transition of `H` down
to level `k`. -/
public theorem stableQuotKer_le_ker_tr
    (hHann : ∀ j : ℕ, I ^ (j + 1) • (⊤ : Submodule A (H.obj (op j))) = ⊥) (k : ℕ) :
    stableQuotKer (H := H) m₀ m₁ I (k + 1) ≤
      LinearMap.ker (tr H ((Nat.le_succ k).trans (le_coverIndex m₀ m₁ (k + 1)))) := by
  refine sup_le ?_ ?_
  · rw [Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    have hmem : a • tr H ((Nat.le_succ k).trans (le_coverIndex m₀ m₁ (k + 1))) x ∈
        I ^ (k + 1) • (⊤ : Submodule A (H.obj (op k))) :=
      Submodule.smul_mem_smul ha Submodule.mem_top
    rw [hHann k, Submodule.mem_bot] at hmem
    exact hmem
  · intro x hx
    exact tr_eq_zero_of_tr_eq_zero H ((Nat.le_succ k).trans (le_stabIndex m₀ (k + 1)))
      (stabIndex_le_coverIndex m₀ m₁ (k + 1)) _ hx

omit hm₁ hm₀ in
/-- **The tower maps down to `H`**: level `k + 1` of the tower maps to level `k` of `H`, by the
transition map of `H`. -/
public def stableQuotDown
    (hHann : ∀ j : ℕ, I ^ (j + 1) • (⊤ : Submodule A (H.obj (op j))) = ⊥) (k : ℕ) :
    stableQuot (H := H) m₀ m₁ I (k + 1) →ₗ[A] H.obj (op k) :=
  Submodule.liftQ _ (tr H ((Nat.le_succ k).trans (le_coverIndex m₀ m₁ (k + 1))))
    (stableQuotKer_le_ker_tr m₀ m₁ I hHann k)

omit hm₁ hm₀ in
public theorem stableQuotDown_mk
    (hHann : ∀ j : ℕ, I ^ (j + 1) • (⊤ : Submodule A (H.obj (op j))) = ⊥) (k : ℕ)
    (x : H.obj (op (coverIndex m₀ m₁ (k + 1)))) :
    stableQuotDown m₀ m₁ I hHann k (Submodule.Quotient.mk x) =
      tr H ((Nat.le_succ k).trans (le_coverIndex m₀ m₁ (k + 1))) x :=
  rfl

omit hm₁ hm₀ in
/-- **The tower and `H` are linked by a ladder**, with both composites equal to transition maps on
the nose: the ladder's maps are the maps down to `H` and the quotient presentations. -/
public def stableQuotLadderData
    (hHann : ∀ j : ℕ, I ^ (j + 1) • (⊤ : Submodule A (H.obj (op j))) = ⊥) :
    LadderData (stableQuotSystem (H := H) m₀ m₁ I) H where
  p n := n
  f n := ModuleCat.ofHom (stableQuotDown m₀ m₁ I hHann n)
  q k := coverIndex m₀ m₁ (k + 1)
  g k := ModuleCat.ofHom (stableQuotKer (H := H) m₀ m₁ I (k + 1)).mkQ
  cf := by
    intro n m hnm
    refine ⟨m, hnm, le_refl m, ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
    obtain ⟨x, rfl⟩ := (stableQuotKer (H := H) m₀ m₁ I (m + 1)).mkQ_surjective z
    change stableQuotDown m₀ m₁ I hHann n
          (tr (stableQuotSystem (H := H) m₀ m₁ I) hnm (Submodule.Quotient.mk x)) =
        tr H hnm (stableQuotDown m₀ m₁ I hHann m
          (tr (stableQuotSystem (H := H) m₀ m₁ I) (le_refl m) (Submodule.Quotient.mk x)))
    simp only [tr_stableQuotSystem_mk, stableQuotDown_mk, tr_tr, tr_self]
  cg := by
    intro k k' hkk'
    refine ⟨coverIndex m₀ m₁ (k' + 1), coverIndex_mono m₀ m₁ (Nat.add_le_add_right hkk' 1),
      le_refl _, ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
    change Submodule.Quotient.mk
          (tr H (coverIndex_mono m₀ m₁ (Nat.add_le_add_right hkk' 1)) x) =
        tr (stableQuotSystem (H := H) m₀ m₁ I) hkk'
          (Submodule.Quotient.mk (tr H (le_refl (coverIndex m₀ m₁ (k' + 1))) x))
    simp only [tr_stableQuotSystem_mk, tr_self]
  fg := by
    intro n
    refine ⟨coverIndex m₀ m₁ (n + 1), le_refl _,
      (Nat.le_succ n).trans (le_coverIndex m₀ m₁ (n + 1)),
      ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
    obtain ⟨x, rfl⟩ :=
      (stableQuotKer (H := H) m₀ m₁ I (coverIndex m₀ m₁ (n + 1) + 1)).mkQ_surjective z
    change Submodule.Quotient.mk
          (stableQuotDown m₀ m₁ I hHann (coverIndex m₀ m₁ (n + 1))
            (tr (stableQuotSystem (H := H) m₀ m₁ I)
              (le_refl (coverIndex m₀ m₁ (n + 1))) (Submodule.Quotient.mk x))) =
        tr (stableQuotSystem (H := H) m₀ m₁ I)
          ((Nat.le_succ n).trans (le_coverIndex m₀ m₁ (n + 1))) (Submodule.Quotient.mk x)
    simp only [tr_stableQuotSystem_mk, stableQuotDown_mk, tr_self]
  gf := by
    intro n
    refine ⟨coverIndex m₀ m₁ (n + 1), le_refl _,
      (Nat.le_succ n).trans (le_coverIndex m₀ m₁ (n + 1)),
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
    change stableQuotDown m₀ m₁ I hHann n
          (Submodule.Quotient.mk (tr H (le_refl (coverIndex m₀ m₁ (n + 1))) x)) =
        tr H ((Nat.le_succ n).trans (le_coverIndex m₀ m₁ (n + 1))) x
    simp only [stableQuotDown_mk, tr_self]

omit hm₁ hm₀ in
/-- The tower is pro-isomorphic to `H`. -/
public theorem hasProLadder_stableQuotSystem
    (hHann : ∀ j : ℕ, I ^ (j + 1) • (⊤ : Submodule A (H.obj (op j))) = ⊥) :
    HasProLadder (stableQuotSystem (H := H) m₀ m₁ I) H :=
  let L' := stableQuotLadderData m₀ m₁ I hHann
  ⟨L'.p, L'.f, L'.q, L'.g, L'.cf, L'.cg, L'.fg, L'.gf⟩

/-! ### The grading of the tower -/

section GradedTower

variable (𝒜) (𝓗 : ∀ j : ℕ, ℤ → AddSubgroup (H.obj (op j)))
  [∀ j : ℕ, DirectSum.Decomposition (𝓗 j)]

omit hm₁ hm₀ in
/-- **The grading of the `k`-th term of the tower**: the images of the graded pieces of
`H_{coverIndex k}`. -/
public abbrev stableQuotPiece (k : ℕ) : ℤ → AddSubgroup (stableQuot (H := H) m₀ m₁ I k) :=
  Submodule.gradedQuotientPiece (𝓗 (coverIndex m₀ m₁ k)) (stableQuotKer (H := H) m₀ m₁ I k)

omit hm₁ hm₀ in
/-- The grading of the `k`-th term of the tower is a `DirectSum.Decomposition`. -/
@[instance_reducible] public noncomputable def stableQuotDecomposition
    (h𝓗 : ∀ (j i : ℕ) (d : ℤ) (a : A) (x : H.obj (op j)), a ∈ 𝒜 i → x ∈ 𝓗 j d →
      a • x ∈ 𝓗 j ((i : ℤ) + d))
    (hHtr : ∀ (j j' : ℕ) (h : j ≤ j') (d : ℤ) (x : H.obj (op j')), x ∈ 𝓗 j' d →
      tr H h x ∈ 𝓗 j d)
    (hIhom : I.IsHomogeneous 𝒜) (k : ℕ) :
    DirectSum.Decomposition (stableQuotPiece (H := H) m₀ m₁ I 𝓗 k) :=
  (Submodule.isInternal_gradedQuotientPiece _
    (isHomogeneous_stableQuotKer 𝒜 m₀ m₁ I 𝓗 h𝓗 hHtr hIhom k)).chooseDecomposition

omit hm₁ hm₀ [AddSubgroupClass σ A] [GradedRing 𝒜]
  [(j : ℕ) → DirectSum.Decomposition (𝓗 j)] in
/-- The grading of the tower is compatible with the grading of `A`. -/
public theorem smul_mem_stableQuotPiece
    (h𝓗 : ∀ (j i : ℕ) (d : ℤ) (a : A) (x : H.obj (op j)), a ∈ 𝒜 i → x ∈ 𝓗 j d →
      a • x ∈ 𝓗 j ((i : ℤ) + d))
    (k i : ℕ) (d : ℤ) (a : A) (z : stableQuot (H := H) m₀ m₁ I k) (ha : a ∈ 𝒜 i)
    (hz : z ∈ stableQuotPiece (H := H) m₀ m₁ I 𝓗 k d) :
    a • z ∈ stableQuotPiece (H := H) m₀ m₁ I 𝓗 k ((i : ℤ) + d) :=
  Submodule.smul_mem_gradedQuotientPiece 𝒜 _ (fun i d a x => h𝓗 _ i d a x) _ ha hz

omit hm₁ hm₀ [(j : ℕ) → DirectSum.Decomposition (𝓗 j)] in
/-- **The transitions of the tower preserve degrees.** -/
public theorem stableQuotTr_mem_stableQuotPiece
    (hHtr : ∀ (j j' : ℕ) (h : j ≤ j') (d : ℤ) (x : H.obj (op j')), x ∈ 𝓗 j' d →
      tr H h x ∈ 𝓗 j d)
    (k : ℕ) (d : ℤ) (z : stableQuot (H := H) m₀ m₁ I (k + 1))
    (hz : z ∈ stableQuotPiece (H := H) m₀ m₁ I 𝓗 (k + 1) d) :
    stableQuotTr (H := H) m₀ m₁ I k z ∈ stableQuotPiece (H := H) m₀ m₁ I 𝓗 k d := by
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨tr H (coverIndex_mono m₀ m₁ (Nat.le_succ k)) y, hHtr _ _ _ d y hy,
    (stableQuotTr_mk m₀ m₁ I k y).symm⟩

omit hm₁ hm₀ [(j : ℕ) → DirectSum.Decomposition (𝓗 j)] in
/-- **The map down to `H` preserves degrees.** -/
public theorem stableQuotDown_mem
    (hHtr : ∀ (j j' : ℕ) (h : j ≤ j') (d : ℤ) (x : H.obj (op j')), x ∈ 𝓗 j' d →
      tr H h x ∈ 𝓗 j d)
    (hHann : ∀ j : ℕ, I ^ (j + 1) • (⊤ : Submodule A (H.obj (op j))) = ⊥)
    (k : ℕ) (d : ℤ) (z : stableQuot (H := H) m₀ m₁ I (k + 1))
    (hz : z ∈ stableQuotPiece (H := H) m₀ m₁ I 𝓗 (k + 1) d) :
    stableQuotDown m₀ m₁ I hHann k z ∈ 𝓗 k d := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [Submodule.mkQ_apply, stableQuotDown_mk]
  exact hHtr _ _ _ d y hy

end GradedTower

end LadderData

end Stacks.ProObject

end
