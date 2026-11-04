module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.CategoryTheory.Limits.ProObject.Stages

/-!
# The stable images of a system pro-isomorphic to an adic tower, and their adic quotients

Let `A` be a commutative ring, `I ⊆ A` an ideal, and let `H` and `W` be inverse systems of
`A`-modules indexed by `ℕ`. Assume `W` is an *adic tower*: its transition maps are surjective and
`ker(W_{j+1} → W_j) = I^{j+1} W_{j+1}`, so that `W_j = W/I^{j+1}W` for the limit `W`. If `H` and
`W` are pro-isomorphic — concretely, linked by the ladder of
`Stacks.ProObject.HasProLadder` — then two things are true of `H`, and they are what the
algebraization of a graded formal module needs.

First, the images of the transition maps into `H_j` **stabilize**, and the stable image is the
range of the ladder map `g_j : W_{q j} → H_j`; call it `P_j`. It is a finite module when the `W_j`
are, the transition maps carry `P_{j+1}` *onto* `P_j`, and — this is the point — it is the image
of a transition map, so in the graded situation it is a graded submodule even though `g_j` is not
a graded map.

Second, and this is the substance, the quotients `P_m / I^k P_m` **stabilize in `m`**: for every
`k` there is an `m₀` with
`ker(P_{m'} → P_m) ⊆ I^k P_{m'}` for all `m' ≥ m ≥ m₀`.
This is what makes the system `k ↦ P_{m(k)} / I^k P_{m(k)}`, for a fast enough `m`, an adic tower
again — with the exact kernel condition `I^k`, not merely a containment — which is the hypothesis
of the graded limit theorem of [Stacks, Tag 0EKC].

## Main definitions

* `Stacks.ProObject.tr` — the transition map of an `ℕᵒᵖ`-indexed inverse system of modules, as a
  linear map.
* `Stacks.ProObject.IsAdicTower` — the predicate on `W` above.
* `Stacks.ProObject.LadderData` — the ladder of a pro-isomorphism, with its existentials named.
* `Stacks.ProObject.LadderData.stable` — the stable image `P_j`.
* `Stacks.ProObject.LadderData.ofIsoLeft` — ladder data transported along an isomorphism of the
  first system.

## Main results

* `Stacks.ProObject.IsAdicTower.ker_tr` — the kernel of a transition map of an adic tower.
* `Stacks.ProObject.LadderData.range_tr_eq_stable` — **the images into `H_j` stabilize**, at the
  range of the ladder map out of `W`.
* `Stacks.ProObject.LadderData.map_tr_stable` — the transitions carry one stable image onto the
  next.
* `Stacks.ProObject.LadderData.mem_pow_smul_stable_of_tr_mem_pow_smul_top` — **the adic quotients
  of the stable images stabilize.**
* `Stacks.ProObject.exists_limitIso_of_hasProLadder` — **a ladder computes the limit**: the limit
  of the first system is the vertex of any limit cone on the second.
* `Stacks.ProObject.HasProLadder.of_natIso` — a ladder transports along an isomorphism of the
  first system.

## Implementation notes

Everything is stated for the data of `Stacks.ProObject.HasProLadder` unpacked into its four
families, rather than for the predicate: the two main results need different parts of it, and the
indices at which the ladder identities hold have to be chosen by hand. The stable image is
`LinearMap.range (g j)` rather than an image of a transition map, so that its finiteness is
immediate; that it is an image of a transition map is the separate statement
`LadderData.range_tr_eq_stable`.

The stabilization argument is the elementary content of the `𝐆ₘ`-equivariance argument of
[Stacks, Tag 0EL4]: the source transports the grading across the canonical extension by a group
action, where here the adic tower `W` is used to show that the graded stable images already form
an adic tower after reindexing.

## References

* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0EKC](https://stacks.math.columbia.edu/tag/0EKC)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ProObject

/-! ### A ladder transports along an isomorphism of systems -/

section Transport

variable {C : Type u} [Category.{v} C]

/-- **A ladder transports along an isomorphism of the first system.** Composing the ladder maps
with the components of the isomorphism gives a ladder again; the composites stay transition maps
because the two families of components cancel. -/
public theorem HasProLadder.of_natIso {D D' E : ℕᵒᵖ ⥤ C} (e : D ≅ D')
    (h : HasProLadder D E) : HasProLadder D' E := by
  obtain ⟨p, f, q, g, cf, cg, fg, gf⟩ := h
  refine ⟨p, fun n => e.inv.app (op (p n)) ≫ f n, q, fun n => g n ≫ e.hom.app (op n),
    ?_, ?_, ?_, ?_⟩
  · intro n m hnm
    obtain ⟨k, h₁, h₂, hk⟩ := cf n m hnm
    refine ⟨k, h₁, h₂, ?_⟩
    simp only [Category.assoc] at hk ⊢
    rw [e.inv.naturality_assoc, hk, e.inv.naturality_assoc]
  · intro n m hnm
    obtain ⟨k, h₁, h₂, hk⟩ := cg n m hnm
    refine ⟨k, h₁, h₂, ?_⟩
    have hk' := congrArg (fun t : E.obj (op k) ⟶ D.obj (op n) => t ≫ e.hom.app (op n)) hk
    simp only [Category.assoc] at hk' ⊢
    rw [hk', e.hom.naturality]
  · intro n
    obtain ⟨k, h₁, h₂, hk⟩ := fg n
    refine ⟨k, h₁, h₂, ?_⟩
    have hk' := congrArg (fun t : D.obj (op k) ⟶ D.obj (op n) => t ≫ e.hom.app (op n)) hk
    simp only [Category.assoc] at hk' ⊢
    rw [e.inv.naturality_assoc, hk', e.hom.naturality, ← Category.assoc, e.inv_hom_id_app,
      Category.id_comp]
  · intro n
    obtain ⟨k, h₁, h₂, hk⟩ := gf n
    refine ⟨k, h₁, h₂, ?_⟩
    simp only [Category.assoc] at hk ⊢
    rw [← Category.assoc (e.hom.app (op (p n))), e.hom_inv_id_app, Category.id_comp, hk]

end Transport

variable {A : Type u} [CommRing A]

/-! ### Transition maps -/

/-- The transition map `D_m → D_n` of an `ℕᵒᵖ`-indexed inverse system of modules, for `n ≤ m`. -/
public abbrev tr (D : ℕᵒᵖ ⥤ ModuleCat.{v} A) {n m : ℕ} (h : n ≤ m) :
    D.obj (op m) →ₗ[A] D.obj (op n) :=
  (invTransition D h).hom

public theorem tr_self (D : ℕᵒᵖ ⥤ ModuleCat.{v} A) (n : ℕ) (x : D.obj (op n)) :
    tr D (le_refl n) x = x := by
  have h : invTransition D (le_refl n) = 𝟙 _ := by simp [invTransition]
  rw [show tr D (le_refl n) = (𝟙 (D.obj (op n)) : _ ⟶ _).hom from congrArg _ h]
  rfl

public theorem tr_tr (D : ℕᵒᵖ ⥤ ModuleCat.{v} A) {n m l : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ l)
    (x : D.obj (op l)) : tr D h₁ (tr D h₂ x) = tr D (h₁.trans h₂) x := by
  have h : invTransition D (h₁.trans h₂) = invTransition D h₂ ≫ invTransition D h₁ := by
    rw [invTransition, invTransition, invTransition, ← D.map_comp]
    exact congrArg D.map (Subsingleton.elim _ _)
  rw [show tr D (h₁.trans h₂) = (invTransition D h₂ ≫ invTransition D h₁).hom from congrArg _ h]
  rfl

/-! ### Adic towers -/

/-- An *adic tower* for an ideal `I`: the transition maps are surjective and the kernel of the
one-step transition `W_{j+1} → W_j` is `I^{j+1} W_{j+1}`. -/
public structure IsAdicTower (I : Ideal A) (W : ℕᵒᵖ ⥤ ModuleCat.{v} A) : Prop where
  /-- The one-step transition maps are surjective. -/
  surjective : ∀ j : ℕ, Function.Surjective (tr W (Nat.le_succ j))
  /-- The kernel of the one-step transition at level `j` is `I ^ (j + 1)` times everything. -/
  ker : ∀ j : ℕ, LinearMap.ker (tr W (Nat.le_succ j)) =
    I ^ (j + 1) • (⊤ : Submodule A (W.obj (op (j + 1))))

namespace IsAdicTower

variable {I : Ideal A} {W : ℕᵒᵖ ⥤ ModuleCat.{v} A} (hW : IsAdicTower I W)

include hW

public theorem surjective_tr {n m : ℕ} (h : n ≤ m) : Function.Surjective (tr W h) := by
  induction m, h using Nat.le_induction with
  | base => exact fun y => ⟨y, tr_self W n y⟩
  | succ m hnm ih =>
      intro y
      obtain ⟨z, hz⟩ := ih y
      obtain ⟨w, hw⟩ := hW.surjective m z
      exact ⟨w, by rw [← tr_tr W hnm (Nat.le_succ m) w, hw, hz]⟩

/-- The level-`j` term of an adic tower is annihilated by `I ^ (j + 1)`. -/
public theorem pow_smul_top_eq_bot (j : ℕ) :
    I ^ (j + 1) • (⊤ : Submodule A (W.obj (op j))) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Submodule.smul_le]
  intro a ha x _
  obtain ⟨y, rfl⟩ := hW.surjective j x
  have hy : a • y ∈ LinearMap.ker (tr W (Nat.le_succ j)) := by
    rw [hW.ker j]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  rw [Submodule.mem_bot, ← map_smul]
  exact hy

/-- **The kernel of a transition map of an adic tower.** -/
public theorem ker_tr {j m : ℕ} (h : j ≤ m) :
    LinearMap.ker (tr W h) = I ^ (j + 1) • (⊤ : Submodule A (W.obj (op m))) := by
  induction m, h using Nat.le_induction with
  | base =>
      refine le_antisymm (fun x hx => ?_) ?_
      · rw [LinearMap.mem_ker, tr_self] at hx
        rw [hx]
        exact zero_mem _
      · rw [Submodule.smul_le]
        intro a ha x _
        have : a • x ∈ I ^ (j + 1) • (⊤ : Submodule A (W.obj (op j))) :=
          Submodule.smul_mem_smul ha Submodule.mem_top
        rw [hW.pow_smul_top_eq_bot j, Submodule.mem_bot] at this
        rw [LinearMap.mem_ker, this, map_zero]
  | succ m hjm ih =>
      refine le_antisymm (fun x hx => ?_) ?_
      · rw [LinearMap.mem_ker, ← tr_tr W hjm (Nat.le_succ m) x] at hx
        have hmem : tr W (Nat.le_succ m) x ∈ I ^ (j + 1) • (⊤ : Submodule A (W.obj (op m))) := by
          rw [← ih]
          exact hx
        obtain ⟨z, hz, hzx⟩ : ∃ z ∈ I ^ (j + 1) • (⊤ : Submodule A (W.obj (op (m + 1)))),
            tr W (Nat.le_succ m) z = tr W (Nat.le_succ m) x := by
          have hmap : Submodule.map (tr W (Nat.le_succ m))
              (I ^ (j + 1) • (⊤ : Submodule A (W.obj (op (m + 1))))) =
              I ^ (j + 1) • (⊤ : Submodule A (W.obj (op m))) := by
            rw [Submodule.map_smul'', Submodule.map_top,
              LinearMap.range_eq_top.2 (hW.surjective m)]
          rw [← hmap] at hmem
          obtain ⟨z, hz, hzx⟩ := hmem
          exact ⟨z, hz, hzx⟩
        have hdiff : x - z ∈ LinearMap.ker (tr W (Nat.le_succ m)) := by
          rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
        rw [hW.ker m] at hdiff
        have hle : I ^ (m + 1) • (⊤ : Submodule A (W.obj (op (m + 1)))) ≤
            I ^ (j + 1) • (⊤ : Submodule A (W.obj (op (m + 1)))) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
        have := add_mem (hle hdiff) hz
        rwa [sub_add_cancel] at this
      · rw [Submodule.smul_le]
        intro a ha x _
        rw [LinearMap.mem_ker, ← tr_tr W hjm (Nat.le_succ m), map_smul]
        have : a • tr W (Nat.le_succ m) x ∈
            I ^ (j + 1) • (⊤ : Submodule A (W.obj (op m))) :=
          Submodule.smul_mem_smul ha Submodule.mem_top
        rw [← ih] at this
        exact this

end IsAdicTower

/-! ### The ladder, unpacked -/

variable {I : Ideal A} {H W : ℕᵒᵖ ⥤ ModuleCat.{v} A}

/-- A linear map sends `I ^ k` times everything into `I ^ k` times everything. -/
private theorem map_mem_pow_smul_top {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {k : ℕ} (φ : M →ₗ[A] N) {x : M}
    (hx : x ∈ I ^ k • (⊤ : Submodule A M)) : φ x ∈ I ^ k • (⊤ : Submodule A N) := by
  have : Submodule.map φ (I ^ k • (⊤ : Submodule A M)) ≤ I ^ k • (⊤ : Submodule A N) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact this ⟨x, hx, rfl⟩

/-- The elementary data of a pro-isomorphism of `ℕ`-indexed inverse systems of modules, as a
structure: the two families of maps, their compatibility with the transitions, and the two
composites. This is `Stacks.ProObject.HasProLadder` with its existentials named. -/
public structure LadderData (H W : ℕᵒᵖ ⥤ ModuleCat.{v} A) where
  /-- The reindexing of the maps out of `H`. -/
  p : ℕ → ℕ
  /-- The maps out of `H`. -/
  f : ∀ n, H.obj (op (p n)) ⟶ W.obj (op n)
  /-- The reindexing of the maps out of `W`. -/
  q : ℕ → ℕ
  /-- The maps out of `W`. -/
  g : ∀ n, W.obj (op (q n)) ⟶ H.obj (op n)
  /-- The maps out of `H` are compatible with the transitions. -/
  cf : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
    invTransition H h₁ ≫ f n = invTransition H h₂ ≫ f m ≫ invTransition W hnm
  /-- The maps out of `W` are compatible with the transitions. -/
  cg : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : q n ≤ k) (h₂ : q m ≤ k),
    invTransition W h₁ ≫ g n = invTransition W h₂ ≫ g m ≫ invTransition H hnm
  /-- One composite is a transition map of `H`. -/
  fg : ∀ n : ℕ, ∃ (k : ℕ) (h₁ : p (q n) ≤ k) (h₂ : n ≤ k),
    invTransition H h₁ ≫ f (q n) ≫ g n = invTransition H h₂
  /-- The other composite is a transition map of `W`. -/
  gf : ∀ n : ℕ, ∃ (k : ℕ) (h₁ : q (p n) ≤ k) (h₂ : n ≤ k),
    invTransition W h₁ ≫ g (p n) ≫ f n = invTransition W h₂

/-- A pro-isomorphism has ladder data. -/
public theorem exists_ladderData (h : HasProLadder H W) : Nonempty (LadderData H W) := by
  obtain ⟨p, f, q, g, cf, cg, fg, gf⟩ := h
  exact ⟨⟨p, f, q, g, cf, cg, fg, gf⟩⟩

/-- **Ladder data transports along an isomorphism of the first system.** Composing the maps out of
`H` with the inverse of the isomorphism and the maps into `H` with the isomorphism gives ladder
data again; the composites stay transition maps because the two families of components cancel. -/
public def LadderData.ofIsoLeft {H' : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : H ≅ H') (L : LadderData H W) :
    LadderData H' W where
  p := L.p
  f n := e.inv.app (op (L.p n)) ≫ L.f n
  q := L.q
  g n := L.g n ≫ e.hom.app (op n)
  cf n m hnm := by
    obtain ⟨k, h₁, h₂, hk⟩ := L.cf n m hnm
    refine ⟨k, h₁, h₂, ?_⟩
    simp only [Category.assoc] at hk ⊢
    rw [e.inv.naturality_assoc, hk, e.inv.naturality_assoc]
  cg n m hnm := by
    obtain ⟨k, h₁, h₂, hk⟩ := L.cg n m hnm
    refine ⟨k, h₁, h₂, ?_⟩
    have hk' := congrArg (fun t : W.obj (op k) ⟶ H.obj (op n) => t ≫ e.hom.app (op n)) hk
    simp only [Category.assoc] at hk' ⊢
    rw [hk', e.hom.naturality]
  fg n := by
    obtain ⟨k, h₁, h₂, hk⟩ := L.fg n
    refine ⟨k, h₁, h₂, ?_⟩
    have hk' := congrArg (fun t : H.obj (op k) ⟶ H.obj (op n) => t ≫ e.hom.app (op n)) hk
    simp only [Category.assoc] at hk' ⊢
    rw [e.inv.naturality_assoc, hk', e.hom.naturality, ← Category.assoc, e.inv_hom_id_app,
      Category.id_comp]
  gf n := by
    obtain ⟨k, h₁, h₂, hk⟩ := L.gf n
    refine ⟨k, h₁, h₂, ?_⟩
    simp only [Category.assoc] at hk ⊢
    rw [← Category.assoc (e.hom.app (op (L.p n))), e.hom_inv_id_app, Category.id_comp, hk]

namespace LadderData

variable (L : LadderData H W)

/-- The stable image of the system `H` in `H_j`: the range of the ladder map out of `W`. -/
public abbrev stable (j : ℕ) : Submodule A (H.obj (op j)) := LinearMap.range (L.g j).hom

public theorem cg_apply {n m : ℕ} (hnm : n ≤ m) :
    ∃ (k : ℕ) (h₁ : L.q n ≤ k) (h₂ : L.q m ≤ k), ∀ w : W.obj (op k),
      (L.g n).hom (tr W h₁ w) = tr H hnm ((L.g m).hom (tr W h₂ w)) := by
  obtain ⟨k, h₁, h₂, hk⟩ := L.cg n m hnm
  exact ⟨k, h₁, h₂, fun w => congrArg (fun φ => (ModuleCat.Hom.hom φ) w) hk⟩

public theorem fg_apply (n : ℕ) :
    ∃ (k : ℕ) (h₁ : L.p (L.q n) ≤ k) (h₂ : n ≤ k), ∀ y : H.obj (op k),
      (L.g n).hom ((L.f (L.q n)).hom (tr H h₁ y)) = tr H h₂ y := by
  obtain ⟨k, h₁, h₂, hk⟩ := L.fg n
  exact ⟨k, h₁, h₂, fun y => congrArg (fun φ => (ModuleCat.Hom.hom φ) y) hk⟩

public theorem gf_apply (n : ℕ) :
    ∃ (k : ℕ) (h₁ : L.q (L.p n) ≤ k) (h₂ : n ≤ k), ∀ w : W.obj (op k),
      (L.f n).hom ((L.g (L.p n)).hom (tr W h₁ w)) = tr W h₂ w := by
  obtain ⟨k, h₁, h₂, hk⟩ := L.gf n
  exact ⟨k, h₁, h₂, fun w => congrArg (fun φ => (ModuleCat.Hom.hom φ) w) hk⟩

variable (hW : IsAdicTower I W)

include hW

/-- **The stable image is an image of a transition map.** For `m` large the image of
`H_m → H_j` is the stable image `P_j`; this is what makes `P_j` a graded submodule in the graded
situation, the ladder maps not being graded. -/
public theorem range_tr_eq_stable (j : ℕ) :
    ∃ m₁ : ℕ, j ≤ m₁ ∧ ∀ m : ℕ, m₁ ≤ m → ∀ (h : j ≤ m),
      LinearMap.range (tr H h) = L.stable j := by
  obtain ⟨k, h₁, h₂, hk⟩ := L.fg_apply j
  refine ⟨max j k, le_max_left _ _, fun m hm h => le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := hy
    have hkm : k ≤ m := (le_max_right j k).trans hm
    rw [← tr_tr H h₂ hkm z, ← hk]
    exact ⟨_, rfl⟩
  · obtain ⟨k', h₁', h₂', hk'⟩ := L.cg_apply h
    intro y hy
    obtain ⟨w, rfl⟩ := hy
    obtain ⟨w', rfl⟩ := hW.surjective_tr h₁' w
    rw [hk' w']
    exact ⟨_, rfl⟩

/-- **The transition maps carry one stable image onto the next.** -/
public theorem map_tr_stable {j m : ℕ} (h : j ≤ m) :
    Submodule.map (tr H h) (L.stable m) = L.stable j := by
  obtain ⟨k, h₁, h₂, hk⟩ := L.cg_apply h
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, ⟨w, rfl⟩, rfl⟩
    obtain ⟨w', rfl⟩ := hW.surjective_tr h₂ w
    rw [← hk w']
    exact ⟨_, rfl⟩
  · rintro y ⟨w, rfl⟩
    obtain ⟨w', rfl⟩ := hW.surjective_tr h₁ w
    exact ⟨_, ⟨_, rfl⟩, (hk w').symm⟩

/-- **The adic quotients of the stable images stabilize.** For every `k` there is an `m₀` such
that for `m' ≥ m ≥ m₀` an element of the stable image at level `m'` whose transition to level `m`
lies in `I ^ k` times everything already lies in `I ^ k` times the stable image at level `m'`.

With surjectivity of the transitions on stable images this says that `P_{m'}/I^kP_{m'}` and
`P_m/I^kP_m` agree, which is what makes the reindexed quotients an adic tower with the exact
kernel condition. -/
public theorem mem_pow_smul_stable_of_tr_mem_pow_smul_top (k : ℕ) :
    ∃ m₀ : ℕ, ∀ m m' : ℕ, m₀ ≤ m → ∀ h : m ≤ m', ∀ x : H.obj (op m'),
      x ∈ L.stable m' → tr H h x ∈ I ^ k • (⊤ : Submodule A (H.obj (op m))) →
        x ∈ I ^ k • L.stable m' := by
  match k with
  | 0 =>
      refine ⟨0, fun m m' _ h x hx _ => ?_⟩
      simpa using hx
  | (κ + 1) =>
      refine ⟨L.p κ, fun m m' hm h x hx hxI => ?_⟩
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨k₁, h₁, h₂, hk₁⟩ := L.cg_apply h
      obtain ⟨k₂, h₁', h₂', hk₂⟩ := L.cg_apply hm
      obtain ⟨k₃, h₁'', h₂'', hk₃⟩ := L.gf_apply κ
      set K := max (max k₁ k₂) k₃ with hK
      have hk₁K : k₁ ≤ K := (le_max_left k₁ k₂).trans (le_max_left _ _)
      have hk₂K : k₂ ≤ K := (le_max_right k₁ k₂).trans (le_max_left _ _)
      have hk₃K : k₃ ≤ K := le_max_right _ _
      obtain ⟨v₃, hv₃⟩ := hW.surjective_tr (h₂.trans hk₁K) v
      -- the image at level `m` is `g m` of a lift of `v₃`
      have hstep : tr H h ((L.g m').hom v) =
          (L.g m).hom (tr W (h₁.trans hk₁K) v₃) := by
        rw [← hv₃, ← tr_tr W h₁ hk₁K v₃, ← tr_tr W h₂ hk₁K v₃]
        exact (hk₁ (tr W hk₁K v₃)).symm
      -- push it down to level `L.p κ` and apply `f κ`
      have hzero : (L.f κ).hom (tr H hm ((L.g m).hom (tr W (h₁.trans hk₁K) v₃))) = 0 := by
        have h0 : (L.g m).hom (tr W (h₁.trans hk₁K) v₃) ∈
            I ^ (κ + 1) • (⊤ : Submodule A (H.obj (op m))) := hstep ▸ hxI
        have h1 := map_mem_pow_smul_top (tr H hm) h0
        have h2 := map_mem_pow_smul_top (L.f κ).hom h1
        rwa [hW.pow_smul_top_eq_bot κ, Submodule.mem_bot] at h2
      -- rewrite that vanishing along the ladder to a transition of `W`
      have e1 : (L.f κ).hom ((L.g (L.p κ)).hom (tr W (h₁''.trans hk₃K) v₃)) =
          tr W (h₂''.trans hk₃K) v₃ := by
        rw [← tr_tr W h₁'' hk₃K v₃, ← tr_tr W h₂'' hk₃K v₃]
        exact hk₃ (tr W hk₃K v₃)
      have e2 : (L.g (L.p κ)).hom (tr W (h₁''.trans hk₃K) v₃) =
          tr H hm ((L.g m).hom (tr W (h₁.trans hk₁K) v₃)) := by
        have hc := hk₂ (tr W hk₂K v₃)
        rw [tr_tr W h₁' hk₂K v₃, tr_tr W h₂' hk₂K v₃] at hc
        exact hc
      have hvan : tr W (h₂''.trans hk₃K) v₃ = 0 := by
        rw [← e1, e2]
        exact hzero
      -- so the lift is `I ^ (κ+1)`-divisible, hence so is `v`, hence so is `x`
      have hv₃mem : v₃ ∈ I ^ (κ + 1) • (⊤ : Submodule A (W.obj (op K))) := by
        rw [← hW.ker_tr (h₂''.trans hk₃K), LinearMap.mem_ker]
        exact hvan
      have hvmem : v ∈ I ^ (κ + 1) • (⊤ : Submodule A (W.obj (op (L.q m')))) := by
        rw [← hv₃]
        exact map_mem_pow_smul_top _ hv₃mem
      have : Submodule.map (L.g m').hom
          (I ^ (κ + 1) • (⊤ : Submodule A (W.obj (op (L.q m'))))) =
          I ^ (κ + 1) • L.stable m' := by
        rw [Submodule.map_smul'', Submodule.map_top]
      exact this ▸ ⟨v, hvmem, rfl⟩

end LadderData

/-! ### A ladder computes the limit

A ladder is enough to identify the inverse limits of the two systems, which is how a
pro-isomorphism is turned into an isomorphism of the modules it presents. -/

/-- **A ladder computes the limit.** A ladder between inverse systems of modules induces an
isomorphism from the limit of the first onto the vertex of a limit cone on the second, and each
projection of the second system is then dominated by one of the projections of the first. -/
public theorem exists_limitIso_of_hasProLadder
    {R : Type u} [CommRing R] {A B : ℕᵒᵖ ⥤ ModuleCat.{v} R} [HasLimit A]
    (D : Cone B) (hD : IsLimit D) (hl : Stacks.ProObject.HasProLadder A B) :
    ∃ e : limit A ≅ D.pt, ∀ n : ℕ, ∃ k : ℕ,
      LinearMap.ker (limit.π A (op k)).hom ≤
        LinearMap.ker ((e.hom ≫ D.π.app (op n)).hom) := by
  obtain ⟨p, f, q, g, hcf, hcg, hfg, hgf⟩ := hl
  have hwA : ∀ {n m : ℕ} (hnm : n ≤ m), limit.π A (op m) ≫
      Stacks.ProObject.invTransition A hnm = limit.π A (op n) := fun hnm =>
    limit.w A (homOfLE hnm).op
  have hwB : ∀ {n m : ℕ} (hnm : n ≤ m), D.π.app (op m) ≫
      Stacks.ProObject.invTransition B hnm = D.π.app (op n) := fun hnm =>
    D.w (homOfLE hnm).op
  -- the cone on `B` with vertex `limit A`
  let cB : Cone B :=
    { pt := limit A
      π :=
        { app := fun j => limit.π A (op (p j.unop)) ≫ f j.unop
          naturality := fun i j φ => by
            obtain ⟨k, h₁, h₂, hk⟩ := hcf j.unop i.unop (leOfHom φ.unop)
            have hB : B.map φ = Stacks.ProObject.invTransition B (leOfHom φ.unop) :=
              congrArg B.map (Subsingleton.elim _ _)
            have hc := congrArg (limit.π A (op k) ≫ ·) hk
            simp only [← Category.assoc, hwA] at hc
            simp only [Functor.const_obj_map, hB]
            exact hc } }
  -- the cone on `A` with vertex `D.pt`
  let cA : Cone A :=
    { pt := D.pt
      π :=
        { app := fun j => D.π.app (op (q j.unop)) ≫ g j.unop
          naturality := fun i j φ => by
            obtain ⟨k, h₁, h₂, hk⟩ := hcg j.unop i.unop (leOfHom φ.unop)
            have hA : A.map φ = Stacks.ProObject.invTransition A (leOfHom φ.unop) :=
              congrArg A.map (Subsingleton.elim _ _)
            have hc := congrArg (D.π.app (op k) ≫ ·) hk
            simp only [← Category.assoc, hwB] at hc
            simp only [Functor.const_obj_map, hA]
            exact hc } }
  refine ⟨⟨hD.lift cB, limit.lift A cA, ?_, ?_⟩, ?_⟩
  · refine limit.hom_ext fun j => ?_
    obtain ⟨k, h₁, h₂, hk⟩ := hfg j.unop
    have hc := congrArg (limit.π A (op k) ≫ ·) hk
    simp only [← Category.assoc, hwA] at hc
    rw [Category.assoc, limit.lift_π, Category.id_comp]
    show hD.lift cB ≫ D.π.app (op (q j.unop)) ≫ g j.unop = limit.π A j
    rw [← Category.assoc, hD.fac cB (op (q j.unop))]
    show (limit.π A (op (p (q j.unop))) ≫ f (q j.unop)) ≫ g j.unop = limit.π A j
    exact hc
  · refine hD.hom_ext fun j => ?_
    obtain ⟨k, h₁, h₂, hk⟩ := hgf j.unop
    have hc := congrArg (D.π.app (op k) ≫ ·) hk
    simp only [← Category.assoc, hwB] at hc
    rw [Category.assoc, hD.fac cB j, Category.id_comp]
    show limit.lift A cA ≫ limit.π A (op (p j.unop)) ≫ f j.unop = D.π.app j
    rw [← Category.assoc, limit.lift_π cA (op (p j.unop))]
    show (D.π.app (op (q (p j.unop))) ≫ g (p j.unop)) ≫ f j.unop = D.π.app j
    exact hc
  · intro n
    refine ⟨p n, fun x hx => ?_⟩
    have hfac : hD.lift cB ≫ D.π.app (op n) = limit.π A (op (p n)) ≫ f n := hD.fac cB (op n)
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hfac, ModuleCat.hom_comp]
    simp only [LinearMap.coe_comp, Function.comp_apply, hx, map_zero]

end Stacks.ProObject

end
