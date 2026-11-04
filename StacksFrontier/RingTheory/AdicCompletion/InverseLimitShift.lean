module

public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# The kernel of a limit projection for a tower cut out at a shifted exponent

`Stacks.AdicCompletion.InverseLimit.InverseSystem.ker_proj` computes the kernel of the projection
`lim_n Mₙ ⟶ Mₙ` of a tower satisfying `Mₙ = M_{n+1} / Iⁿ M_{n+1}`: it is `Iⁿ` times the limit, so
that `lim_n Mₙ / Iⁿ = Mₙ`.  The towers of levels of [Stacks, Proposition 60.21.1, Tag 07JN] are
cut out one exponent higher than that: the level `e` of the system there is `D(n)/(p)^{N+e}` for
the uniform shift `N = Crystalline.uniformLevel`, so the relation available is
`M_e = M_{e+1}/p^{N+e} M_{e+1}` and not `M_e = M_{e+1}/p^e M_{e+1}`.

**This file computes the kernel of the limit projection for the shifted relation**:
`ker (lim_e M_e ⟶ M_e) = I^{N+e} (lim_e M_e)`, so that `lim_e M_e / I^{N+e} = M_e`.

## How the shift is removed

Not by redoing the argument of [Stacks, Tag 09B8], which is `ker_proj`, but by reducing to it.
The tower `Qₙ = Mₙ / Iⁿ Mₙ` satisfies the *unshifted* relation on the nose: the kernel of
`M_{n+1} ⟶ Mₙ` is `I^{N+n} M_{n+1}`, which is contained in `Iⁿ M_{n+1}`, so the preimage of
`Iⁿ Mₙ` is exactly `Iⁿ M_{n+1}` and therefore `Qₙ = Q_{n+1} / Iⁿ Q_{n+1}`.  And the two limits
agree, `Crystalline.invLimitQuotientEquiv`: the comparison `lim_n Mₙ ⟶ lim_n Qₙ` is injective
because `I^{N+n} Mₙ = 0` kills what the quotients forget, and surjective because a family of lifts
of a compatible family of classes becomes compatible after descending `N` levels — the descended
lifts stop moving once the error `Iʲ Mₘ` has `j ≥ N + m`, which is the only place the shift is
used.

## Main definitions

* `Crystalline.towerDescend` — the composite `Mₙ ⟶ Mₘ` of the transition maps of a tower, for
  `m ≤ n`, as a linear map.
* `Crystalline.shiftedQuotientSystem` — the tower `Mₙ / Iⁿ Mₙ`, as a bundled
  `Stacks.AdicCompletion.InverseLimit.InverseSystem` for `I`.
* `Crystalline.invLimitQuotientEquiv` — the identification `lim_n Mₙ ≅ lim_n (Mₙ / Iⁿ Mₙ)`.

## Main results

* `Crystalline.comap_pow_smul_top_of_le` — `Iᵏ M_{m+1}` is the preimage of `Iᵏ Mₘ` as soon as
  `k ≤ N + m`.
* `Crystalline.pow_smul_top_shift_eq_bot` — `I^{N+n}` annihilates `Mₙ`.
* `Crystalline.ker_proj_shift` — **the kernel of the limit projection is `I^{N+n}`** times the
  limit.
* `Crystalline.proj_shift_quotientEquiv` — the resulting identification
  `lim_n Mₙ / I^{N+n} ≅ Mₙ`.

## References

* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

universe u w

namespace Crystalline

open Stacks.AdicCompletion.InverseLimit

/-! ### A linear map carries `Iᵏ` into `Iᵏ` -/

/-- A linear map carries `J` times its source into `J` times its target. -/
theorem linearMap_mem_smul_top {A : Type u} [CommRing A] {P Q : Type w} [AddCommGroup P]
    [Module A P] [AddCommGroup Q] [Module A Q] (f : P →ₗ[A] Q) (J : Ideal A) {z : P}
    (hz : z ∈ J • (⊤ : Submodule A P)) : f z ∈ J • (⊤ : Submodule A Q) := by
  have hle : Submodule.map f (J • ⊤) ≤ J • (⊤ : Submodule A Q) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨z, hz, rfl⟩

/-- A surjective linear map carries `J` times its source onto `J` times its target. -/
private theorem map_smul_top_of_surjective {A : Type u} [CommRing A] {P Q : Type w}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (f : P →ₗ[A] Q)
    (hf : Function.Surjective f) (J : Ideal A) :
    Submodule.map f (J • ⊤) = J • (⊤ : Submodule A Q) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- Higher powers of an ideal times the whole module give smaller submodules. -/
private theorem pow_smul_top_anti {A : Type u} [CommRing A] {I : Ideal A} {P : Type w}
    [AddCommGroup P] [Module A P] {i j : ℕ} (h : i ≤ j) :
    I ^ j • (⊤ : Submodule A P) ≤ I ^ i • ⊤ :=
  Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl

/-! ### Descending a tower -/

section Descend

variable {A : Type u} [CommRing A] {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module A (M n)] (t : ∀ n, M (n + 1) →ₗ[A] M n)

/-- **The composite of the transition maps of a tower**, from the level `n` down to a level
`m ≤ n`, as an `A`-linear map. -/
def towerDescend {m : ℕ} : ∀ {n : ℕ}, m ≤ n → (M n →ₗ[A] M m) :=
  Nat.leRec LinearMap.id fun k _ f ↦ f ∘ₗ t k

/-- Descending from a level `m` to itself is the identity of `M m`. -/
@[simp] theorem towerDescend_self {m : ℕ} (h : m ≤ m) :
    towerDescend t h = (LinearMap.id : M m →ₗ[A] M m) :=
  Nat.leRec_self (motive := fun n (_ : m ≤ n) ↦ M n →ₗ[A] M m) _ _

/-- Descending from the level `n + 1` to `m` is applying the transition map `t n` and then
descending from the level `n` to `m`. -/
theorem towerDescend_succ {m n : ℕ} (h : m ≤ n) (h' : m ≤ n + 1) :
    towerDescend t h' = towerDescend t h ∘ₗ t n :=
  Nat.leRec_succ (motive := fun n (_ : m ≤ n) ↦ M n →ₗ[A] M m) _ _ h

/-- Descending to the level `m + 1` and applying one more transition map is descending to the
level `m`. -/
theorem towerDescend_transition {m n : ℕ} (h : m + 1 ≤ n) (h' : m ≤ n) :
    t m ∘ₗ towerDescend t h = towerDescend t h' := by
  induction n, h using Nat.le_induction with
  | base => rw [towerDescend_self, towerDescend_succ t le_rfl, towerDescend_self]; rfl
  | succ n h ih =>
      rw [towerDescend_succ t h, ← LinearMap.comp_assoc, ih (Nat.le_of_succ_le h),
        towerDescend_succ t (Nat.le_of_succ_le h) h']

/-- A compatible family in the limit is carried to its lower components by the descent maps. -/
theorem towerDescend_apply_of_mem_invLimit {x : ∀ n, M n} (hx : x ∈ invLimit M t) {m n : ℕ}
    (h : m ≤ n) : towerDescend t h (x n) = x m := by
  induction n, h using Nat.le_induction with
  | base => rw [towerDescend_self]; rfl
  | succ n h ih =>
      rw [towerDescend_succ t h, LinearMap.comp_apply, hx n, ih]

end Descend

/-! ### The shifted tower relation -/

section Shift

variable {A : Type u} [CommRing A] {I : Ideal A} {M : ℕ → Type w} [∀ n, AddCommGroup (M n)]
  [∀ n, Module A (M n)] (t : ∀ n, M (n + 1) →ₗ[A] M n) (N : ℕ)
  (hsurj : ∀ n, Function.Surjective (t n))
  (hker : ∀ n, LinearMap.ker (t n) = I ^ (N + n) • (⊤ : Submodule A (M (n + 1))))

include hsurj in
/-- A surjection carries `Iᵏ` of its source onto `Iᵏ` of its target. -/
theorem map_pow_smul_top_transition (k n : ℕ) :
    Submodule.map (t n) (I ^ k • ⊤) = (I ^ k • ⊤ : Submodule A (M n)) := by
  exact map_smul_top_of_surjective (t n) (hsurj n) _

include hsurj hker in
/-- **`Iᵏ M_{m+1}` is the preimage of `Iᵏ Mₘ`** as soon as `k ≤ N + m`: the kernel
`I^{N+m} M_{m+1}` of the transition map is then already contained in `Iᵏ M_{m+1}`. -/
theorem comap_pow_smul_top_of_le {k m : ℕ} (hkm : k ≤ N + m) :
    Submodule.comap (t m) (I ^ k • (⊤ : Submodule A (M m)))
      = I ^ k • (⊤ : Submodule A (M (m + 1))) := by
  rw [← map_pow_smul_top_transition t hsurj k m, Submodule.comap_map_eq, hker m]
  exact sup_eq_left.2 (pow_smul_top_anti hkm)

include hsurj hker in
/-- **`I^{N+n}` annihilates `Mₙ`**, since `Mₙ` is `M_{n+1}` modulo `I^{N+n} M_{n+1}`. -/
theorem pow_smul_top_shift_eq_bot (n : ℕ) :
    I ^ (N + n) • (⊤ : Submodule A (M n)) = ⊥ := by
  rw [← map_pow_smul_top_transition t hsurj (N + n) n, ← hker n, eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  simpa using hy

include hsurj hker in
/-- A compatible family vanishing at the level `e` has every later component in `I^{N+e}`. -/
theorem mem_pow_smul_top_of_proj_eq_zero_shift {x : ∀ n, M n} (hx : x ∈ invLimit M t) {e : ℕ}
    (he : x e = 0) {j : ℕ} (hj : e ≤ j) : x j ∈ I ^ (N + e) • (⊤ : Submodule A (M j)) := by
  induction j, hj using Nat.le_induction with
  | base => rw [he]; exact Submodule.zero_mem _
  | succ j hj ih =>
      have hc : x (j + 1) ∈
          Submodule.comap (t j) (I ^ (N + e) • (⊤ : Submodule A (M j))) := by
        simpa [hx j] using ih
      rwa [comap_pow_smul_top_of_le t N hsurj hker (Nat.add_le_add_left hj N)] at hc

/-! ### The unshifted tower of quotients -/

include hsurj hker in
/-- The transition maps of the tower pass to the quotients `Mₙ / Iⁿ Mₙ`. -/
theorem le_comap_pow_smul_top_succ (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A (M (n + 1))) ≤
      Submodule.comap (t n) (I ^ n • (⊤ : Submodule A (M n))) := by
  rw [comap_pow_smul_top_of_le t N hsurj hker (Nat.le_add_left n N)]
  exact pow_smul_top_anti n.le_succ

/-- **The tower `Mₙ / Iⁿ Mₙ`**, which satisfies the *unshifted* relation
`Qₙ = Q_{n+1} / Iⁿ Q_{n+1}` of [Stacks, Tag 09B8] whenever the tower `(Mₙ)` satisfies the shifted
one. -/
def shiftedQuotientSystem : InverseSystem I where
  M n := M n ⧸ (I ^ n • (⊤ : Submodule A (M n)))
  π n := Submodule.mapQ _ _ (t n) (le_comap_pow_smul_top_succ t N hsurj hker n)
  surjective n := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := hsurj n y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  ker_π n := by
    have hmap : Submodule.map (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A (M (n + 1)))))
          (I ^ n • ⊤) =
        I ^ n • (⊤ : Submodule A (M (n + 1) ⧸ (I ^ (n + 1) •
          (⊤ : Submodule A (M (n + 1)))))) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap]
    refine le_antisymm (fun y hy ↦ ?_) ?_
    · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      refine ⟨y, ?_, rfl⟩
      have hy' : Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule A (M n))) (t n y) = 0 := hy
      have hy'' : t n y ∈ I ^ n • (⊤ : Submodule A (M n)) :=
        (Submodule.Quotient.mk_eq_zero _).1 hy'
      rw [← comap_pow_smul_top_of_le t N hsurj hker (Nat.le_add_left n N)]
      exact hy''
    · rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.comap (t n) (I ^ n • (⊤ : Submodule A (M n))) := by
        rw [comap_pow_smul_top_of_le t N hsurj hker (Nat.le_add_left n N)]; exact hx
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule A (M n))) (t n x) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hx'

/-! ### The two limits agree -/

/-- **The comparison map `lim_n Mₙ ⟶ lim_n (Mₙ / Iⁿ Mₙ)`**, the reduction of each component of a
compatible family. -/
def invLimitQuotientMap :
    ↥(invLimit M t) →ₗ[A] ↥(shiftedQuotientSystem t N hsurj hker).limit where
  toFun x := ⟨fun n ↦ Submodule.Quotient.mk ((x : ∀ n, M n) n), fun n ↦ by
    change Submodule.mapQ _ _ (t n) (le_comap_pow_smul_top_succ t N hsurj hker n)
        (Submodule.Quotient.mk ((x : ∀ n, M n) (n + 1))) = _
    rw [Submodule.mapQ_apply, x.property n]⟩
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The `n`-th component of the image of a compatible family under
`Crystalline.invLimitQuotientMap` is the class of its `n`-th component. -/
@[simp] theorem invLimitQuotientMap_val (x : ↥(invLimit M t)) (n : ℕ) :
    (invLimitQuotientMap t N hsurj hker x).val n =
      Submodule.Quotient.mk ((x : ∀ n, M n) n) :=
  rfl

include hsurj hker in
/-- **The comparison map of `Crystalline.invLimitQuotientMap` is injective.**  A compatible family
all of whose components are reduced away lies in `I^{N+n}` at the level `N + n`, and descending
from there to the level `n` lands in `I^{N+n} Mₙ = 0`. -/
theorem invLimitQuotientMap_injective :
    Function.Injective (invLimitQuotientMap t N hsurj hker) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  refine Subtype.ext (funext fun n ↦ ?_)
  have hval : ∀ m, (x : ∀ n, M n) m ∈ I ^ m • (⊤ : Submodule A (M m)) := fun m ↦
    (Submodule.Quotient.mk_eq_zero _).1
      (congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hx)) m)
  have hmem : towerDescend t (Nat.le_add_left n N) ((x : ∀ n, M n) (N + n)) ∈
      I ^ (N + n) • (⊤ : Submodule A (M n)) :=
    linearMap_mem_smul_top _ _ (hval (N + n))
  rw [towerDescend_apply_of_mem_invLimit t x.property (Nat.le_add_left n N)] at hmem
  rw [pow_smul_top_shift_eq_bot t N hsurj hker n] at hmem
  exact hmem

include hsurj hker in
/-- **The comparison map of `Crystalline.invLimitQuotientMap` is surjective.**  Lift each class to
the level it lives at and descend the lift `N` levels: the descended lifts no longer move, because
the error at the level `j` lies in `Iʲ Mₘ`, which vanishes once `j ≥ N + m`. -/
theorem invLimitQuotientMap_surjective :
    Function.Surjective (invLimitQuotientMap t N hsurj hker) := by
  classical
  intro y
  choose z hz using fun n ↦
    Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule A (M n))) (y.val n)
  have herr : ∀ j, t j (z (j + 1)) - z j ∈ I ^ j • (⊤ : Submodule A (M j)) := by
    intro j
    refine (Submodule.Quotient.eq _).1 ?_
    have hy := y.property j
    have h1 : Submodule.mapQ _ _ (t j) (le_comap_pow_smul_top_succ t N hsurj hker j)
        (Submodule.Quotient.mk (z (j + 1))) = Submodule.Quotient.mk (z j) := by
      rw [show Submodule.Quotient.mk (z (j + 1)) = y.val (j + 1) from hz (j + 1),
        show Submodule.Quotient.mk (z j) = y.val j from hz j]
      exact hy
    rwa [Submodule.mapQ_apply] at h1
  have hstep : ∀ (m j : ℕ) (hmj : m ≤ j),
      towerDescend t (hmj.trans j.le_succ) (z (j + 1)) - towerDescend t hmj (z j) ∈
        I ^ j • (⊤ : Submodule A (M m)) := by
    intro m j hmj
    rw [towerDescend_succ t hmj (hmj.trans j.le_succ), LinearMap.comp_apply, ← map_sub]
    exact linearMap_mem_smul_top _ _ (herr j)
  have hstab : ∀ (m j : ℕ) (hmj : m ≤ j), N + m ≤ j →
      towerDescend t (hmj.trans j.le_succ) (z (j + 1)) = towerDescend t hmj (z j) := by
    intro m j hmj hNm
    have h1 := hstep m j hmj
    have h2 := pow_smul_top_anti (I := I) (P := M m) hNm
    rw [pow_smul_top_shift_eq_bot t N hsurj hker m] at h2
    rw [← sub_eq_zero]
    simpa using h2 h1
  have hclose : ∀ (n j : ℕ) (h : n ≤ j),
      towerDescend t h (z j) - z n ∈ I ^ n • (⊤ : Submodule A (M n)) := by
    intro n j h
    induction j, h using Nat.le_induction with
    | base => rw [towerDescend_self]; simp
    | succ j hnj ih =>
        have := Submodule.add_mem _ (pow_smul_top_anti hnj (hstep n j hnj)) ih
        rwa [sub_add_sub_cancel] at this
  refine ⟨⟨fun n ↦ towerDescend t (Nat.le_add_left n N) (z (N + n)), fun n ↦ ?_⟩,
    Subtype.ext (funext fun n ↦ ?_)⟩
  · show t n (towerDescend t (Nat.le_add_left (n + 1) N) (z (N + (n + 1)))) = _
    rw [← LinearMap.comp_apply,
      towerDescend_transition t (Nat.le_add_left (n + 1) N) (Nat.le_succ_of_le
        (Nat.le_add_left n N))]
    exact hstab n (N + n) (Nat.le_add_left n N) le_rfl
  · rw [invLimitQuotientMap_val]
    show Submodule.Quotient.mk (towerDescend t (Nat.le_add_left n N) (z (N + n))) = _
    rw [← hz n]
    exact (Submodule.Quotient.eq _).2 (hclose n (N + n) (Nat.le_add_left n N))

/-- **The identification `lim_n Mₙ ≅ lim_n (Mₙ / Iⁿ Mₙ)`** for a tower cut out at the shifted
exponent. -/
noncomputable def invLimitQuotientEquiv :
    ↥(invLimit M t) ≃ₗ[A] ↥(shiftedQuotientSystem t N hsurj hker).limit :=
  LinearEquiv.ofBijective (invLimitQuotientMap t N hsurj hker)
    ⟨invLimitQuotientMap_injective t N hsurj hker,
      invLimitQuotientMap_surjective t N hsurj hker⟩

/-- The `n`-th component of the image of a compatible family under
`Crystalline.invLimitQuotientEquiv` is the class of its `n`-th component. -/
@[simp] theorem invLimitQuotientEquiv_apply_val (x : ↥(invLimit M t)) (n : ℕ) :
    (invLimitQuotientEquiv t N hsurj hker x).val n =
      Submodule.Quotient.mk ((x : ∀ n, M n) n) :=
  rfl

/-! ### The kernel of the limit projection -/

include hsurj hker in
/-- **The kernel of the projection `lim_n Mₙ ⟶ Mₙ` is `I^{N+n}` times the limit**, for a tower
with `ker (M_{n+1} ⟶ Mₙ) = I^{N+n} M_{n+1}`.

At `N = 0` this is `Stacks.AdicCompletion.InverseLimit.InverseSystem.ker_proj`, which is
[Stacks, Tag 09B8]; the general case is reduced to it through the tower `Mₙ / Iⁿ Mₙ`, which
satisfies the unshifted relation, and the identification
`Crystalline.invLimitQuotientEquiv` of the two limits. -/
theorem ker_proj_shift (hI : I.FG) (n : ℕ) :
    LinearMap.ker (invLimit.proj M t n) =
      I ^ (N + n) • (⊤ : Submodule A ↥(invLimit M t)) := by
  set S := shiftedQuotientSystem t N hsurj hker with hS
  set e := invLimitQuotientEquiv t N hsurj hker with he
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · have hxz : (x : ∀ m, M m) n = 0 := LinearMap.mem_ker.1 hx
    have hup : (x : ∀ m, M m) (N + n) ∈ I ^ (N + n) • (⊤ : Submodule A (M (N + n))) :=
      mem_pow_smul_top_of_proj_eq_zero_shift t N hsurj hker x.property hxz (Nat.le_add_left n N)
    have hker' : e x ∈ LinearMap.ker (S.proj (N + n)) := by
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk ((x : ∀ m, M m) (N + n)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hup
    rw [S.ker_proj hI (N + n)] at hker'
    have himg : e x ∈ Submodule.map (e : ↥(invLimit M t) →ₗ[A] ↥S.limit)
        (I ^ (N + n) • (⊤ : Submodule A ↥(invLimit M t))) := by
      rw [map_smul_top_of_surjective _ e.surjective]
      exact hker'
    obtain ⟨w, hw, hwx⟩ := himg
    rwa [← e.injective hwx]
  · rw [Submodule.smul_le]
    intro r hr x _
    have h0 : r • (x : ∀ m, M m) n ∈ I ^ (N + n) • (⊤ : Submodule A (M n)) :=
      Submodule.smul_mem_smul hr Submodule.mem_top
    rw [pow_smul_top_shift_eq_bot t N hsurj hker n, Submodule.mem_bot] at h0
    rw [LinearMap.mem_ker]
    show r • (x : ∀ m, M m) n = 0
    exact h0

include hsurj hker in
/-- **The resulting identification `lim_n Mₙ / I^{N+n} ≅ Mₙ`**, the shifted form of
[Stacks, Tag 09B8] (1). -/
noncomputable def proj_shift_quotientEquiv (hI : I.FG) (n : ℕ) :
    (↥(invLimit M t) ⧸ (I ^ (N + n) • (⊤ : Submodule A ↥(invLimit M t)))) ≃ₗ[A] M n :=
  (Submodule.quotEquivOfEq _ _ (ker_proj_shift t N hsurj hker hI n).symm).trans
    ((invLimit.proj M t n).quotKerEquivOfSurjective (invLimit.proj_surjective M t hsurj n))

end Shift

end Crystalline

end
