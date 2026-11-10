module

public import Mathlib

/-!
# Inverse limits of towers of modules with pro-zero kernel and cokernel

A *tower* of `A`-modules is a family `T : ℕ → ModuleCat A` together with transition maps
`t n : T (n + 1) ⟶ T n`. Its inverse limit is realized concretely as the submodule
`Stacks.ProZero.towerSections` of compatible sequences inside the product `∀ n, T n`, which is
the shape in which a limit of modules of sections occurs in practice.

A map of towers `ψ n : X n ⟶ Y n` induces a map of compatible sequences. The main result is a
criterion for that induced map to be bijective: it suffices that the kernels and the cokernels
of the `ψ n` be *pro-zero*, meaning that for every level `n` there is a later level `m` from
which the kernel dies on descending to `n`, respectively from which every element of `Y m`
descends into the image of `ψ n`. Neither the kernel nor the cokernel needs to vanish at any
single level.

No Mittag-Leffler or derived-limit input is used: the proof is the elementary diagonal argument,
run on the functorial transition maps that `CategoryTheory.Functor.ofOpSequence` provides, so
that no arithmetic on the indices is ever transported.

## Main definitions

* `Stacks.ProZero.towerSections` — the module of compatible sequences of a tower.
* `Stacks.ProZero.towerMapLE` — the transition map `T m ⟶ T n` attached to `n ≤ m`.
* `Stacks.ProZero.towerSectionsMap` — the map of compatible sequences induced by a map of towers.
* `Stacks.ProZero.IsProZeroKer`, `Stacks.ProZero.IsProZeroCoker` — the two pro-zero conditions.

## Main results

* `Stacks.ProZero.injective_towerSectionsMap_of_proZeroKer` — a pro-zero kernel makes the induced
  map on compatible sequences injective.
* `Stacks.ProZero.surjective_towerSectionsMap_of_proZero` — pro-zero kernel and cokernel make it
  surjective.
* `Stacks.ProZero.bijective_towerSectionsMap_of_proZero` — **the criterion**: pro-zero kernel and
  cokernel make it bijective.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace Stacks.ProZero

variable {A : Type u} [CommRing A]

section Tower

variable (T : ℕ → ModuleCat.{v} A) (t : ∀ n, T (n + 1) ⟶ T n)

/-- The tower `T` with transition maps `t`, as a functor on the opposite of `ℕ`. -/
def towerFunctor : ℕᵒᵖ ⥤ ModuleCat.{v} A := Functor.ofOpSequence t

/-- The transition map of a tower from level `m` down to a level `n ≤ m`. -/
def towerMapLE {n m : ℕ} (h : n ≤ m) : T m ⟶ T n :=
  (towerFunctor T t).map (homOfLE h).op

/-- The transition map from a level to itself is the identity. -/
@[simp]
theorem towerMapLE_self {n : ℕ} (h : n ≤ n) : towerMapLE T t h = 𝟙 (T n) :=
  (congrArg (towerFunctor T t).map
      (Subsingleton.elim (homOfLE h).op (𝟙 (op n)))).trans ((towerFunctor T t).map_id (op n))

/-- The transition map from level `n + 1` to level `n` is `t n`. -/
@[simp]
theorem towerMapLE_succ (n : ℕ) (h : n ≤ n + 1) : towerMapLE T t h = t n :=
  (congrArg (towerFunctor T t).map
        (Subsingleton.elim (homOfLE h).op (homOfLE (Nat.le_add_right n 1)).op)).trans
    (Functor.ofOpSequence_map_homOfLE_succ t n)

/-- Transition maps compose: descending from `k` to `m` and then to `n` is descending from `k`
to `n`. -/
theorem towerMapLE_trans {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    towerMapLE T t h₂ ≫ towerMapLE T t h₁ = towerMapLE T t (h₁.trans h₂) :=
  ((towerFunctor T t).map_comp (homOfLE h₂).op (homOfLE h₁).op).symm.trans
    (congrArg (towerFunctor T t).map (Subsingleton.elim _ _))

/-- Elementwise form of `towerMapLE_trans`. -/
theorem towerMapLE_trans_apply {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x : T k) :
    towerMapLE T t h₁ (towerMapLE T t h₂ x) = towerMapLE T t (h₁.trans h₂) x :=
  congrArg (fun φ : T k ⟶ T n ↦ φ x) (towerMapLE_trans T t h₁ h₂)

/-- The compatible sequences of a tower of modules: the concrete inverse limit. -/
def towerSections : Submodule A (∀ n, T n) where
  carrier x := ∀ n, t n (x (n + 1)) = x n
  zero_mem' n := by simp
  add_mem' hx hy n := by simp [hx n, hy n]
  smul_mem' a x hx n := by simp [hx n]

/-- A sequence lies in `towerSections T t` if and only if `t n (x (n + 1)) = x n` for every `n`. -/
theorem mem_towerSections {x : ∀ n, T n} :
    x ∈ towerSections T t ↔ ∀ n, t n (x (n + 1)) = x n := Iff.rfl

/-- A compatible sequence is compatible for every transition map, not only the successor ones. -/
theorem towerSections_apply_le (x : towerSections T t) {n m : ℕ} (h : n ≤ m) :
    towerMapLE T t h (x.1 m) = x.1 n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
      rw [← towerMapLE_trans_apply T t hnm (Nat.le_succ m), towerMapLE_succ, x.2 m, ih]

end Tower

section ProZero

variable {X Y : ℕ → ModuleCat.{v} A} (dx : ∀ n, X (n + 1) ⟶ X n) (dy : ∀ n, Y (n + 1) ⟶ Y n)
  (ψ : ∀ n, X n ⟶ Y n)

/-- The kernels of a map of towers are **pro-zero**: from some later level the kernel dies on
descending to the given level. -/
def IsProZeroKer : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), ∀ x : X m, ψ m x = 0 → towerMapLE X dx h x = 0

/-- The cokernels of a map of towers are **pro-zero**: from some later level every element
descends into the image of the map at the given level. -/
def IsProZeroCoker : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), ∀ y : Y m, ∃ x : X n, ψ n x = towerMapLE Y dy h y

variable (hψ : ∀ (n : ℕ) (x : X (n + 1)), dy n (ψ (n + 1) x) = ψ n (dx n x))

include hψ

/-- A map of towers commutes with every transition map, not only the successor ones. -/
theorem towerMapLE_map {n m : ℕ} (h : n ≤ m) (x : X m) :
    ψ n (towerMapLE X dx h x) = towerMapLE Y dy h (ψ m x) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
      rw [← towerMapLE_trans_apply X dx hnm (Nat.le_succ m), towerMapLE_succ, ih,
        ← towerMapLE_trans_apply Y dy hnm (Nat.le_succ m), towerMapLE_succ, hψ]

/-- The map on compatible sequences induced by a map of towers. -/
def towerSectionsMap : towerSections X dx →ₗ[A] towerSections Y dy where
  toFun x := ⟨fun n ↦ ψ n (x.1 n), fun n ↦ by rw [hψ n (x.1 (n + 1)), x.2 n]⟩
  map_add' x y := Subtype.ext (funext fun n ↦ map_add (ψ n).hom _ _)
  map_smul' a x := Subtype.ext (funext fun n ↦ map_smul (ψ n).hom a _)

/-- The level-`n` value of the image of `x` under `towerSectionsMap` is `ψ n (x.1 n)`. -/
@[simp]
theorem towerSectionsMap_apply_coe (x : towerSections X dx) (n : ℕ) :
    (towerSectionsMap dx dy ψ hψ x).1 n = ψ n (x.1 n) := rfl

/-- With a pro-zero kernel the induced map on compatible sequences is injective: an element of
the limit killed at every level is killed at a later level, hence is zero at the given one. -/
theorem injective_towerSectionsMap_of_proZeroKer (hker : IsProZeroKer dx ψ) :
    Function.Injective (towerSectionsMap dx dy ψ hψ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  funext n
  obtain ⟨m, hnm, hm⟩ := hker n
  have hzero : ψ m (x.1 m) = 0 :=
    congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hx)) m
  have hd := hm _ hzero
  rwa [towerSections_apply_le X dx x hnm] at hd

/-- Descending a `ψ`-preimage of `y.1 i` to a lower level `m` gives a `ψ`-preimage of `y.1 m`. -/
private theorem map_towerMapLE_eq (y : towerSections Y dy) {m i : ℕ} (hi : m ≤ i) (z : X i)
    (hz : ψ i z = y.1 i) : ψ m (towerMapLE X dx hi z) = y.1 m := by
  rw [towerMapLE_map dx dy ψ hψ hi, hz, towerSections_apply_le Y dy y hi]

/-- The level-`n` value of a preimage, read off from any sufficiently late level: if the kernel of
`ψ` dies on descending from `m` to `n`, then the descent to `n` of a `ψ`-preimage of `y.1 m'` is
the same for every `m' ≥ m`, whatever preimage is taken. -/
private theorem descent_eq (y : towerSections Y dy) (n : ℕ) {m : ℕ} (hnm : n ≤ m)
    (hm : ∀ x : X m, ψ m x = 0 → towerMapLE X dx hnm x = 0)
    {m₁ m₂ : ℕ} (h₁ : m ≤ m₁) (h₂ : m ≤ m₂) (z₁ : X m₁) (z₂ : X m₂)
    (hz₁ : ψ m₁ z₁ = y.1 m₁) (hz₂ : ψ m₂ z₂ = y.1 m₂) :
    towerMapLE X dx (hnm.trans h₁) z₁ = towerMapLE X dx (hnm.trans h₂) z₂ := by
  have hsub : ψ m (towerMapLE X dx h₁ z₁ - towerMapLE X dx h₂ z₂) = 0 := by
    rw [map_sub, map_towerMapLE_eq dx dy ψ hψ y h₁ z₁ hz₁,
      map_towerMapLE_eq dx dy ψ hψ y h₂ z₂ hz₂, sub_self]
  have hd := hm _ hsub
  rw [map_sub, sub_eq_zero] at hd
  rw [← towerMapLE_trans_apply X dx hnm h₁, ← towerMapLE_trans_apply X dx hnm h₂]
  exact hd

/-- With pro-zero kernel and pro-zero cokernel the induced map on compatible sequences is
surjective.

Given `y` in the limit, the cokernel hypothesis makes `y.1 n` a value of `ψ n` at every level,
and the kernel hypothesis makes the descent to level `n` of such a preimage, chosen at a
sufficiently late level, independent of all the choices. Those canonical values form a compatible
sequence, because two consecutive ones can be computed from a single preimage at a level above
both thresholds. -/
theorem surjective_towerSectionsMap_of_proZero (hker : IsProZeroKer dx ψ)
    (hcoker : IsProZeroCoker dy ψ) :
    Function.Surjective (towerSectionsMap dx dy ψ hψ) := by
  intro y
  have hpre : ∀ i : ℕ, ∃ z : X i, ψ i z = y.1 i := by
    intro i
    obtain ⟨m, him, hm⟩ := hcoker i
    obtain ⟨z, hz⟩ := hm (y.1 m)
    exact ⟨z, by rw [hz, towerSections_apply_le Y dy y him]⟩
  choose thr hthr hkill using hker
  choose pre hpreψ using hpre
  have hval (n : ℕ) : ψ n (towerMapLE X dx (hthr n) (pre (thr n))) = y.1 n :=
    map_towerMapLE_eq dx dy ψ hψ y (hthr n) _ (hpreψ _)
  refine ⟨⟨fun n ↦ towerMapLE X dx (hthr n) (pre (thr n)), fun n ↦ ?_⟩, ?_⟩
  · change dx n (towerMapLE X dx (hthr (n + 1)) (pre (thr (n + 1)))) =
      towerMapLE X dx (hthr n) (pre (thr n))
    have hnM : thr n ≤ max (thr n) (thr (n + 1)) := le_max_left _ _
    have hsM : thr (n + 1) ≤ max (thr n) (thr (n + 1)) := le_max_right _ _
    rw [descent_eq dx dy ψ hψ y n (hthr n) (hkill n) le_rfl hnM _ (pre _)
        (hpreψ (thr n)) (hpreψ _),
      descent_eq dx dy ψ hψ y (n + 1) (hthr (n + 1)) (hkill (n + 1)) le_rfl hsM _ (pre _)
        (hpreψ (thr (n + 1))) (hpreψ _),
      ← towerMapLE_succ X dx n (Nat.le_succ n), towerMapLE_trans_apply X dx (Nat.le_succ n)]
  · exact Subtype.ext (funext hval)

/-- **The pro-zero criterion for an inverse limit of modules.** A map of towers of `A`-modules
whose kernels and cokernels are pro-zero induces a bijection on compatible sequences, even though
it may be neither injective nor surjective at any single level. -/
theorem bijective_towerSectionsMap_of_proZero (hker : IsProZeroKer dx ψ)
    (hcoker : IsProZeroCoker dy ψ) :
    Function.Bijective (towerSectionsMap dx dy ψ hψ) :=
  ⟨injective_towerSectionsMap_of_proZeroKer dx dy ψ hψ hker,
    surjective_towerSectionsMap_of_proZero dx dy ψ hψ hker hcoker⟩

end ProZero

end Stacks.ProZero

end
