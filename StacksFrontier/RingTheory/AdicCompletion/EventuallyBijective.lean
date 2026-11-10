module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Bijectivity of an adic completion from bijectivity at deep levels

Let `I` be an ideal of a commutative ring `R` and let `f : X →ₗ[R] Y` be a map of `R`-modules.
Mathlib's `AdicCompletion.map I f` is computed level by level from the reductions
`f.reduceModIdeal (I ^ n)`, so bijectivity of those reductions makes the completed map bijective.
Only the levels beyond some cutoff `N` are needed: the levels below are reached from the deep ones
through the transition maps, and both the kernel and the image statement descend along a
transition.

The cutoff matters in practice.  The comparison of [Stacks, Lemma 60.20.1, Tag 07KK] identifies the
divided power differentials of a ring modulo `pⁿ` with those of its `p`-adic completion modulo `pⁿ`
only once `pⁿ` lies inside the divided power ideal and is stable under the divided powers, which
happens from some level on and not before.

The second ingredient here is an elementwise reading of levelwise bijectivity: the reduction
`X / P → Y / Q` of `f` is bijective exactly when every `y : Y` is congruent to some `f x` modulo
`Q` and every `x : X` with `f x ∈ Q` already lies in `P`.  Those two conditions mention only the
underlying sets of `P` and `Q`, so they transfer for free between the submodule structures that
the same subgroup `pⁿ · X` carries over different rings — a bookkeeping step that comes up
whenever the `p`-adic filtration of one module is read in two different base rings.

## Main results

* `Crystalline.bijective_reduceModIdeal_iff` — the elementwise reading of levelwise bijectivity.
* `Crystalline.bijective_reduceModIdeal_of_mem_iff` — transfer of levelwise bijectivity between
  two submodule structures with the same underlying sets.
* `Crystalline.map_bijective_of_reduceModIdeal_eventually` — bijectivity of the completed map from
  bijectivity of the reductions at all levels beyond a cutoff.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public section

namespace Crystalline

universe u v w

section Levelwise

variable {R : Type u} [CommRing R] {X : Type v} [AddCommGroup X] [Module R X]
  {Y : Type w} [AddCommGroup Y] [Module R Y]

/-- **Levelwise bijectivity, read elementwise.**  The reduction of `f` modulo `I` is bijective
exactly when every element of `Y` agrees with a value of `f` modulo `I · Y`, and every element of
`X` whose value lies in `I · Y` already lies in `I · X`. -/
theorem bijective_reduceModIdeal_iff (I : Ideal R) (f : X →ₗ[R] Y) :
    Function.Bijective (f.reduceModIdeal I) ↔
      ((∀ y : Y, ∃ x : X, y - f x ∈ I • (⊤ : Submodule R Y)) ∧
        ∀ x : X, f x ∈ I • (⊤ : Submodule R Y) → x ∈ I • (⊤ : Submodule R X)) := by
  refine ⟨fun h ↦ ⟨fun y ↦ ?_, fun x hx ↦ ?_⟩,
    fun ⟨hsurj, hinj⟩ ↦ ⟨fun q q' hqq' ↦ ?_, fun q ↦ ?_⟩⟩
  · obtain ⟨q, hq⟩ := h.surjective (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R Y)) y)
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R X)) q
    rw [Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply] at hq
    exact ⟨x, (Submodule.Quotient.eq _).mp hq.symm⟩
  · have hx' : f.reduceModIdeal I (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R X)) x) =
        f.reduceModIdeal I (Submodule.Quotient.mk (p := (I • ⊤ : Submodule R X)) 0) := by
      rw [LinearMap.reduceModIdeal_apply, LinearMap.reduceModIdeal_apply, map_zero]
      exact (Submodule.Quotient.eq _).mpr (by simpa using hx)
    simpa using (Submodule.Quotient.eq _).mp (h.injective hx')
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R X)) q
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R X)) q'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply,
      LinearMap.reduceModIdeal_apply, Submodule.Quotient.eq] at hqq'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hinj _ (by rwa [map_sub])
  · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R Y)) q
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨Submodule.Quotient.mk (p := (I • ⊤ : Submodule R X)) x, ?_⟩
    rw [Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply, Submodule.Quotient.eq]
    simpa using neg_mem hx

/-- **Levelwise bijectivity only depends on the underlying sets of the two levels.**  Stated as a
transfer between two ideals whose level submodules have the same members, which is the situation of
the `p`-adic filtration read in two different base rings. -/
theorem bijective_reduceModIdeal_of_mem_iff {I J : Ideal R} (f : X →ₗ[R] Y)
    (hX : ∀ x : X, x ∈ I • (⊤ : Submodule R X) ↔ x ∈ J • (⊤ : Submodule R X))
    (hY : ∀ y : Y, y ∈ I • (⊤ : Submodule R Y) ↔ y ∈ J • (⊤ : Submodule R Y))
    (h : Function.Bijective (f.reduceModIdeal I)) :
    Function.Bijective (f.reduceModIdeal J) := by
  rw [bijective_reduceModIdeal_iff] at h ⊢
  exact ⟨fun y ↦ (h.1 y).imp fun x hx ↦ (hY _).mp hx,
    fun x hx ↦ (hX x).mp (h.2 x ((hY _).mpr hx))⟩

end Levelwise

section Completion

variable {R : Type u} [CommRing R] {X Y : Type v} [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y]

private theorem transitionMap_apply_transitionMap (I : Ideal R) {i j k : ℕ} (h : i ≤ j)
    (h' : j ≤ k) (x : X ⧸ I ^ k • (⊤ : Submodule R X)) :
    AdicCompletion.transitionMap I X h (AdicCompletion.transitionMap I X h' x) =
      AdicCompletion.transitionMap I X (h.trans h') x := by
  induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- Reducing modulo a lower power of `I` commutes with the transition maps. -/
private theorem reduceModIdeal_transitionMap (I : Ideal R) (f : X →ₗ[R] Y) {m n : ℕ} (h : m ≤ n)
    (x : X ⧸ I ^ n • (⊤ : Submodule R X)) :
    f.reduceModIdeal (I ^ m) (AdicCompletion.transitionMap I X h x) =
      AdicCompletion.transitionMap I Y h (f.reduceModIdeal (I ^ n) x) :=
  (LinearMap.congr_fun (AdicCompletion.transitionMap_comp_reduceModIdeal I f h) x).symm

/-- **The completion of a map which is bijective at every deep enough level is bijective.**  Only
the levels `N ≤ n` are used: a level below `N` is the image of the level `N + n` under a transition
map, and `AdicCompletion.map` commutes with the transitions. -/
theorem map_bijective_of_reduceModIdeal_eventually (I : Ideal R) (f : X →ₗ[R] Y) (N : ℕ)
    (hf : ∀ n : ℕ, N ≤ n → Function.Bijective (f.reduceModIdeal (I ^ n))) :
    Function.Bijective (AdicCompletion.map I f) := by
  refine ⟨fun x y hxy ↦ AdicCompletion.ext fun n ↦ ?_, fun y ↦ ?_⟩
  · have hdeep : x.val (N + n) = y.val (N + n) :=
      (hf (N + n) (Nat.le_add_right N n)).injective
        (congrArg (fun z : AdicCompletion I Y => z.val (N + n)) hxy)
    rw [← x.property (Nat.le_add_left n N), ← y.property (Nat.le_add_left n N), hdeep]
  choose x hx using fun n : ℕ =>
    (hf (N + n) (Nat.le_add_right N n)).surjective (y.val (N + n))
  have hstep : ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap I X (Nat.add_le_add_left h N) (x n) = x m := by
    intro m n h
    apply (hf (N + m) (Nat.le_add_right N m)).injective
    rw [reduceModIdeal_transitionMap, hx, y.property, hx]
  refine ⟨⟨fun n => AdicCompletion.transitionMap I X (Nat.le_add_left n N) (x n), ?_⟩, ?_⟩
  · intro m n h
    dsimp only
    rw [transitionMap_apply_transitionMap, ← hstep h, transitionMap_apply_transitionMap]
  · refine AdicCompletion.ext fun n ↦ ?_
    change f.reduceModIdeal (I ^ n)
      (AdicCompletion.transitionMap I X (Nat.le_add_left n N) (x n)) = y.val n
    rw [reduceModIdeal_transitionMap, hx, y.property]

end Completion

end Crystalline

end
