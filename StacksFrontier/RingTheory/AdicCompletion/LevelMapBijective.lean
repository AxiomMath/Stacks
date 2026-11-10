module

public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality
public import StacksFrontier.RingTheory.AdicCompletion.LevelwiseBijective

/-!
# Bijectivity of a `p`-adically completed additive map

`Crystalline.PAdicCompletion.levelMap` reduces an additive map modulo `pⁿ`.  Its source and its
target are modules over two possibly unrelated rings, because the level `pⁿ · X` is cut out by the
integer `pⁿ` (`Crystalline.PAdicCompletion.mem_pow_smul_top_iff`); for the same reason bijectivity
of the reduction has a reading that mentions no ring at all:

* every `y` in the target is `f x + pⁿ · y'` for some `x` and `y'`;
* every `x` with `f x` divisible by `pⁿ` is itself divisible by `pⁿ`.

That reading is what makes the notion usable in a chain of maps whose intermediate modules live
over different rings — the situation of a comparison between a ring and its completion — and it
is why the elementary closure properties below hold: composition, cancellation of a left factor,
and the fact that an additive bijection is bijective at every level.

Finally, bijectivity at all levels beyond a cutoff makes the completed map
`Crystalline.PAdicCompletion.mapAddHom` bijective.  The cutoff is needed because the comparison of
[Stacks, Lemma 60.20.1, Tag 07KK] identifies divided power differentials modulo `pⁿ` only once
`pⁿ` lies in the divided power ideal and is stable under its divided powers.

## Main results

* `Crystalline.PAdicCompletion.bijective_levelMap_iff` — the ring-free reading.
* `Crystalline.PAdicCompletion.levelMap_comp`, `bijective_levelMap_comp`,
  `bijective_levelMap_of_comp_left` — functoriality and cancellation.
* `Crystalline.PAdicCompletion.bijective_levelMap_of_bijective` — an additive bijection.
* `Crystalline.PAdicCompletion.bijective_levelMap_of_reduceModIdeal` — the linear reduction over
  one ring gives the additive reduction across two.
* `Crystalline.PAdicCompletion.bijective_mapAddHom_of_levelMap` — the completed map is bijective.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public section

open DividedPowers

universe u u' u'' v w t

namespace Crystalline

namespace PAdicCompletion

variable (p : ℕ) (R : Type u) [CommRing R] (S : Type u') [CommRing S]
  {X : Type v} [AddCommGroup X] [Module R X] {Y : Type w} [AddCommGroup Y] [Module S Y]

/-- Two elements have the same class modulo `pⁿ • ⊤` iff they differ by a multiple of `pⁿ`. -/
private theorem quotient_mk_eq_iff_pow_smul (n : ℕ) {A : Type*} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] (x x' : M) :
    (Submodule.Quotient.mk (p := (pAdicIdeal (A := A) p ^ n • ⊤ : Submodule A M)) x =
        Submodule.Quotient.mk (p := (pAdicIdeal (A := A) p ^ n • ⊤ : Submodule A M)) x') ↔
      ∃ w : M, x - x' = (p ^ n : ℕ) • w :=
  (Submodule.Quotient.eq _).trans (mem_pow_smul_top_iff p A n _)

/-- **Bijectivity of the level-`pⁿ` reduction, read without reference to either base ring.** -/
theorem bijective_levelMap_iff (f : X →+ Y) (n : ℕ) :
    Function.Bijective (levelMap p R S f n) ↔
      ((∀ y : Y, ∃ (x : X) (z : Y), y - f x = (p ^ n : ℕ) • z) ∧
        ∀ x : X, (∃ z : Y, f x = (p ^ n : ℕ) • z) → ∃ w : X, x = (p ^ n : ℕ) • w) := by
  have hX := quotient_mk_eq_iff_pow_smul p n (A := R) (M := X)
  have hY := quotient_mk_eq_iff_pow_smul p n (A := S) (M := Y)
  constructor
  · intro h
    refine ⟨fun y ↦ ?_, fun x hx ↦ ?_⟩
    · obtain ⟨q, hq⟩ := h.surjective (Submodule.Quotient.mk
        (p := (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S Y)) y)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
        (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X) q
      rw [levelMap_mk] at hq
      exact ⟨x, (hY y (f x)).mp hq.symm⟩
    · obtain ⟨z, hz⟩ := hx
      have h0 : levelMap p R S f n (Submodule.Quotient.mk
            (p := (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X)) x) =
          levelMap p R S f n (Submodule.Quotient.mk
            (p := (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X)) 0) := by
        rw [levelMap_mk, levelMap_mk, map_zero]
        exact (hY (f x) 0).mpr ⟨z, by rw [sub_zero, hz]⟩
      obtain ⟨w, hw⟩ := (hX x 0).mp (h.injective h0)
      exact ⟨w, by rw [← hw, sub_zero]⟩
  · rintro ⟨hsurj, hinj⟩
    constructor
    · intro q q' hqq'
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
        (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X) q
      obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective
        (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X) q'
      rw [levelMap_mk, levelMap_mk, hY] at hqq'
      obtain ⟨z, hz⟩ := hqq'
      exact (hX x x').mpr (hinj (x - x') ⟨z, by rwa [map_sub]⟩)
    · intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
        (pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S Y) q
      obtain ⟨x, z, hz⟩ := hsurj y
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [levelMap_mk]
      refine (hY (f x) y).mpr ⟨-z, ?_⟩
      rw [smul_neg, ← hz]
      abel

/-- An additive bijection is bijective at every level. -/
theorem bijective_levelMap_of_bijective (f : X →+ Y) (hf : Function.Bijective f) (n : ℕ) :
    Function.Bijective (levelMap p R S f n) := by
  obtain ⟨g, hgf, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  rw [bijective_levelMap_iff]
  refine ⟨fun y ↦ ⟨g y, 0, by rw [hfg y, sub_self, smul_zero]⟩, fun x hx ↦ ?_⟩
  obtain ⟨z, hz⟩ := hx
  refine ⟨g z, hf.injective ?_⟩
  rw [hz, map_nsmul, hfg z]

/-- The level-`pⁿ` reduction of a composite is the composite of the reductions. -/
theorem levelMap_comp (T : Type u'') [CommRing T] {Z : Type t} [AddCommGroup Z] [Module T Z]
    (f : X →+ Y) (g : Y →+ Z) (n : ℕ) :
    levelMap p R T (g.comp f) n = (levelMap p S T g n).comp (levelMap p R S f n) := by
  refine AddMonoidHom.ext fun q ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X) q
  simp only [levelMap_mk, AddMonoidHom.comp_apply]

/-- Levelwise bijectivity is closed under composition. -/
theorem bijective_levelMap_comp (T : Type u'') [CommRing T] {Z : Type t} [AddCommGroup Z]
    [Module T Z] (f : X →+ Y) (g : Y →+ Z) (n : ℕ)
    (hf : Function.Bijective (levelMap p R S f n))
    (hg : Function.Bijective (levelMap p S T g n)) :
    Function.Bijective (levelMap p R T (g.comp f) n) := by
  rw [levelMap_comp p R S T f g n]
  exact hg.comp hf

/-- **Cancellation of a right factor.**  If `f` and `g ∘ f` are bijective at level `pⁿ`, so is
`g`.  Surjectivity of `g` is immediate; for the kernel statement, `t` differs from a value of `f`
by a multiple of `pⁿ`, and then the kernel statement for `g ∘ f` applies. -/
theorem bijective_levelMap_of_comp_left (T : Type u'') [CommRing T] {Z : Type t} [AddCommGroup Z]
    [Module T Z] (f : X →+ Y) (g : Y →+ Z) (n : ℕ)
    (hf : Function.Bijective (levelMap p R S f n))
    (hgf : Function.Bijective (levelMap p R T (g.comp f) n)) :
    Function.Bijective (levelMap p S T g n) := by
  rw [bijective_levelMap_iff] at hf hgf ⊢
  refine ⟨fun z ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨x, w, hw⟩ := hgf.1 z
    exact ⟨f x, w, hw⟩
  · obtain ⟨z, hz⟩ := hy
    obtain ⟨x, s, hs⟩ := hf.1 y
    have hgfx : (g.comp f) x = (p ^ n : ℕ) • (z - g s) := by
      have hy' : y = f x + (p ^ n : ℕ) • s := by
        rw [← hs]
        abel
      have : g y = g (f x) + (p ^ n : ℕ) • g s := by
        rw [hy', map_add, map_nsmul]
      rw [smul_sub, ← hz, this]
      abel
    obtain ⟨u, hu⟩ := hgf.2 x ⟨z - g s, hgfx⟩
    refine ⟨f u + s, ?_⟩
    rw [smul_add, ← map_nsmul, ← hu, ← hs]
    abel

/-- Bijectivity of the linear reduction modulo `(p)ⁿ`, read without reference to the base ring. -/
private theorem bijective_reduceModIdeal_pow_iff {Y' : Type w} [AddCommGroup Y'] [Module R Y']
    (f : X →ₗ[R] Y') (n : ℕ) :
    Function.Bijective (f.reduceModIdeal (pAdicIdeal (A := R) p ^ n)) ↔
      ((∀ y : Y', ∃ (x : X) (z : Y'), y - f x = (p ^ n : ℕ) • z) ∧
        ∀ x : X, (∃ z : Y', f x = (p ^ n : ℕ) • z) → ∃ w : X, x = (p ^ n : ℕ) • w) := by
  simp only [bijective_reduceModIdeal_iff, mem_pow_smul_top_iff p R n, forall_exists_index]

/-- The linear reduction modulo `(p)ⁿ` of a linear map gives its additive reduction, read with any
base ring on the target. -/
theorem bijective_levelMap_of_reduceModIdeal {Y' : Type w} [AddCommGroup Y'] [Module R Y']
    (f : X →ₗ[R] Y') (n : ℕ)
    (h : Function.Bijective (f.reduceModIdeal (pAdicIdeal (A := R) p ^ n)))
    (S' : Type u'') [CommRing S'] [Module S' Y'] :
    Function.Bijective (levelMap p R S' f.toAddMonoidHom n) := by
  exact (bijective_levelMap_iff p R S' f.toAddMonoidHom n).mpr
    ((bijective_reduceModIdeal_pow_iff p R f n).mp h)

/-- Levelwise bijectivity does not depend on the base rings the two levels are read in. -/
theorem bijective_levelMap_congr (R' : Type u) [CommRing R'] [Module R' X]
    (S' : Type u') [CommRing S'] [Module S' Y] (f : X →+ Y) (n : ℕ)
    (h : Function.Bijective (levelMap p R S f n)) :
    Function.Bijective (levelMap p R' S' f n) := by
  rw [bijective_levelMap_iff] at h ⊢
  exact h

/-- Conversely to `Crystalline.PAdicCompletion.bijective_levelMap_of_reduceModIdeal`, the additive
reduction gives the linear one. -/
theorem bijective_reduceModIdeal_of_levelMap {Y' : Type w} [AddCommGroup Y'] [Module R Y']
    (f : X →ₗ[R] Y') (n : ℕ) (S' : Type u'') [CommRing S'] [Module S' Y']
    (h : Function.Bijective (levelMap p R S' f.toAddMonoidHom n)) :
    Function.Bijective (f.reduceModIdeal (pAdicIdeal (A := R) p ^ n)) := by
  exact (bijective_reduceModIdeal_pow_iff p R f n).mpr
    ((bijective_levelMap_iff p R S' f.toAddMonoidHom n).mp h)

/-- The transition maps commute with the level reductions. -/
theorem transitionMap_levelMap (f : X →+ Y) {m n : ℕ} (hmn : m ≤ n)
    (q : X ⧸ (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X)) :
    AdicCompletion.transitionMap (pAdicIdeal (A := S) p) Y hmn (levelMap p R S f n q) =
      levelMap p R S f m (AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X hmn q) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X) q
  rw [levelMap_mk, transitionMap_mk, transitionMap_mk, levelMap_mk]

/-- **The `p`-adic completion of an additive map which is bijective at every level beyond a
cutoff is bijective.** -/
theorem bijective_mapAddHom_of_levelMap (f : X →+ Y) (N : ℕ)
    (hf : ∀ n : ℕ, N ≤ n → Function.Bijective (levelMap p R S f n)) :
    Function.Bijective (mapAddHom p R S f) := by
  constructor
  · intro z w hzw
    refine AdicCompletion.ext fun n ↦ ?_
    have hdeep : z.val (N + n) = w.val (N + n) :=
      (hf (N + n) (Nat.le_add_right N n)).injective
        (congrArg (fun u : AdicCompletion (pAdicIdeal (A := S) p) Y => u.val (N + n)) hzw)
    rw [← z.property (Nat.le_add_left n N), ← w.property (Nat.le_add_left n N), hdeep]
  · intro w
    choose u hu using fun n : ℕ =>
      (hf (N + n) (Nat.le_add_right N n)).surjective (w.val (N + n))
    have hstep : ∀ {m n : ℕ} (h : m ≤ n),
        AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X
          (Nat.add_le_add_left h N) (u n) = u m := by
      intro m n h
      apply (hf (N + m) (Nat.le_add_right N m)).injective
      rw [← transitionMap_levelMap p R S f (Nat.add_le_add_left h N) (u n), hu,
        w.property, hu]
    refine ⟨⟨fun n => AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X
      (Nat.le_add_left n N) (u n), ?_⟩, ?_⟩
    · intro m n h
      dsimp only
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective
        (pAdicIdeal (A := R) p ^ (N + n) • ⊤ : Submodule R X) (u n)
      have h1 : AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X h
          (AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X
            (Nat.le_add_left n N) (u n)) =
          AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X
            (Nat.le_add_left m N) (AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X
              (Nat.add_le_add_left h N) (u n)) := by
        rw [← hx, transitionMap_mk, transitionMap_mk, transitionMap_mk, transitionMap_mk]
      rw [h1, hstep h]
    · refine AdicCompletion.ext fun n ↦ ?_
      change levelMap p R S f n (AdicCompletion.transitionMap (pAdicIdeal (A := R) p) X
        (Nat.le_add_left n N) (u n)) = w.val n
      rw [← transitionMap_levelMap p R S f (Nat.le_add_left n N) (u n), hu, w.property]

end PAdicCompletion

end Crystalline

end
