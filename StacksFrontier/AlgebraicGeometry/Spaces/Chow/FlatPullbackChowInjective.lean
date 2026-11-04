module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FlatPullbackChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingTower

/-!
# Injectivity of flat pullback on Chow homology

In Situation 0EDT let `f : X ⟶ Y` be a flat morphism of relative dimension `r` of good algebraic
spaces over `B`. If a `k`-cycle on `Y` whose flat pullback is rationally equivalent to zero on `X`
is itself rationally equivalent to zero, for every `k`, then the flat pullback
`f^* : CH_*(Y) ⟶ CH_*(X)` on Chow homology is injective. This is the form in which the splitting
principle (Stacks 0ESC) is used: an identity between operations on `CH_*(X)` intertwined by `f^*`
with operations on `CH_*(Y)` descends from `Y` to `X`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.gradedChowMap_apply_add`: the components of the image
  under a homogeneous homomorphism.
* `AlgebraicGeometry.Space.PrivateChern.gradedChowMap_injective`: a homogeneous homomorphism of
  Chow homologies with injective components is injective.
* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow_injective`: flat pullback on Chow
  homology is injective when flat pullback of cycles reflects rational equivalence.

## References

* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space.PrivateChern

variable (D : BaseSpaceDimensionSituation.{u}) {X Y : D.Ambient}

/-- The component of degree `k + s` of the image of `α` under a homogeneous homomorphism of degree
`s` is the image of the component of degree `k`. -/
theorem gradedChowMap_apply_add (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (s : ℤ)
    (φ : ∀ k : ℤ, chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY (k + s))
    (α : chowHomology.{u, v} D sX hX) (k : ℤ) :
    gradedChowMap.{u, v} D sX hX sY hY s φ α (k + s) = φ k (α k) := by
  classical
  induction α using DirectSum.induction_on with
  | zero => simp
  | of j a =>
    rw [gradedChowMap_of]
    by_cases hj : j = k
    · subst hj
      simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega : k + s ≠ j + s),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj), map_zero]
  | add a b ha hb => simp only [map_add, DirectSum.add_apply, ha, hb]

/-- **A homogeneous homomorphism of Chow homologies with injective components is injective.** -/
theorem gradedChowMap_injective (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (s : ℤ)
    (φ : ∀ k : ℤ, chowGroup.{v} D sX hX k →+ chowGroup.{v} D sY hY (k + s))
    (hφ : ∀ k, Function.Injective (φ k)) :
    Function.Injective (gradedChowMap.{u, v} D sX hX sY hY s φ) := by
  rw [injective_iff_map_eq_zero]
  intro α hα
  ext k
  have h := congrArg (fun β : chowHomology.{u, v} D sY hY => β (k + s)) hα
  simp only [DirectSum.zero_apply, gradedChowMap_apply_add] at h ⊢
  exact hφ k (h.trans (map_zero (φ k)).symm)

/-- **Flat pullback on Chow homology is injective** when flat pullback of cycles reflects
rational equivalence: `f^* : CH_*(Y) ⟶ CH_*(X)` for a flat morphism `f : X ⟶ Y` of relative
dimension `r` such that a cycle on `Y` whose pullback is rationally equivalent to zero is itself
rationally equivalent to zero. -/
theorem flatPullbackChow_injective (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (h : FlatPullbackReflectsRationalEquivalence.{max v (u + 1)} D sX hX sY hY f hbase r hflat
      hr) :
    Function.Injective (flatPullbackChow.{u, max v (u + 1)} D sX hX sY hY f hbase r hflat hr) := by
  refine gradedChowMap_injective.{u, max v (u + 1)} D sY hY sX hX r _ fun k => ?_
  rw [injective_iff_map_eq_zero]
  intro α hα
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
  change chowDescend.{u, max v (u + 1)} D sY hY sX hX _ (chowClass D sY hY k a) = 0 at hα
  rw [chowDescend_chowClass _ _ _ _ _ _
    (respectsRationalEquivalence_flatPullbackMap.{u, v} D sX hX sY hY f hbase r hflat hr k),
    chowClass_eq_zero_iff] at hα
  exact (chowClass_eq_zero_iff _ _ _ _ _).2 (h k (k + r) rfl a hα)

end AlgebraicGeometry.Space.PrivateChern

end
