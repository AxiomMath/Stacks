module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Map

/-!
# The two spellings of the projective space bundle map

The projective space bundle formula [Stacks, Tag 02TX] and the operation of [Stacks, Tag 02TW]
are written in this repository in two ways. The Chern class material of
`StacksDraft.AlgebraicGeometry.Chow.ChernClassHigher` indexes the bundle by its rank `r` and
reads the map through `Stacks.Chow.projectiveBundleChernTerm`, landing in degree
`k + (r - 1) - r`; the projective space bundle formula itself is proved in
`StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Map` for the fibre dimension `n`,
through `Stacks.Chow.bundleTerm`, `Stacks.Chow.bundleMap` and `Stacks.Chow.bundleProjection`.
This file identifies the two at `r = n + 1`, so that the projective space bundle formula in the
second spelling discharges the hypotheses `Stacks.Chow.ProjectiveBundleRelationInjective` and
`Stacks.Chow.ProjectiveBundleRelationSurjective` of the first.

## Main results

* `Stacks.Chow.projectiveBundleChernTerm_eq_bundleTerm` — each summand of the relation of Stacks
  02U6 is a summand of the map of Stacks 02TX, up to transport along equalities of degrees.
* `Stacks.Chow.projectiveBundleRelationInjective_of_bundleMap` and
  `Stacks.Chow.projectiveBundleRelationSurjective_of_bundleMap` — the two halves of Stacks 02TX in
  the first spelling, from the same halves in the second.
* `Stacks.Chow.projectiveBundleProjection_eq_bundleProjection` — the two spellings of the
  operation of Stacks 02TW agree.
* `Stacks.Chow.projectiveBundleProjection_top_of_bundleProjection` — the top half of Stacks 02TW
  in the first spelling, from the same statement in the second.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (n + 1 - 1) hπ k)
  (ξ : ChernCapOperator C sP)

/-- Flat pullback along `π` commutes with transport along an equality of degrees. -/
theorem bundlePullback_chowGroupCast {a b : ℤ} (e : a = b) (z : chowGroup C sX a) :
    bundlePullback C sX sP π hsP n hπ b (chowGroupCast C sX e z) =
      chowGroupCast C sP (by rw [e]) (bundlePullback C sX sP π hsP n hπ a z) := by
  subst e; rfl

/-- **Each summand of the relation of Stacks 02U6 is a summand of the map of Stacks 02TX.** For
the bundle of rank `n + 1`, the summand `c₁^i ∩ π^*(-)` of degree `k - (n + 1 - i)` of
`Stacks.Chow.projectiveBundleChernTerm` is the summand `Stacks.Chow.bundleTerm` in base degree
`k - (n + 1)`, up to transport along equalities of degrees. -/
theorem projectiveBundleChernTerm_eq_bundleTerm (k : ℤ) (i : ℕ) (hi : i ≤ n + 1)
    (x : chowGroup C sX (k - ((n + 1 - i : ℕ) : ℤ))) :
    projectiveBundleChernTerm C sX sP π hsP (n + 1) hπ hfac ξ k i hi x =
      chowGroupCast C sP (by push_cast [Nat.cast_sub hi]; ring)
        (bundleTerm C sX sP π hsP n hπ ξ (k - ((n + 1 : ℕ) : ℤ)) i
          (chowGroupCast C sX (by push_cast [Nat.cast_sub hi]; ring) x)) := by
  simp only [projectiveBundleChernTerm, bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [bundlePullback_chowGroupCast, chowGroupCast_capPow, capPow_cast,
    ← capPow_eq_iteratedChernCapOnChow, capPow_cast]
  rfl

/-- **The map of the relation of Stacks 02U6 is the map of Stacks 02TX**, up to transport along
equalities of degrees: the sum of the first `n + 1` summands of the relation, in degree `k`, is
`Stacks.Chow.bundleMap` in base degree `k - (n + 1)` applied to the transported family. -/
theorem sum_projectiveBundleChernTerm_eq_bundleMap (k : ℤ)
    (β : ∀ i : Fin (n + 1), chowGroup C sX (k - ((n + 1 - i.val : ℕ) : ℤ))) :
    ∑ i : Fin (n + 1), projectiveBundleChernTerm C sX sP π hsP (n + 1) hπ hfac ξ k i.val
        i.isLt.le (β i) =
      chowGroupCast C sP (by push_cast; ring)
        (bundleMap C sX sP π hsP n hπ ξ (k - ((n + 1 : ℕ) : ℤ))
          fun i ↦ chowGroupCast C sX (by push_cast [Nat.cast_sub i.isLt.le]; ring) (β i)) := by
  rw [bundleMap_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    projectiveBundleChernTerm_eq_bundleTerm C sX sP π hsP n hπ hfac ξ k i.val i.isLt.le (β i)

/-- **Stacks 02TX, injectivity, in the spelling of the Chern class material**, from injectivity
of `Stacks.Chow.bundleMap` in every degree. -/
theorem projectiveBundleRelationInjective_of_bundleMap
    (h : ∀ k : ℤ, Function.Injective (bundleMap C sX sP π hsP n hπ ξ k)) :
    ProjectiveBundleRelationInjective C sX sP π hsP (n + 1) hπ hfac ξ := by
  intro k β γ hβγ
  have hβγ' := hβγ
  simp only [sum_projectiveBundleChernTerm_eq_bundleMap] at hβγ'
  have hfam := h _ ((chowGroupCast C sP _).injective hβγ')
  funext i
  exact (chowGroupCast C sX _).injective (congrFun hfam i)

/-- **Stacks 02TX, surjectivity, in the spelling of the Chern class material**, from surjectivity
of `Stacks.Chow.bundleMap` in every degree. -/
theorem projectiveBundleRelationSurjective_of_bundleMap
    (h : ∀ k : ℤ, Function.Surjective (bundleMap C sX sP π hsP n hπ ξ k)) :
    ProjectiveBundleRelationSurjective C sX sP π hsP (n + 1) hπ hfac ξ := by
  intro k y
  obtain ⟨β, hβ⟩ := h (k - ((n + 1 : ℕ) : ℤ))
    ((chowGroupCast C sP (show k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) =
      k - ((n + 1 : ℕ) : ℤ) + (n : ℤ) by push_cast; ring)) y)
  refine ⟨fun i ↦ (chowGroupCast C sX
    (show k - ((n + 1 - i.val : ℕ) : ℤ) = k - ((n + 1 : ℕ) : ℤ) + (i.val : ℤ) by
      push_cast [Nat.cast_sub i.isLt.le]; ring)).symm (β i), ?_⟩
  change ∑ i : Fin (n + 1), _ = y
  rw [sum_projectiveBundleChernTerm_eq_bundleMap]
  simp only [AddEquiv.apply_symm_apply]
  rw [hβ, chowGroupCast_chowGroupCast, chowGroupCast_rfl]

/-- **The two spellings of the operation of Stacks 02TW agree**:
`Stacks.Chow.projectiveBundleProjection` for the bundle of rank `n + 1` is
`Stacks.Chow.bundleProjection` for fibre dimension `n`. -/
theorem projectiveBundleProjection_eq_bundleProjection [IsProper π] (s : ℕ) (k : ℤ)
    (x : chowGroup C sX k) :
    projectiveBundleProjection C sX sP π hsP (n + 1) hπ hfac ξ s k x =
      bundleProjection C sX sP π hsP n hπ ξ s k (k + ((n + 1 - 1 : ℕ) : ℤ) - (s : ℤ))
        (by push_cast; ring) x := by
  simp only [projectiveBundleProjection, bundleProjection, AddMonoidHom.coe_comp,
    Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [← capPow_eq_iteratedChernCapOnChow, capPow_cast]
  rfl

/-- `Stacks.Chow.bundleProjection` is unchanged by transporting its target degree. -/
theorem bundleProjection_congr_target [IsProper π] (s : ℕ) (k : ℤ) {m m' : ℤ}
    (h : k + n = m + s) (e : m = m') (x : chowGroup C sX k) :
    bundleProjection C sX sP π hsP n hπ ξ s k m' (e ▸ h) x =
      chowGroupCast C sX e (bundleProjection C sX sP π hsP n hπ ξ s k m h x) := by
  subst e; rfl

/-- **The top half of Stacks 02TW in the spelling of the Chern class material**, from the same
statement for `Stacks.Chow.bundleProjection`: `π_*(c₁^{r-1} ∩ π^*β) = β` for the bundle of rank
`r = n + 1`. -/
theorem projectiveBundleProjection_top_of_bundleProjection [IsProper π]
    (htop : ∀ (k : ℤ) (β : chowGroup C sX k),
      bundleProjection C sX sP π hsP n hπ ξ n k k (by ring) β = β) (k : ℤ)
    (β : chowGroup C sX k) :
    projectiveBundleProjection C sX sP π hsP (n + 1) hπ hfac ξ (n + 1 - 1) k β =
      chowGroupCast C sX (by omega) β := by
  rw [projectiveBundleProjection_eq_bundleProjection]
  have h := bundleProjection_congr_target C sX sP π hsP n hπ ξ n k (by ring)
    (show k = k + ((n + 1 - 1 : ℕ) : ℤ) - ((n + 1 - 1 : ℕ) : ℤ) by ring) β
  rw [htop] at h
  exact h

end Stacks.Chow

end
