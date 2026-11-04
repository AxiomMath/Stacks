module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap

/-!
# Injectivity of the pullback to a projective bundle, and the first Chern class in rank one

Two consequences of the top half of [Stacks, Tag 02TW], `π_*(c₁(𝒪_P(1))^{r-1} ∩ π^*β) = β`:

* the flat pullback `π^* : CH_k(X) ⟶ CH_{k+r-1}(P)` is injective, which is what lets an identity
  between Chern classes be checked after pulling back to a projective bundle;
* for a module `ℒ` of rank one, whose twist `𝒪_P(1)` caps like `π^*ℒ`, the first Chern class
  `π_*(c₁(𝒪_P(1)) ∩ π^*α)` of
  `Stacks.Chow.chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily`
  is `c₁(ℒ) ∩ α`. This is the first Chern class part of [Stacks, Tag 02U2].

## Main results

* `Stacks.Chow.projectiveBundlePullback_injective`.
* `Stacks.Chow.projectiveBundleProjection_one_eq_of_rank_one`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [Flat π] [IsProper π]
  (hsP : π ≫ sX = sP) (twist : ChernCapOperator C sP)

section

variable (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)

/-- **The pullback to a projective bundle is injective** on Chow groups, granted the top half of
Stacks 02TW: `β = π_*(c₁(𝒪_P(1))^{r-1} ∩ π^*β)` is recovered from `π^*β`. -/
theorem projectiveBundlePullback_injective
    (htop : ∀ (k : ℤ) (β : chowGroup C sX k),
      projectiveBundleProjection C sX sP π hsP r hπ hfac twist (r - 1) k β =
        chowGroupCast C sX (by omega) β) (k : ℤ) :
    Function.Injective (projectiveBundlePullback C sX sP π hsP r hπ hfac k) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro β hβ
  have h := htop k β
  simp only [projectiveBundleProjection, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, (AddMonoidHom.mem_ker).1 hβ, map_zero] at h
  exact (AddSubgroup.mem_bot).2 ((chowGroupCast C sX _).injective (h.symm.trans (map_zero _).symm))

end

variable (hπ : AlgebraicGeometry.RelativeDimension π (1 - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (1 - 1) hπ k)

/-- **The first Chern class in rank one.** If the twist of a bundle of fibre dimension zero caps
pulled-back classes like a pullback of the operation `cap` — as `c₁(𝒪_P(1)) = c₁(π^*ℒ)` does for
`𝒪_P(1) ≅ π^*ℒ`, by Stacks 02SS — then `π_*(c₁(𝒪_P(1)) ∩ π^*α) = cap(α)`. -/
theorem projectiveBundleProjection_one_eq_of_rank_one
    (htop : ∀ (k : ℤ) (β : chowGroup C sX k),
      projectiveBundleProjection C sX sP π hsP 1 hπ hfac twist 0 k β =
        chowGroupCast C sX (by omega) β)
    (cap : ∀ d : ℤ, chowGroup C sX (d + 1) →+ chowGroup C sX d)
    (hξ : ∀ (k : ℤ) (α : chowGroup C sX k) (d : ℤ) (_ : d + 1 = k + ((1 - 1 : ℕ) : ℤ))
      (y : chowGroup C sP (d + 1))
      (_ : y ≍ projectiveBundlePullback C sX sP π hsP 1 hπ hfac k α),
      twist.capOnChow C sP d y ≍
        projectiveBundlePullback C sX sP π hsP 1 hπ hfac (k - 1)
          (cap (k - 1) (chowGroupCast C sX (by omega) α)))
    (k : ℤ) (α : chowGroup C sX k) :
    projectiveBundleProjection C sX sP π hsP 1 hπ hfac twist 1 k α =
      chowGroupCast C sX (by omega) (cap (k - 1) (chowGroupCast C sX (by omega) α)) := by
  set v := cap (k - 1) (chowGroupCast C sX (by omega) α) with hv
  have h0 := htop (k - 1) v
  refine chowGroup_eq_of_heq C sX ?_
  refine HEq.trans ?_ ((heq_of_eq h0).trans ((chowGroupCast_heq C sX _ _).trans
    (chowGroupCast_heq C sX _ _).symm))
  simp only [projectiveBundleProjection, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  refine properChowPushforward_heq C sP sX π hsP (by omega) ?_
  set x := chowGroupCast C sP (show k + ((1 - 1 : ℕ) : ℤ) =
      k + ((1 - 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) + ((List.replicate 1 twist).length : ℤ) by simp)
    (projectiveBundlePullback C sX sP π hsP 1 hπ hfac k α) with hx
  have hx' : x ≍ projectiveBundlePullback C sX sP π hsP 1 hπ hfac k α :=
    chowGroupCast_heq C sP _ _
  set x₀ : chowGroup C sP (k + ((1 - 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) + 1 +
      ((List.replicate 0 twist).length : ℤ)) := chowGroupCast C sP (by simp) x with hx₀
  rw [iteratedChernCapOnChow_replicate_succ_heq C sP twist 0 _ x x₀
    (chowGroupCast_heq C sP _ x).symm]
  refine HEq.trans ?_ ((iteratedChernCapOnChow_replicate_zero_heq C sP twist _ _).trans
    (chowGroupCast_heq C sP _ _)).symm
  refine HEq.trans (capOnChow_heq C sP twist rfl (y := chowGroupCast C sP (by simp) x₀) ?_)
    (hξ k α _ (by omega) _ ?_)
  · exact (iteratedChernCapOnChow_replicate_zero_heq C sP twist _ _).trans
      (chowGroupCast_heq C sP _ _).symm
  · exact (chowGroupCast_heq C sP _ _).trans ((chowGroupCast_heq C sP _ _).trans hx')

end Stacks.Chow

end
