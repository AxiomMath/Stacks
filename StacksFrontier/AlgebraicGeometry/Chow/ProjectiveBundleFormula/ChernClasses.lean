module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bridge
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleExistence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.IntegralChernClass

/-!
# The Chern class cap products of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42, `X` locally of finite type over `S`, `ℰ` a
finite locally free `𝒪_X`-module of rank `r = n + 1` and `(π : 𝐏(ℰ) ⟶ X, 𝒪(1))` its projective
bundle. By the projective space bundle formula [Stacks, Tag 02TX] every class `α ∈ A_k(X)` has a
unique family `α_j ∈ A_{k-j}(X)`, `0 ≤ j ≤ r`, with `α_0 = α` and

  `∑_{i=0}^{r} (-1)^i c₁(𝒪(1))^i ∩ π^*α_{r-i} = 0`,

the characterization of [Stacks, Tag 02U6]; at `α = [X]` this is [Stacks, Tag 02U0].

## Main definitions

* `Stacks.Chow.IsBundleChernCapFamily` — the characterization of Stacks 02U6 on `𝐏(ℰ)`.
* `Stacks.Chow.bundleChernCapFamily` — the family `(c_j(ℰ) ∩ α)_j` of Stacks 02U6.
* `Stacks.Chow.bundleChernCap` — `c_j(ℰ) ∩ - : A_k(X) ⟶ A_{k-j}(X)`.
* `Stacks.Chow.chernClassFundamentalFamily`, `Stacks.Chow.chernClassFundamental` — the Chern
  classes `c_i(ℰ) ∩ [X]` of Stacks 02U0.

## Main results

* `Stacks.Chow.projectiveBundleRelationInjective_bundle`,
  `Stacks.Chow.projectiveBundleRelationSurjective_bundle` — Stacks 02TX for `𝐏(ℰ)` in the
  indexing of the relation of Stacks 02U6.
* `Stacks.Chow.projectiveBundleProjection_bundle_self` — the top case of Stacks 02TW for `𝐏(ℰ)`
  in the indexing of `Stacks.Chow.projectiveBundleProjection`.
* `Stacks.Chow.isChernCapFamily_bundleChernCapFamily`,
  `Stacks.Chow.eq_bundleChernCapFamily_of_isChernCapFamily` — existence and uniqueness in
  Stacks 02U6.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

section Bundle

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 02TX, injectivity**, for the projective bundle of a module of rank `n + 1`, in the
indexing of the relation of Stacks 02U6. -/
theorem projectiveBundleRelationInjective_bundle
    :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    ProjectiveBundleRelationInjective C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
      (relativeDimension_bundleProj E n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  projectiveBundleRelationInjective_of_bundleMap C sX _ _ rfl n _ _ _
    fun k ↦ (projectiveBundle_formula E n C sX k).1

/-- **Stacks 02TX, surjectivity**, for the projective bundle of a module of rank `n + 1`, in the
indexing of the relation of Stacks 02U6. -/
theorem projectiveBundleRelationSurjective_bundle
    :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    ProjectiveBundleRelationSurjective C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
      (relativeDimension_bundleProj E n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  projectiveBundleRelationSurjective_of_bundleMap C sX _ _ rfl n _ _ _
    fun k ↦ (projectiveBundle_formula E n C sX k).2

/-- **The top case of Stacks 02TW** for the projective bundle of a module of rank `n + 1`, in the
indexing of `Stacks.Chow.projectiveBundleProjection`: `π_*(c₁(𝒪(1))^n ∩ π^*β) = β`. -/
theorem projectiveBundleProjection_bundle_self (k : ℤ)
    (β : chowGroup C sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    projectiveBundleProjection C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
        (relativeDimension_bundleProj E n)
        (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
        (bundleTwistCap E C sX) (n + 1 - 1) k β =
      chowGroupCast C sX (by omega) β := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  exact projectiveBundleProjection_top_of_bundleProjection C sX _ _ rfl n _ _ _
    (projectiveBundle_projection_self E n C sX) k β

/-! ### The Chern class cap products of Stacks 02U6 -/

/-- **Stacks 02U6, the characterization**, on the projective bundle of a module `ℰ` of rank
`n + 1`: that a family `(α_j)_{0 ≤ j ≤ n + 1}`, `α_j ∈ A_{k-j}(X)`, has `α_0 = α` and satisfies
`∑_{i=0}^{n+1} (-1)^i c₁(𝒪(1))^i ∩ π^*α_{n+1-i} = 0` in the Chow group of `𝐏(ℰ)`. This is
`Stacks.Chow.IsChernCapFamily` at the projection of `𝐏(ℰ)` and the cap operator of its twist. -/
abbrev IsBundleChernCapFamily (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (n + 1 + 1), chowGroup C sX (k - (j : ℤ))) : Prop :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  IsChernCapFamily C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
    (relativeDimension_bundleProj E n)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (bundleTwistCap E C sX) k α c

/-- **Stacks 02U6.** The family `(c_j(ℰ) ∩ α)_{0 ≤ j ≤ n + 1}` of Chern class cap products of a
class `α ∈ A_k(X)` with a module `ℰ` of rank `n + 1`, the `j`-th member lying in `A_{k-j}(X)`:
the unique solution of the relation of Stacks 02U6 on the projective bundle of `ℰ` with
`α_0 = α`, whose existence and uniqueness are the two halves of Stacks 02TX. -/
def bundleChernCapFamily (k : ℤ)
    (α : chowGroup C sX k) (j : Fin (n + 1 + 1)) : chowGroup C sX (k - (j : ℤ)) :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  projectiveBundleChernCapFamily C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
      (relativeDimension_bundleProj E n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX)
    (projectiveBundleRelationSurjective_bundle E n C sX) k α j

/-- **Stacks 02U6, existence.** The family `Stacks.Chow.bundleChernCapFamily` of `α` has
`α_0 = α` and satisfies the relation `∑_{i=0}^{n+1} (-1)^i c₁(𝒪(1))^i ∩ π^*α_{n+1-i} = 0` on the
projective bundle. -/
theorem isChernCapFamily_bundleChernCapFamily
    (k : ℤ) (α : chowGroup C sX k) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    IsChernCapFamily C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
      (relativeDimension_bundleProj E n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX) k α
      (bundleChernCapFamily E n C sX k α) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  isChernCapFamily_projectiveBundleChernCapFamily C sX _ _ rfl _ _ _ _
    (projectiveBundleRelationSurjective_bundle E n C sX) k α

/-- **Stacks 02U6, uniqueness.** Every family satisfying the characterization of Stacks 02U6 for
`α` is `Stacks.Chow.bundleChernCapFamily` of `α`. -/
theorem eq_bundleChernCapFamily_of_isChernCapFamily
    (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (n + 1 + 1), chowGroup C sX (k - (j : ℤ)))
    (hc : IsBundleChernCapFamily E n C sX k α c) :
    c = bundleChernCapFamily E n C sX k α :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  eq_of_isChernCapFamily C sX _ _ rfl _ _ _ _
    (projectiveBundleRelationInjective_bundle E n C sX) k α hc
    (isChernCapFamily_bundleChernCapFamily E n C sX k α)

/-- **Stacks 02U6, the normalisation** `c_0(ℰ) ∩ α = α`. -/
theorem bundleChernCapFamily_zero
    (k : ℤ) (α : chowGroup C sX k) :
    chowGroupCast C sX (show k - ((0 : Fin (n + 1 + 1)) : ℤ) = k by simp)
      (bundleChernCapFamily E n C sX k α 0) = α :=
  (isChernCapFamily_bundleChernCapFamily E n C sX k α).1

/-- **Stacks 02U6, additivity.** The Chern class cap products are additive in the class. -/
theorem bundleChernCapFamily_add
    (k : ℤ) (α β : chowGroup C sX k) (j : Fin (n + 1 + 1)) :
    bundleChernCapFamily E n C sX k (α + β) j =
      bundleChernCapFamily E n C sX k α j + bundleChernCapFamily E n C sX k β j := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  exact congrFun (projectiveBundleChernCapFamily_add C sX _ _ rfl _ _ _ _
    (projectiveBundleRelationInjective_bundle E n C sX)
    (projectiveBundleRelationSurjective_bundle E n C sX) k α β) j

/-- **Stacks 02U6 and 02U7.** Intersection with the `j`-th Chern class of a module of rank `n + 1`
as a homomorphism of Chow groups, `c_j(ℰ) ∩ - : A_k(X) ⟶ A_{k-j}(X)`. -/
def bundleChernCap (k : ℤ)
    (j : Fin (n + 1 + 1)) : chowGroup C sX k →+ chowGroup C sX (k - (j : ℤ)) :=
  AddMonoidHom.mk' (fun α ↦ bundleChernCapFamily E n C sX k α j)
    fun α β ↦ bundleChernCapFamily_add E n C sX k α β j

/-- The homomorphism `c_j(ℰ) ∩ -` sends `α` to the `j`-th member of
`Stacks.Chow.bundleChernCapFamily` of `α`. -/
@[simp]
theorem bundleChernCap_apply
    (k : ℤ) (j : Fin (n + 1 + 1)) (α : chowGroup C sX k) :
    bundleChernCap E n C sX k j α = bundleChernCapFamily E n C sX k α j :=
  rfl

/-! ### The Chern classes of Stacks 02U0 -/

/-- **Stacks 02U0, clause (1).** The family of Chern classes of a module of rank `n + 1` capped
with the fundamental cycle `[X]_d`, as the datum `Stacks.Chow.ChernClassFundamentalFamily`:
the family of Chern class cap products of `[X]_d`. -/
def chernClassFundamentalFamily
    (d : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (n + 1)
    letI := flat_bundleProj E n
    letI := locallyOfFiniteType_bundleProj E n
    ChernClassFundamentalFamily C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
      (relativeDimension_bundleProj E n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
      (bundleTwistCap E C sX) d :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  letI := flat_bundleProj E n
  letI := locallyOfFiniteType_bundleProj E n
  ⟨bundleChernCapFamily E n C sX d _, isChernCapFamily_bundleChernCapFamily E n C sX d _⟩

/-- **Stacks 02U0, part (2).** The `i`-th Chern class of a module of rank `n + 1` on `X`,
`c_i(ℰ) ∩ [X] ∈ A_{d-i}(X)`, where `[X] = [X]_d` is the fundamental cycle of Stacks 02QU. -/
def chernClassFundamental
    (d : ℤ) (i : Fin (n + 1 + 1)) : chowGroup C sX (d - (i : ℤ)) :=
  bundleChernCapFamily E n C sX d
    (QuotientAddGroup.mk' (rationalEquivalences C sX d)
      (cycleAssociatedToClosedSubscheme C sX (𝟙 X) d)) i

end Bundle

end Stacks.Chow

end
