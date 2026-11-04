module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of Stacks 02U0 at every rank

Let `(S, δ)` be the base situation of chapter 42, `X` locally of finite type over `S` and `ℰ` a
finite locally free `𝒪_X`-module of rank `r`, with projective bundle `(π : 𝐏(ℰ) ⟶ X, 𝒪(1))`.
[Stacks, Tag 02U0] defines the Chern classes of `ℰ` on `X`:

1. by the projective space bundle formula [Stacks, Tag 02TX] there are classes
   `c_i ∈ A_{n-i}(X)`, `0 ≤ i ≤ r`, with `c_0 = [X]` and
   `∑_{i=0}^{r} (-1)^i c₁(𝒪(1))^i ∩ π^*c_{r-i} = 0`;
2. `c_i(ℰ) ∩ [X] = c_i`;
3. `c(ℰ) ∩ [X] = ∑_i c_i(ℰ) ∩ [X]` in `A_*(X) = ⊕_k A_k(X)`.

This file states and proves the three parts for the genuine projective bundle `Stacks.Chow.bundle`
of `ℰ`, at every rank `r` — in rank zero `𝐏(ℰ)` is empty, so its Chow groups vanish and the
relation holds trivially — and for the classes `c_j(ℰ) ∩ α` of an arbitrary class `α`
([Stacks, Tag 02U6]).

## Main results

* `Stacks.Chow.existsUnique_isChernCapFamilyOfRank` — every class `α ∈ A_k(X)` has exactly one
  family `(α_j)` with `α_0 = α` satisfying the relation on `𝐏(ℰ)`.
* `Stacks.Chow.existsUnique_isChernClassFundamentalFamilyOfRank` — **Stacks 02U0, part (1)**.
* `Stacks.Chow.chernClassFundamentalOfRank` — **Stacks 02U0, part (2)**.
* `Stacks.Chow.totalChernClassFundamentalOfRank` — **Stacks 02U0, part (3)**.

## Implementation notes

The source assumes `X` integral and `n = dim_δ(X)`. Neither is used: the fundamental cycle
`[X]_n` is defined for every `X` and every `n`, and the relation is an identity in the Chow group
of `𝐏(ℰ)`. Specializing gives the source's statement verbatim, so dropping them is a
generalization.

## References

* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- The projection of the projective bundle of a module of rank `r` is flat: in rank zero its
source is empty. -/
theorem flat_bundleProj_ofRank :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    Flat (bundleProj E) := by
  rcases r with _ | n
  · let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    have := isEmpty_bundle_of_rank_zero E
    exact Flat.of_stalkMap (f := bundleProj E) fun x ↦ isEmptyElim x
  · exact flat_bundleProj E n

/-- The projection of the projective bundle of a module of rank `r` is locally of finite type. -/
theorem locallyOfFiniteType_bundleProj_ofRank :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    LocallyOfFiniteType (bundleProj E) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  inferInstance

/-- The projection of the projective bundle of a module of rank `r` has relative dimension
`r - 1`: in rank zero its source is empty, so it has no nonempty fibre. -/
theorem relativeDimension_bundleProj_ofRank :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    letI := locallyOfFiniteType_bundleProj_ofRank E r
    AlgebraicGeometry.RelativeDimension (bundleProj E) (r - 1) := by
  rcases r with _ | n
  · let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    have := isEmpty_bundle_of_rank_zero E
    intro s ⟨y⟩
    exact isEmptyElim ((bundleProj E).fiberι s y)
  · exact relativeDimension_bundleProj E n

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 02U6, the characterization**, on the projective bundle of a module `ℰ` of rank `r`:
that a family `(α_j)_{0 ≤ j ≤ r}`, `α_j ∈ A_{k-j}(X)`, has `α_0 = α` and satisfies
`∑_{i=0}^{r} (-1)^i c₁(𝒪(1))^i ∩ π^*α_{r-i} = 0` in the Chow group of `𝐏(ℰ)`. -/
abbrev IsChernCapFamilyOfRank (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) : Prop :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  letI := flat_bundleProj_ofRank E r
  letI := locallyOfFiniteType_bundleProj_ofRank E r
  IsChernCapFamily C sX (bundleProj E ≫ sX) (bundleProj E) rfl r
    (relativeDimension_bundleProj_ofRank E r)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (bundleTwistCap E C sX) k α c

/-- **Stacks 02TX, both halves, in the indexing of the relation of Stacks 02U6**, at every rank.
In rank zero the source of the map is the zero group and its target, a Chow group of the empty
scheme, vanishes. -/
theorem projectiveBundleRelation_ofRank :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
    letI := flat_bundleProj_ofRank E r
    letI := locallyOfFiniteType_bundleProj_ofRank E r
    ProjectiveBundleRelationInjective C sX (bundleProj E ≫ sX) (bundleProj E) rfl r
        (relativeDimension_bundleProj_ofRank E r)
        (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
        (bundleTwistCap E C sX) ∧
      ProjectiveBundleRelationSurjective C sX (bundleProj E ≫ sX) (bundleProj E) rfl r
        (relativeDimension_bundleProj_ofRank E r)
        (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
        (bundleTwistCap E C sX) := by
  rcases r with _ | n
  · let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    refine ⟨fun k β γ _ ↦ funext fun i ↦ i.elim0, fun k y ↦ ⟨fun i ↦ i.elim0, ?_⟩⟩
    have := subsingleton_chowGroup_bundle_of_rank_zero E C sX
      (k + ((0 - 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))
    exact Subsingleton.elim _ _
  · exact ⟨projectiveBundleRelationInjective_bundle E n C sX,
      projectiveBundleRelationSurjective_bundle E n C sX⟩

/-- **Stacks 02U6, existence and uniqueness**, at every rank: every class `α ∈ A_k(X)` has exactly
one family `(α_j)_{0 ≤ j ≤ r}` with `α_0 = α` satisfying the relation on `𝐏(ℰ)`. -/
theorem existsUnique_isChernCapFamilyOfRank (k : ℤ) (α : chowGroup C sX k) :
    ∃! c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)),
      IsChernCapFamilyOfRank E r C sX k α c :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let := flat_bundleProj_ofRank E r
  let := locallyOfFiniteType_bundleProj_ofRank E r
  existsUnique_isChernCapFamily C sX _ _ rfl r _ _ _ (projectiveBundleRelation_ofRank E r C sX).1
    (projectiveBundleRelation_ofRank E r C sX).2 k α

/-- **The Chern class cap products of Stacks 02U6**, `(c_j(ℰ) ∩ α)_{0 ≤ j ≤ r}` for a class
`α ∈ A_k(X)` and a module of rank `r`: the unique family of
`Stacks.Chow.existsUnique_isChernCapFamilyOfRank`. -/
def chernCapFamilyOfRank (k : ℤ) (α : chowGroup C sX k) (j : Fin (r + 1)) :
    chowGroup C sX (k - (j : ℤ)) :=
  (existsUnique_isChernCapFamilyOfRank E r C sX k α).exists.choose j

/-- The family `Stacks.Chow.chernCapFamilyOfRank` has first member `α` and satisfies the relation
on `𝐏(ℰ)`. -/
theorem isChernCapFamilyOfRank_chernCapFamilyOfRank (k : ℤ) (α : chowGroup C sX k) :
    IsChernCapFamilyOfRank E r C sX k α (chernCapFamilyOfRank E r C sX k α) :=
  (existsUnique_isChernCapFamilyOfRank E r C sX k α).exists.choose_spec

/-- Every family with first member `α` satisfying the relation on `𝐏(ℰ)` is
`Stacks.Chow.chernCapFamilyOfRank`. -/
theorem eq_chernCapFamilyOfRank_of_isChernCapFamilyOfRank (k : ℤ) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamilyOfRank E r C sX k α c) : c = chernCapFamilyOfRank E r C sX k α :=
  (existsUnique_isChernCapFamilyOfRank E r C sX k α).unique hc
    (isChernCapFamilyOfRank_chernCapFamilyOfRank E r C sX k α)

/-- In rank `n + 1` the family is `Stacks.Chow.bundleChernCapFamily`. -/
theorem chernCapFamilyOfRank_succ (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] (k : ℤ)
    (α : chowGroup C sX k) :
    chernCapFamilyOfRank E (n + 1) C sX k α = bundleChernCapFamily E n C sX k α :=
  (eq_chernCapFamilyOfRank_of_isChernCapFamilyOfRank E (n + 1) C sX k α _
    (isChernCapFamily_bundleChernCapFamily E n C sX k α)).symm

/-- In rank zero the family is `α` itself. -/
theorem chernCapFamilyOfRank_rank_zero
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] (k : ℤ)
    (α : chowGroup C sX k) (j : Fin (0 + 1)) :
    chernCapFamilyOfRank E 0 C sX k α j =
      chowGroupCast C sX (by rw [Fin.val_eq_zero j]; simp) α := by
  obtain rfl : j = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (Fin.val_eq_zero j)
  have h := (isChernCapFamilyOfRank_chernCapFamilyOfRank E 0 C sX k α).1
  conv_rhs => rw [← h]
  rw [chowGroupCast_chowGroupCast]
  rfl

/-! ### Stacks 02U0 -/

/-- **Stacks 02U0, part (1).** For a module `ℰ` of rank `r` on `X` and an integer `n`, there are
classes `c_i ∈ A_{n-i}(X)`, `0 ≤ i ≤ r`, with `c_0 = [X]` and
`∑_{i=0}^{r} (-1)^i c₁(𝒪_{𝐏(ℰ)}(1))^i ∩ π^*c_{r-i} = 0`, and exactly one such family. Here
`[X] = [X]_n` is the fundamental cycle of Stacks 02QU; the source takes `X` integral and
`n = dim_δ(X)`, which is not needed. -/
@[stacks 02U0 "part (1)"]
theorem existsUnique_isChernClassFundamentalFamilyOfRank (n : ℤ) :
    ∃! c : ∀ i : Fin (r + 1), chowGroup C sX (n - (i : ℤ)),
      IsChernCapFamilyOfRank E r C sX n
        (QuotientAddGroup.mk' (rationalEquivalences C sX n)
          (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n)) c :=
  existsUnique_isChernCapFamilyOfRank E r C sX n _

/-- **Stacks 02U0, part (2).** The `i`-th Chern class of a module `ℰ` of rank `r` on `X`,
`c_i(ℰ) ∩ [X] = c_i ∈ A_{n-i}(X)`: the `i`-th member of the family of part (1). -/
@[stacks 02U0 "part (2)"]
def chernClassFundamentalOfRank (n : ℤ) (i : Fin (r + 1)) : chowGroup C sX (n - (i : ℤ)) :=
  chernCapFamilyOfRank E r C sX n
    (QuotientAddGroup.mk' (rationalEquivalences C sX n)
      (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n)) i

/-- In rank `n + 1` the classes are `Stacks.Chow.chernClassFundamental`. -/
theorem chernClassFundamentalOfRank_succ (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] (d : ℤ) :
    chernClassFundamentalOfRank E (n + 1) C sX d = chernClassFundamental E n C sX d :=
  chernCapFamilyOfRank_succ E C sX n d _

/-- The Chern classes of part (2) form the family of part (1). -/
theorem isChernCapFamilyOfRank_chernClassFundamentalOfRank (n : ℤ) :
    IsChernCapFamilyOfRank E r C sX n
      (QuotientAddGroup.mk' (rationalEquivalences C sX n)
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) n))
      (chernClassFundamentalOfRank E r C sX n) :=
  isChernCapFamilyOfRank_chernCapFamilyOfRank E r C sX n _

/-- **Stacks 02U0, part (3).** The total Chern class of a module of rank `r` on `X`,
`c(ℰ) ∩ [X] = c_0(ℰ) ∩ [X] + … + c_r(ℰ) ∩ [X]` in `A_*(X) = ⊕_k A_k(X)`. -/
@[stacks 02U0 "part (3)"]
def totalChernClassFundamentalOfRank (n : ℤ) : ⨁ k : ℤ, chowGroup C sX k :=
  ∑ i : Fin (r + 1), DirectSum.of (fun k : ℤ => chowGroup C sX k) (n - (i : ℤ))
    (chernClassFundamentalOfRank E r C sX n i)

end Stacks.Chow

end
