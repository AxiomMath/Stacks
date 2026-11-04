module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratification

/-!
# The canonical gerbe stratification of an algebraic stack, and the question of Stacks 06RG

Let `𝒳` be an algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact. The
stratification of type (a) of **Stacks 06RF**, with strata chosen as large as possible, is
canonical (`exists_gerbe_stratification_unique`). Here it is made a definite object: the closed
sets `T_α = |𝒳| \ ⋃_{β < α} |𝒰_β|` are defined by transfinite recursion over the ordinals, with
`|𝒰_α|` the largest gerbe in `T_α` (`maximalGerbePointSet`), and the well-ordered index set `I` is
the set of ordinals below the least `α` with `T_α = ∅`
(`TopologicalSpace.stratificationIndex`).

**Stacks 06RG** (a remark) asks about the order type of these canonical stratifications: a natural
guess is that `I` has cardinality at most `ℵ₀`, and the Stacks project does not know whether this
is true or false. The question is stated here as a proposition,
`CanonicalGerbeStratificationIndexCountable`; neither it nor its negation is proved.

## Main results

* `AlgebraicGeometry.Stack.canonicalGerbeStratificationIndex`: the index set `I` of the canonical
  stratification of type (a), and `AlgebraicGeometry.Stack.canonicalGerbeStratum` its strata.
* `AlgebraicGeometry.Stack.canonicalGerbeStratification_spec`: these form a stratification of
  type (a) as in Stacks 06RF.
* `AlgebraicGeometry.Stack.canonicalGerbeStratification_unique`: every stratification of type (a)
  with strata as large as possible is order-isomorphic to it, with the same strata.
* `AlgebraicGeometry.Stack.CanonicalGerbeStratificationIndexCountable`: the question of Stacks
  06RG, and `canonicalGerbeStratificationIndexCountable_iff` its equivalent form for an arbitrary
  stratification of type (a).

## References

* [Stacks Project, Tag 06RF](https://stacks.math.columbia.edu/tag/06RF)
* [Stacks Project, Tag 06RG](https://stacks.math.columbia.edu/tag/06RG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The closed sets of the canonical stratification.** The transfinite sequence
`T_α = |𝒳| \ ⋃_{β < α} f T_β` of sets of points of `𝒳`, where `f T` is the largest gerbe in `T`
(`maximalGerbePointSet`). -/
noncomputable def canonicalGerbeStratificationClosed (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Ordinal.{u + 1} → Set (AlgebraicStacks.points B S hS 𝒳) :=
  TopologicalSpace.stratificationSeq (maximalGerbePointSet B S hS 𝒳)

/-- **The index set of the canonical stratification of type (a)** of Stacks 06RF: the ordinals
below the least `α` with `T_α = ∅`, well-ordered by the order of ordinals. -/
def canonicalGerbeStratificationIndex (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    Set Ordinal.{u + 1} :=
  TopologicalSpace.stratificationIndex (maximalGerbePointSet B S hS 𝒳)

/-- **The strata of the canonical stratification of type (a)**: the stratum indexed by `α` is the
largest gerbe in `T_α`. -/
noncomputable def canonicalGerbeStratum (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (i : canonicalGerbeStratificationIndex B S hS 𝒳) : Set (AlgebraicStacks.points B S hS 𝒳) :=
  maximalGerbePointSet B S hS 𝒳 (canonicalGerbeStratificationClosed B S hS 𝒳 i)

/-- A nonempty closed set of points lies in the closure of the largest gerbe in it. -/
private theorem subset_closure_maximalGerbePointSet (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) (hTne : T.Nonempty) :
    T ⊆ @closure _ (pointTopology B S hS 𝒳.val) (maximalGerbePointSet B S hS 𝒳 T) := by
  obtain ⟨Q, hQ, -, -, -, -, -, hdense, hmax⟩ := (exists_gerbe_strata B S hS 𝒳
    (isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection B S hS 𝒳 hqc) T hT
    hTne).1
  rwa [← hmax]

/-- Over a closed set of points, the largest gerbe is open in it, and nonempty when the set is. -/
private theorem maximalGerbePointSet_isOpen_nonempty (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    (∀ T, @IsClosed _ (pointTopology B S hS 𝒳.val) T → ∃ O,
      @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧ maximalGerbePointSet B S hS 𝒳 T = T ∩ O) ∧
    (∀ T, @IsClosed _ (pointTopology B S hS 𝒳.val) T → T.Nonempty →
      (maximalGerbePointSet B S hS 𝒳 T).Nonempty) := by
  let := pointTopology B S hS 𝒳.val
  have hqc' := isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection B S hS 𝒳 hqc
  refine ⟨fun T hT => ?_, fun T hT hTne => ?_⟩
  · obtain rfl | hne := T.eq_empty_or_nonempty
    · refine ⟨∅, isOpen_empty, ?_⟩
      rw [Set.empty_inter]
      exact Set.subset_empty_iff.1 (maximalGerbePointSet_subset B S hS 𝒳 ∅)
    · obtain ⟨Q, hQ, -, -, -, -, ⟨O, hO, hOeq⟩, -, hmax⟩ :=
        (exists_gerbe_strata B S hS 𝒳 hqc' T hT hne).1
      exact ⟨O, hO, hmax.symm.trans hOeq⟩
  · exact closure_nonempty_iff.1
      (hTne.mono (subset_closure_maximalGerbePointSet B S hS 𝒳 hqc T hT hTne))

/-- **The canonical stratification is a stratification of type (a)** (Stacks 06RF). Let `𝒳` be an
algebraic stack over `S` whose inertia projection is quasi-compact, and write `Wᵢ` for
`canonicalGerbeStratum` and `Tᵢ = |𝒳| \ ⋃_{j < i} Wⱼ`. Then, over the well-ordered index set
`canonicalGerbeStratificationIndex`,

* `Wᵢ` is the largest gerbe in `Tᵢ` (`maximalGerbePointSet`), and is nonempty,
* the `Wᵢ` cover `|𝒳|`,
* `Tᵢ` is closed, `Wᵢ` is open and dense in `Tᵢ`, and
* `Wᵢ` is the set of points of a reduced locally closed substack of `𝒳` which is a gerbe. -/
theorem canonicalGerbeStratification_spec (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) :
    (∀ i, canonicalGerbeStratum B S hS 𝒳 i = maximalGerbePointSet B S hS 𝒳
      (Set.univ \ ⋃ (j : canonicalGerbeStratificationIndex B S hS 𝒳) (_ : j < i),
        canonicalGerbeStratum B S hS 𝒳 j)) ∧
    (∀ i, (canonicalGerbeStratum B S hS 𝒳 i).Nonempty) ∧
    (⋃ i, canonicalGerbeStratum B S hS 𝒳 i) = Set.univ ∧
    (∀ i, @IsClosed _ (pointTopology B S hS 𝒳.val)
      (Set.univ \ ⋃ (j : canonicalGerbeStratificationIndex B S hS 𝒳) (_ : j < i),
        canonicalGerbeStratum B S hS 𝒳 j)) ∧
    (∀ i, ∃ O, @IsOpen _ (pointTopology B S hS 𝒳.val) O ∧ canonicalGerbeStratum B S hS 𝒳 i =
      (Set.univ \ ⋃ (j : canonicalGerbeStratificationIndex B S hS 𝒳) (_ : j < i),
        canonicalGerbeStratum B S hS 𝒳 j) ∩ O) ∧
    (∀ i, (Set.univ \ ⋃ (j : canonicalGerbeStratificationIndex B S hS 𝒳) (_ : j < i),
        canonicalGerbeStratum B S hS 𝒳 j) ⊆
      @closure _ (pointTopology B S hS 𝒳.val) (canonicalGerbeStratum B S hS 𝒳 i)) ∧
    (∀ i, ∃ (Q : ObjectProperty 𝒳.val.val.obj)
      (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q)),
      IsLocallyClosedSubstack 𝒳 Q ∧
        IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        AlgebraicStacks.IsGerbe B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ) ∧
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hQ)) =
          canonicalGerbeStratum B S hS 𝒳 i) := by
  let := pointTopology B S hS 𝒳.val
  have hqc' := isQuasiCompact_isomSpace_of_isQuasiCompactMorphism_inertiaProjection B S hS 𝒳 hqc
  obtain ⟨hopen, hne⟩ := maximalGerbePointSet_isOpen_nonempty B S hS 𝒳 hqc
  obtain ⟨hT, hTc, hTne, hcov⟩ := TopologicalSpace.isWellOrderedStratification_stratificationIndex
    (maximalGerbePointSet B S hS 𝒳) (maximalGerbePointSet_subset B S hS 𝒳) hopen hne
  have hTi : ∀ i : canonicalGerbeStratificationIndex B S hS 𝒳,
      (Set.univ \ ⋃ (j : canonicalGerbeStratificationIndex B S hS 𝒳) (_ : j < i),
        canonicalGerbeStratum B S hS 𝒳 j) = canonicalGerbeStratificationClosed B S hS 𝒳 i :=
    fun i => (hT i).symm
  refine ⟨fun i => by rw [hTi i]; rfl, fun i => hne _ (hTc i) (hTne i), hcov,
    fun i => by rw [hTi i]; exact hTc i, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hTi i]
    exact hopen _ (hTc i)
  · rw [hTi i]
    exact subset_closure_maximalGerbePointSet B S hS 𝒳 hqc _ (hTc i) (hTne i)
  · obtain ⟨Q, hQ, hlc, hr, hg, -, -, -, hmax⟩ :=
      (exists_gerbe_strata B S hS 𝒳 hqc' _ (hTc i) (hTne i)).1
    exact ⟨Q, hQ, hlc, hr, hg, hmax⟩

/-- **The canonical stratification is the stratification of type (a).** Let `𝒳` be an algebraic
stack over `S` whose inertia projection is quasi-compact. If a well-ordered family of nonempty
sets of points `Wᵢ` covers `|𝒳|` and each `Wᵢ` is the largest gerbe (`maximalGerbePointSet`) in
`|𝒳| \ ⋃_{j < i} Wⱼ`, then its index set is order-isomorphic to
`canonicalGerbeStratificationIndex`, matching the strata. -/
theorem canonicalGerbeStratification_unique (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    {I : Type*} [LinearOrder I] [WellFoundedLT I] (W : I → Set (AlgebraicStacks.points B S hS 𝒳))
    (hW : ∀ i, W i = maximalGerbePointSet B S hS 𝒳 (Set.univ \ ⋃ (j : I) (_ : j < i), W j))
    (hWne : ∀ i, (W i).Nonempty) (hWcov : (⋃ i, W i) = Set.univ) :
    ∃ e : I ≃o canonicalGerbeStratificationIndex B S hS 𝒳,
      ∀ i, canonicalGerbeStratum B S hS 𝒳 (e i) = W i := by
  obtain ⟨hW', hW'ne, hW'cov, -⟩ := canonicalGerbeStratification_spec B S hS 𝒳 hqc
  exact exists_gerbe_stratification_unique B S hS 𝒳 W hW hWne hWcov
    (canonicalGerbeStratum B S hS 𝒳) hW' hW'ne hW'cov

/-- **The question of Stacks 06RG.** For every algebraic stack `𝒳` over a scheme `S` whose inertia
projection `I_𝒳 ⟶ 𝒳` is quasi-compact (the setting of Stacks 06RF), the well-ordered index set `I`
of the canonical stratification of type (a) (`canonicalGerbeStratificationIndex`) has cardinality
at most `ℵ₀`.

This is the "natural guess" of the remark Stacks 06RG about the order type of the canonical
stratifications. The Stacks project does not know whether it is true or false; it is stated here
as a proposition, and neither it nor its negation is proved. By
`canonicalGerbeStratificationIndexCountable_iff` it says equally that every stratification of type
(a) with strata as large as possible has a countable index set. -/
@[stacks 06RG "the open question of the remark, stated as a proposition; neither it nor its \
negation is proved"]
def CanonicalGerbeStratificationIndexCountable : Prop :=
  ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS),
    IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) →
      (canonicalGerbeStratificationIndex B S hS 𝒳).Countable

/-- **The question of Stacks 06RG, for an arbitrary stratification of type (a).** The canonical
index sets are all countable if and only if every well-ordered family of nonempty sets of points
`Wᵢ` covering `|𝒳|`, each the largest gerbe in `|𝒳| \ ⋃_{j < i} Wⱼ`, has a countable index set. -/
theorem canonicalGerbeStratificationIndexCountable_iff :
    CanonicalGerbeStratificationIndexCountable.{u, w} ↔
      ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
        (𝒳 : AlgebraicStacks.{u, w} B S hS),
        IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) →
        ∀ (I : Type (u + 2)) [LinearOrder I] [WellFoundedLT I]
          (W : I → Set (AlgebraicStacks.points B S hS 𝒳)),
          (∀ i, W i = maximalGerbePointSet B S hS 𝒳 (Set.univ \ ⋃ (j : I) (_ : j < i), W j)) →
          (∀ i, (W i).Nonempty) → (⋃ i, W i) = Set.univ → Countable I := by
  constructor
  · intro h B S hS 𝒳 hqc I _ _ W hW hWne hWcov
    obtain ⟨e, -⟩ := canonicalGerbeStratification_unique B S hS 𝒳 hqc W hW hWne hWcov
    have := (h B S hS 𝒳 hqc).to_subtype
    exact e.injective.countable
  · intro h B S hS 𝒳 hqc
    obtain ⟨hW, hWne, hWcov, -⟩ := canonicalGerbeStratification_spec B S hS 𝒳 hqc
    exact Set.countable_coe_iff.1
      (h B S hS 𝒳 hqc _ (canonicalGerbeStratum B S hS 𝒳) hW hWne hWcov)

end AlgebraicGeometry.Stack

end
