module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenRestrictionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankSubspace

/-!
# Chow groups of a good algebraic space decomposed into open and closed subspaces

In Situation 0EDT let `X/B` be good and let `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` be a decomposition of `X`
into open and closed subspaces (`AlgebraicGeometry.Space.IsClopenSubspaceDecomposition`). Then
the Chow groups of `X` form a direct product along it,

`CH_k(X) = ∏_i CH_k(X_i)`,

the projections being the restrictions `α ↦ α|_{X_i}`, that is the flat pullbacks along the
inclusions of the pieces (Stacks 0EQB), which are open immersions and so flat of relative
dimension `0`. Surjectivity is the gluing of cycles of
`AlgebraicGeometry.Space.cycleGroupDecompositionEquiv`; injectivity is
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_of_forall_cycleGroupRestrict`: a
cycle whose restriction to every piece is rationally equivalent to zero is rationally equivalent
to zero, the pieces forming a locally finite family.

For a finite locally free `𝒪_X`-module `ℰ` the subspaces `X_r` where `ℰ` has rank `r`
(`AlgebraicGeometry.Space.rankSubspace`) form such a decomposition, and so do their inverse
images `X'_r` in any good `X' ⟶ X`. This is the decomposition of Stacks 0ES2.

## Main definitions

* `AlgebraicGeometry.Space.chowGroupCanonicalPieceRestrict`: the restriction
  `CH_k(X) → CH_k(X_i)`.
* `AlgebraicGeometry.Space.chowGroupCanonicalDecompositionEquiv`: the isomorphism
  `CH_k(X) ≅ ∏_i CH_k(X_i)`.

## Main results

* `AlgebraicGeometry.Space.IsClopenSubspaceDecomposition.isClosedSubspace`: each piece of a
  decomposition is a closed subspace.
* `AlgebraicGeometry.Space.bijective_chowGroupCanonicalDecompositionRestrict`: the restrictions
  to the pieces identify `CH_k(X)` with the product of the `CH_k(X_i)`.
* `AlgebraicGeometry.Space.isClopenSubspaceDecomposition_rankSubspace`: the rank subspaces of a
  finite locally free module form a decomposition of `X`.
* `AlgebraicGeometry.Space.isClopenSubspaceDecomposition_rankSubspace_preimage`: so do their
  inverse images in a good `X' ⟶ X`.

## Implementation notes

The rank decomposition is indexed by `ULift ℕ`, because the decomposition of the Chow groups is
stated for an index type in the universe of the spaces, which is where the index of the locally
finite family in the injectivity half has to live.

## References

* [Stacks Project, Tag 0ES2](https://stacks.math.columbia.edu/tag/0ES2)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The pieces of a decomposition are open and closed subspaces -/

section Pieces

variable {D : BaseSpaceDimensionSituation.{u}}
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    {I : Type u} {R : I → Subfunctor Y}

namespace IsClopenSubspaceDecomposition

/-- A piece of a decomposition is an open subspace. -/
theorem isOpenSubspace (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (i : I) :
    IsOpenSubspace D.site D.base D.base_mem (R i) :=
  ⟨(h.isGoodPiece i).1, h.isOpenImmersion i⟩

/-- A piece of a decomposition is a closed subspace. -/
theorem isClosedSubspace (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (i : I) :
    IsClosedSubspace D.site D.base D.base_mem (R i) :=
  ⟨(h.isGoodPiece i).1, isClosedImmersion_of_isOpenImmersion_of_isClosed_range_pointsMap
    D.site D.base D.base_mem (R i).ι (h.isOpenImmersion i) (h.isClosed_pieceRange i)⟩

end IsClopenSubspaceDecomposition

end Pieces

/-! ### The product decomposition of the Chow groups -/

section ChowGroup

variable {D : BaseSpaceDimensionSituation.{u}}
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    {I : Type u} {R : I → Subfunctor Y}

/-- The inclusion of a piece of a decomposition is flat of relative dimension `0`, being an open
immersion. -/
theorem isFlat_and_hasRelativeDimension_zero_ι
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (i : I) :
    IsFlat D.site D.base D.base_mem (R i).ι ∧
      HasRelativeDimension 0 D.site D.base D.base_mem (R i).ι :=
  ⟨isFlat_of_isEtale D.site D.base D.base_mem
      (isEtale_of_isOpenImmersion D.site D.base D.base_mem (h.isOpenImmersion i)),
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem (R i).ι h.isGood.1
      (isEtale_of_isOpenImmersion D.site D.base D.base_mem (h.isOpenImmersion i))⟩

/-- **The restriction `CH_k(X) → CH_k(X_i)` to a piece of a decomposition**: the flat pullback
(Stacks 0EQB) along the inclusion of the piece, which is flat of relative dimension `0`. -/
def chowGroupCanonicalPieceRestrict (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι)
    (i : I) (k : ℤ) :
    chowGroupCanonical.{u + 1} D sY h.isGood k →+
      chowGroupCanonical.{u + 1} D ((R i).ι ≫ sY) (h.isGoodPiece i) k :=
  flatPullbackChowMapCanonical.{u + 1} D ((R i).ι ≫ sY) (h.isGoodPiece i) sY h.isGood (R i).ι rfl
    0 (isFlat_and_hasRelativeDimension_zero_ι h i).1
    (isFlat_and_hasRelativeDimension_zero_ι h i).2 k k (by simp)

/-- The restriction to a piece sends the class of a cycle to the class of its restriction. -/
theorem chowGroupCanonicalPieceRestrict_chowClassCanonical
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (i : I) (k : ℤ)
    (α : CycleGroup D sY k) :
    chowGroupCanonicalPieceRestrict h i k (chowClassCanonical.{u + 1} D sY h.isGood k α) =
      chowClassCanonical.{u + 1} D ((R i).ι ≫ sY) (h.isGoodPiece i) k
        (cycleGroupRestrict D sY h.isGood ((R i).ι ≫ sY) (h.isGoodPiece i)
          (h.isOpenImmersion i) rfl k α) := by
  rw [chowGroupCanonicalPieceRestrict, flatPullbackChowMapCanonical_chowClassCanonical]
  exact congrArg _ (Subtype.ext (flatPullbackMap_eq_cycleGroupRestrict D sY h.isGood
    ((R i).ι ≫ sY) (h.isGoodPiece i) (h.isOpenImmersion i) rfl k k (by simp) α))

/-- The restrictions to all the pieces of a decomposition at once,
`CH_k(X) → ∏_i CH_k(X_i)`. -/
def chowGroupCanonicalDecompositionRestrict
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (k : ℤ) :
    chowGroupCanonical.{u + 1} D sY h.isGood k →+
      ∀ i, chowGroupCanonical.{u + 1} D ((R i).ι ≫ sY) (h.isGoodPiece i) k :=
  Pi.addMonoidHom fun i => chowGroupCanonicalPieceRestrict h i k

/-- The glued cycle restricts to the given cycle on every piece. -/
theorem cycleGroupRestrict_glueDecompositionCycle
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) {k : ℤ}
    (β : ∀ i, CycleGroup D ((R i).ι ≫ sY) k) (i : I) :
    cycleGroupRestrict D sY h.isGood ((R i).ι ≫ sY) (h.isGoodPiece i) (h.isOpenImmersion i) rfl k
        (glueDecompositionCycle h β) = β i :=
  Subtype.ext (funext fun W => glueDecompositionCoeff_eq h β (rfl : h.pieceClosureImage i W = _))

/-- **Stacks 0ES2: `CH_k(X) = ∏_i CH_k(X_i)`.** Along a decomposition of a good algebraic space
into open and closed subspaces the restrictions to the pieces identify the Chow group of `X` with
the product of the Chow groups of the pieces. -/
theorem bijective_chowGroupCanonicalDecompositionRestrict
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (k : ℤ) :
    Function.Bijective (chowGroupCanonicalDecompositionRestrict h k) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun α hα => ?_, fun β => ?_⟩
  · obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ α
    show chowClassCanonical.{u + 1} D sY h.isGood k a = 0
    rw [chowClassCanonical_eq_zero_iff]
    refine isRationallyEquivalentToZeroCanonical_of_forall_cycleGroupRestrict D sY h.isGood R
      h.isOpenSubspace h.isClosedSubspace h.disjoint (fun p => h.exists_mem p) k a fun i => ?_
    have hi := congrFun hα i
    change chowGroupCanonicalPieceRestrict h i k (chowClassCanonical.{u + 1} D sY h.isGood k a) =
      0 at hi
    rwa [chowGroupCanonicalPieceRestrict_chowClassCanonical, chowClassCanonical_eq_zero_iff] at hi
  · choose b hb using fun i => QuotientAddGroup.mk'_surjective
      (rationalEquivalencesCanonical.{u + 1} D ((R i).ι ≫ sY) (h.isGoodPiece i) k) (β i)
    refine ⟨chowClassCanonical.{u + 1} D sY h.isGood k (glueDecompositionCycle h b),
      funext fun i => ?_⟩
    show chowGroupCanonicalPieceRestrict h i k
      (chowClassCanonical.{u + 1} D sY h.isGood k (glueDecompositionCycle h b)) = β i
    rw [chowGroupCanonicalPieceRestrict_chowClassCanonical,
      cycleGroupRestrict_glueDecompositionCycle h b i]
    exact hb i

/-- **Stacks 0ES2: the isomorphism `CH_k(X) ≅ ∏_i CH_k(X_i)`** along a decomposition of a good
algebraic space into open and closed subspaces, given by the restrictions to the pieces. -/
def chowGroupCanonicalDecompositionEquiv
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (k : ℤ) :
    chowGroupCanonical.{u + 1} D sY h.isGood k ≃+
      ∀ i, chowGroupCanonical.{u + 1} D ((R i).ι ≫ sY) (h.isGoodPiece i) k :=
  AddEquiv.ofBijective (chowGroupCanonicalDecompositionRestrict h k)
    (bijective_chowGroupCanonicalDecompositionRestrict h k)

/-- The isomorphism of the product decomposition is restriction to the pieces. -/
@[simp]
theorem chowGroupCanonicalDecompositionEquiv_apply
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D sY h.isGood k) (i : I) :
    chowGroupCanonicalDecompositionEquiv h k α i = chowGroupCanonicalPieceRestrict h i k α :=
  rfl

/-- Two classes on `X` with the same restrictions to all the pieces are equal. -/
theorem chowGroupCanonical_ext_of_decomposition
    (h : IsClopenSubspaceDecomposition D sY fun i => (R i).ι) {k : ℤ}
    {α β : chowGroupCanonical.{u + 1} D sY h.isGood k}
    (hαβ : ∀ i, chowGroupCanonicalPieceRestrict h i k α =
      chowGroupCanonicalPieceRestrict h i k β) : α = β :=
  (bijective_chowGroupCanonicalDecompositionRestrict h k).1 (funext hαβ)

end ChowGroup

/-! ### The decomposition by the rank of a finite locally free module -/

section Rank

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The rank subspace `X_r ⊆ X` of `ℰ` is good over the base. -/
theorem isGood_rankSubspace (r : ℕ) :
    D.IsGood ((rankSubspace (Y := ⟨X, hX.1⟩) E r).ι ≫ sX) :=
  isGood_ι_of_isOpenSubspace D sX hX _ (isOpenSubspace_rankSubspace (Y := ⟨X, hX.1⟩) E r)

/-- The image on points of the inclusion of `X_r` is the rank locus of `r`. -/
theorem pieceRange_rankSubspace (r : ULift.{u} ℕ) :
    pieceRange D (fun r : ULift.{u} ℕ => (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι) r =
      rankLocus (Y := ⟨X, hX.1⟩) E r.down :=
  range_pointsMap_ι_rankSubspace (Y := ⟨X, hX.1⟩) E r.down

include hE in
/-- **Stacks 0ES2: `X = X_0 ⨿ X_1 ⨿ X_2 ⨿ …`.** The subspaces `X_r` where a finite locally free
module `ℰ` has rank `r` are a decomposition of a good algebraic space `X` into open and closed
subspaces. -/
theorem isClopenSubspaceDecomposition_rankSubspace :
    IsClopenSubspaceDecomposition D sX fun r : ULift.{u} ℕ =>
      (rankSubspace (Y := ⟨X, hX.1⟩) E r.down).ι where
  isGood := hX
  isGoodPiece r := isGood_rankSubspace D sX hX E r.down
  isOpenImmersion r := (isOpenSubspace_rankSubspace (Y := ⟨X, hX.1⟩) E r.down).2
  disjoint r r' hrr' := by
    rw [pieceRange_rankSubspace D sX hX E r, pieceRange_rankSubspace D sX hX E r']
    exact Set.disjoint_left.2 fun _ h h' =>
      hrr' (ULift.ext _ _ (eq_of_mem_rankLocus_of_mem_rankLocus h h'))
  iUnion_pieceRange_eq_univ := by
    refine Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_mem_rankLocus (Y := ⟨X, hX.1⟩) hE p
    exact ⟨ULift.up n, by rwa [pieceRange_rankSubspace D sX hX E]⟩

/-- The inverse image `X'_r ⊆ X'` of `X_r` in a good `g : X' ⟶ X` is good over the base. -/
theorem isGood_rankSubspace_preimage {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (r : ℕ) :
    D.IsGood (((rankSubspace (Y := ⟨X, hX.1⟩) E r).preimage g).ι ≫ g ≫ sX) :=
  isGood_ι_of_isOpenSubspace D (g ≫ sX) hY _
    (isOpenSubspace_preimage D.site D.base D.base_mem g _ hX.1 hY.1
      (isOpenSubspace_rankSubspace (Y := ⟨X, hX.1⟩) E r))

include hE in
/-- **Stacks 0ES2: the decomposition of `X'` obtained by pullback.** For a good `g : X' ⟶ X` the
inverse images `X'_r` of the rank subspaces of `ℰ` are a decomposition of `X'` into open and
closed subspaces. -/
theorem isClopenSubspaceDecomposition_rankSubspace_preimage
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) :
    IsClopenSubspaceDecomposition D (g ≫ sX) fun r : ULift.{u} ℕ =>
      ((rankSubspace (Y := ⟨X, hX.1⟩) E r.down).preimage g).ι :=
  isClopenSubspaceDecomposition_preimage g
    (isClopenSubspaceDecomposition_rankSubspace D sX hX E hE) hY
    fun r => isGood_rankSubspace_preimage D sX hX E g hY r.down

end Rank

end AlgebraicGeometry.Space
