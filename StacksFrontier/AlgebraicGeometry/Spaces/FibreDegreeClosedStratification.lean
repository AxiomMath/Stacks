module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.DegreeStratificationChartTransport

/-!
# The fibre degree stratification of an algebraic space

Let `W ⟶ X` be a morphism from a scheme to an algebraic space over `S` which is flat, locally of
finite presentation, separated and locally quasi-finite with universally bounded fibres. The
point set of `X` carries a finite chain of closed subsets
`∅ = Z₀ ⊆ Z₁ ⊆ … ⊆ Z_{n + 1} = |X|` whose strata `Z_{r + 1} ∖ Z_r` are characterized by the
base changes of `W ⟶ X` that are finite locally free of degree `r`.

## Main results

* `AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank`: the degree
  stratification of the point set of an algebraic space induced by such a morphism, together
  with its universal property.

## Implementation notes

**Indexing.** The chain is indexed by `ℕ` and shifted by one against the source, where it runs
from `Z₋₁ = ∅`: the set `Z r` here is the source's `Z_{r - 1}`, so the source's stratum `X_r` is
`Z (r + 1) ∖ Z r`. Inclusion is recorded as `Monotone`, which on `ℕ` is the conjunction of the
consecutive inclusions of the source.

**Strata as point sets.** The strata are closed subsets of the point set of `X` in the sense of
Stacks 03BX rather than reduced closed subspaces. The reduced induced structure of Stacks 047X is
determined by the underlying closed subset, and the universal property quantifies only over the
set-theoretic image of a morphism into `X`, so nothing in the statement depends on it.

**The scheme-level input.** The chart base change is handled by
`AlgebraicGeometry.Space.exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY`, which asks for
the stratification of a morphism of schemes in a chain indexed by `ℕ` and adapted to a *given*
degree bound, whereas
`AlgebraicGeometry.exists_closed_filtration_characterizing_finiteLocallyFree_rank`
produces its own bound and indexes by `Fin (n + 2)`. Both describe the same chain, namely the
loci where some fibre degree below the index occurs, so the reindexing below rebuilds that chain
directly from the lower semicontinuity of the fibre degree
(`AlgebraicGeometry.isClosed_fiber_rank_lt`) and from fixed-degree descent along a base change
(`AlgebraicGeometry.rank_of_constant_fiber_rank`).

**The bound.** `AlgebraicGeometry.Space.HasUniversallyBoundedFibers` bounds the fibre degrees by
an integer, which may be replaced by its truncation to `ℕ`: a degree witnessing the bound is a
natural number, so the bound is nonnegative as soon as it is used at all.

## References

* [Stacks Project, Tag 07S8](https://stacks.math.columbia.edu/tag/07S8)
* [Stacks Project, Tag 07RY](https://stacks.math.columbia.edu/tag/07RY)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- The locus where some fibre degree strictly below `m` occurs. -/
private def fiberRankLT {X S : Scheme.{u}} (f : X ⟶ S) (m : ℕ) : Set S :=
  {s | ∃ r < m, IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r}

/-- For universally bounded fibres, consecutive differences of the loci where some fibre degree
below the index occurs are the loci of a fixed fibre degree. -/
private lemma fiberRankLT_sdiff_self {X S : Scheme.{u}} (f : X ⟶ S)
    (hb : HasUniversallyBoundedFibers f) (r : ℕ) :
    fiberRankLT f (r + 1) \ fiberRankLT f r =
      {s | IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField s) r} := by
  ext s
  refine ⟨fun h => ?_, fun h => ⟨⟨r, lt_add_one r, h⟩, ?_⟩⟩
  · obtain ⟨⟨k, hk, hkrank⟩, hnot⟩ := h
    have hkr : k = r := by
      by_contra hne
      exact hnot ⟨k, by omega, hkrank⟩
    exact hkr ▸ hkrank
  · rintro ⟨k, hk, hkrank⟩
    obtain ⟨_, _, huniq⟩ := existsUnique_rank_of_bounded_fiber f hb s
    have := (huniq k hkrank).trans (huniq r h).symm
    omega

/-- **Stacks Project, Tag 07RY**, with the degree bound given in advance and the chain of closed
loci indexed by `ℕ`: a natural number `n` bounding the degrees of the fibres of a separated,
flat, locally finitely presented, locally quasi-finite morphism yields an increasing chain of
closed subsets from `∅` to the whole target, reaching it at index `n + 1`, whose strata
universally characterize the base changes which are finite locally free of each degree. -/
private lemma exists_monotone_closedChain_of_boundsFiberDegrees {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] [LocallyQuasiFinite f] (n : ℕ)
    (hn : BoundsFiberDegrees f (n : ℤ)) :
    ∃ Y : ℕ → Set S, Y 0 = ∅ ∧ (∀ r, IsClosed (Y r)) ∧ Monotone Y ∧
      Y (n + 1) = Set.univ ∧
      ∀ r : ℕ, r ≤ n → ∀ (T : Scheme.{u}) (t : T ⟶ S),
        IsFiniteLocallyFreeOfRank (pullback.snd f t) r ↔
          Set.range t.base ⊆ Y (r + 1) \ Y r := by
  have hb : HasUniversallyBoundedFibers f := ⟨n, hn⟩
  refine ⟨fiberRankLT f, ?_, fun r => isClosed_fiber_rank_lt f hb r, ?_, ?_, ?_⟩
  · ext s
    simp [fiberRankLT]
  · rintro a b hab s ⟨r, hr, hrank⟩
    exact ⟨r, lt_of_lt_of_le hr hab, hrank⟩
  · refine Set.eq_univ_of_forall fun s => ?_
    obtain ⟨r, hr, hrank⟩ := hn s
    exact ⟨r, by omega, hrank⟩
  · intro r _ T t
    rw [fiberRankLT_sdiff_self f hb r]
    refine ⟨fun h s hs => ?_, fun h => ?_⟩
    · obtain ⟨p, rfl⟩ := hs
      obtain ⟨m, hm, -⟩ := existsUnique_rank_of_bounded_fiber f hb (t.base p)
      have hmfib := finiteLocallyFreeOfRank_residueFiber_baseChange f t p m hm
      let := h
      have hrfib : IsFiniteLocallyFreeOfRank
          ((pullback.snd f t).fiberToSpecResidueField p) r :=
        IsFiniteLocallyFreeOfRank.of_isPullback
          (IsPullback.of_hasPullback (pullback.snd f t) (T.fromSpecResidueField p))
      exact (finiteLocallyFree_rank_unique _ m r hmfib hrfib) ▸ hm
    · exact rank_of_constant_fiber_rank (pullback.snd f t) r fun p =>
        finiteLocallyFreeOfRank_residueFiber_baseChange f t p r (h ⟨p, rfl⟩)

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 07S8.** A flat, locally finitely presented, separated, locally
quasi-finite morphism from a scheme to an algebraic space with universally bounded fibres induces
a finite increasing chain of closed subsets of the point set, from `∅` to the whole point set,
whose strata are the loci over which the base change of the morphism is finite locally free of a
fixed degree. -/
@[stacks 07S8]
theorem exists_closedChain_isFiniteLocallyFreeOfRank
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (W : BigFppfOver B S hS)
    (g : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hflat : IsFlat B S hS g) (hlfp : IsLocallyOfFinitePresentation B S hS g)
    (hsep : IsSeparated B S hS g) (hlqf : IsLocallyQuasiFinite B S hS g)
    (hbound : HasUniversallyBoundedFibers B S hS W g) :
    ∃ (n : ℕ) (Z : ℕ → Set (points B S hS X)), Z 0 = ∅ ∧ (∀ r, IsClosed (Z r)) ∧ Monotone Z ∧
      Z (n + 1) = Set.univ ∧
      ∀ r : ℕ, r ≤ n → ∀ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hm : T ⟶ X),
        IsAlgebraicSpace B S hS T →
        ∀ (Pp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (pr₁ : Pp ⟶ yoneda.obj W) (pr₂ : Pp ⟶ T),
          IsPullback pr₁ pr₂ g hm →
          ((MorphismProperty.inverseImage (IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf pr₂ ↔
            Set.range (pointsMap B S hS T hm) ⊆ Z (r + 1) \ Z r) := by
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N.toNat, exists_closedChain_isFiniteLocallyFreeOfRank_of_h07RY B S hS
    (fun f hf hlfp' hsep' hlqf' m hm => ?_) X W g hX hflat hlfp hsep hlqf N.toNat
    fun k _ T hT ξ => ?_⟩
  · let := hf
    let := hlfp'
    let := hsep'
    let := hlqf'
    exact exists_monotone_closedChain_of_boundsFiberDegrees f m hm
  · obtain ⟨V, p, i, r, hrN, hrank, hpull⟩ := hN k T hT ξ
    exact ⟨V, p, i, r, by omega, hrank, hpull⟩

end Space

end AlgebraicGeometry

end
