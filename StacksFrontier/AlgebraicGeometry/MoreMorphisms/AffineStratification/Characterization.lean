module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CohomologyVanishing

/-!
# What a bound on the affine stratification number says

On a quasi-compact quasi-separated scheme the inequality `affineStratificationNumber X ≤ d` is
equivalent to the existence of an affine stratification of `X` indexed by `0, …, d`, which is
the characterisation of the number in [Stacks, Tag 0F2V].

## Main results

* `AlgebraicGeometry.affineStratificationNumber_le_iff`: the equivalence.

## Implementation notes

The affine stratification number is an infimum in `ℕ` over the lengths of the affine
stratifications of `X`, so it is zero when there is none, and the inequality then holds for
every `d` while no stratification exists. The equivalence therefore needs the hypothesis that
makes a finite affine stratification exist, by [Stacks, Tag 0F2U] quasi-compactness and
quasi-separatedness; a statement about the number alone carries the existence of a
stratification only in its presence.

The direction from the inequality to the existence lengthens the optimal stratification, whose
length is the number itself, to one indexed by `0, …, d`. The added strata are empty: the empty
subset is locally closed, the reduced induced scheme on it is the empty scheme, which is affine,
and its inclusion is an affine morphism.

## References

* [Stacks Project, Tag 0F2V](https://stacks.math.columbia.edu/tag/0F2V)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

namespace AffineStratification

/-- The strata of an affine stratification indexed by `0, …, m`, read as a family indexed by
`0, …, d`: the indices beyond `m` carry the empty stratum. -/
private def padStrata {X : Scheme.{u}} {m : ℕ} (s : AffineStratification X (Fin (m + 1)))
    (d : ℕ) : Fin (d + 1) → Set X := fun k =>
  if hk : (k : ℕ) < m + 1 then s.strata ⟨k, hk⟩ else ∅

private lemma padStrata_of_lt {X : Scheme.{u}} {m : ℕ} (s : AffineStratification X (Fin (m + 1)))
    (d : ℕ) {k : Fin (d + 1)} (hk : (k : ℕ) < m + 1) :
    padStrata s d k = s.strata ⟨k, hk⟩ := dif_pos hk

private lemma padStrata_of_not_lt {X : Scheme.{u}} {m : ℕ}
    (s : AffineStratification X (Fin (m + 1))) (d : ℕ) {k : Fin (d + 1)}
    (hk : ¬ (k : ℕ) < m + 1) : padStrata s d k = ∅ := dif_neg hk

private lemma padStrata_castLE {X : Scheme.{u}} {m d : ℕ}
    (s : AffineStratification X (Fin (m + 1))) (hmd : m + 1 ≤ d + 1) (i : Fin (m + 1)) :
    padStrata s d (Fin.castLE hmd i) = s.strata i := by
  rw [padStrata_of_lt s d (show ((Fin.castLE hmd i : Fin (d + 1)) : ℕ) < m + 1 from i.isLt)]
  exact congrArg s.strata (Fin.ext rfl)

private lemma padStrata_isLocallyFiniteStratification {X : Scheme.{u}} {m d : ℕ}
    (s : AffineStratification X (Fin (m + 1))) (hmd : m ≤ d) :
    IsLocallyFiniteStratification (padStrata s d) := by
  have hmd' : m + 1 ≤ d + 1 := by omega
  have hpart := s.isLocallyFiniteStratification.isStratification.isPartition
  refine ⟨⟨⟨fun k => ?_, fun k l hkl => ?_, ?_⟩, fun k => ?_⟩, locallyFinite_of_finite _⟩
  · by_cases hk : (k : ℕ) < m + 1
    · rw [padStrata_of_lt s d hk]
      exact hpart.locallyClosed _
    · rw [padStrata_of_not_lt s d hk]
      exact isOpen_empty.isLocallyClosed
  · by_cases hk : (k : ℕ) < m + 1
    · by_cases hl : (l : ℕ) < m + 1
      · rw [padStrata_of_lt s d hk, padStrata_of_lt s d hl]
        refine hpart.disjoint _ _ fun h => hkl (Fin.ext ?_)
        simpa using congrArg Fin.val h
      · rw [padStrata_of_not_lt s d hl]
        exact disjoint_bot_right
    · rw [padStrata_of_not_lt s d hk]
      exact disjoint_bot_left
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hpart.cover ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨Fin.castLE hmd' i, by rwa [padStrata_castLE s hmd']⟩
  · by_cases hk : (k : ℕ) < m + 1
    · rw [padStrata_of_lt s d hk]
      intro x hx
      obtain ⟨i, hik, hxi⟩ := by
        simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using
          s.isLocallyFiniteStratification.isStratification.closure_subset ⟨(k : ℕ), hk⟩ hx
      refine Set.mem_iUnion₂.mpr ⟨Fin.castLE hmd' i, Set.mem_ofPred_eq.mpr ?_, ?_⟩
      · exact Fin.le_def.mpr (Fin.le_def.mp hik)
      · rwa [padStrata_castLE s hmd']
    · rw [padStrata_of_not_lt s d hk]
      simp

private lemma padStrata_isAffine {X : Scheme.{u}} {m d : ℕ}
    (s : AffineStratification X (Fin (m + 1))) (k : Fin (d + 1))
    (hLC : IsLocallyClosed (padStrata s d k)) :
    IsAffine (reducedInducedScheme (padStrata s d k) hLC) ∧
      IsAffineHom (reducedInducedInclusion (padStrata s d k) hLC) := by
  by_cases hk : (k : ℕ) < m + 1
  · let i : Fin (m + 1) := ⟨(k : ℕ), hk⟩
    let hTi := s.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed i
    let f := reducedInducedInclusion (s.strata i) hTi
    have : IsAffine (reducedInducedScheme (s.strata i) hTi) := s.isAffine i
    have : IsAffineHom f := s.isAffineHom i
    have : IsImmersion f := by
      dsimp [f, reducedInducedInclusion]
      infer_instance
    exact isAffine_reducedInduced_of_range_eq _ hLC f
      (by rw [range_reducedInducedInclusion, padStrata_of_lt s d hk])
  · have : IsEmpty (reducedInducedScheme (padStrata s d k) hLC) := ⟨fun y => by
      have hy : reducedInducedInclusion (padStrata s d k) hLC y ∈
          Set.range (reducedInducedInclusion (padStrata s d k) hLC) := ⟨y, rfl⟩
      rw [range_reducedInducedInclusion] at hy
      exact (padStrata_of_not_lt s d hk).le hy⟩
    exact ⟨inferInstance, inferInstance⟩

/-- An affine stratification indexed by `0, …, m` read as one indexed by `0, …, d`, for
`m ≤ d`: the indices beyond `m` carry the empty stratum, which is affine with affine
inclusion. -/
private def ofLe {X : Scheme.{u}} {m d : ℕ} (s : AffineStratification X (Fin (m + 1)))
    (hmd : m ≤ d) : AffineStratification X (Fin (d + 1)) :=
  { strata := padStrata s d
    isLocallyFiniteStratification := padStrata_isLocallyFiniteStratification s hmd
    isAffine := fun k => (padStrata_isAffine s k _).1
    isAffineHom := fun k => (padStrata_isAffine s k _).2 }

end AffineStratification

/-- On a quasi-compact quasi-separated scheme the bound `affineStratificationNumber X ≤ d` says
exactly that `X` has an affine stratification indexed by `0, …, d`, the characterisation of the
number in [Stacks, Tag 0F2V]. The hypothesis is what makes the infimum defining the number be
taken over a nonempty set of lengths: a scheme with no finite affine stratification has affine
stratification number zero, and then the left-hand side holds for every `d` with no
stratification to be had. -/
theorem affineStratificationNumber_le_iff (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (d : ℕ) :
    affineStratificationNumber X ≤ d ↔ Nonempty (AffineStratification X (Fin (d + 1))) := by
  refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
  obtain ⟨s⟩ := nonempty_affineStratification_affineStratificationNumber X
  exact ⟨AffineStratification.ofLe s h⟩

end AlgebraicGeometry

end
