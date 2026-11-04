module

public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Krull dimension and irreducibility from an open cover

Two facts about a topological space `X` covered by open subsets `Uᵢ`.

* If every `Uᵢ` has Krull dimension at most `n`, so does `X`: a chain of irreducible closed
  subsets of `X` restricts to a chain of the same length in any open set meeting its smallest
  member ([Stacks, Tag 0B7I]).
* If every `Uᵢ` is irreducible and all of them contain a common point, `X` is irreducible: each
  `Uᵢ` lies in the closure of `U_j`, an irreducible open set being dense in itself.

## Main results

* `topologicalKrullDim_le_of_isOpen_cover`.
* `irreducibleSpace_of_isOpen_cover`.

## References

* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
-/

@[expose] public section

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] {ι : Type*}

/-- **A space covered by open subsets of dimension at most `n` has dimension at most `n`.** -/
@[ega "0 14.1.7" "partial"]
theorem topologicalKrullDim_le_of_isOpen_cover (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcov : ∀ x, ∃ i, x ∈ U i) {n : WithBot ℕ∞} (hn : ∀ i, topologicalKrullDim (U i) ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  obtain ⟨i, hi⟩ := hcov x
  refine le_trans ?_ (hn i)
  unfold TopologicalSpace.localKrullDim
  exact iInf₂_le_of_le (U i) (hU i) (iInf_le _ hi)

/-- **A space covered by irreducible open subsets with a common point is irreducible.** -/
@[ega "0 2.1.4" "special case"]
theorem irreducibleSpace_of_isOpen_cover [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hirr : ∀ i, IsIrreducible (U i)) (hcov : ∀ x, ∃ i, x ∈ U i) (x : X) (hx : ∀ i, x ∈ U i) :
    IrreducibleSpace X := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hclosure : closure (U i₀) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨i, hi⟩ := hcov y
    have hsub := subset_closure_inter_of_isPreirreducible_of_isOpen
      (hirr i).isPreirreducible (hU i₀) ⟨x, hx i, hx i₀⟩
    exact closure_mono Set.inter_subset_right (hsub hi)
  have h := (hirr i₀).closure
  rw [hclosure] at h
  exact (irreducibleSpace_def X).mpr h
