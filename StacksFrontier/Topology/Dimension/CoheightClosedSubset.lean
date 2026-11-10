module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

/-!
# The dimension of a closed set of points of large codimension

Let `X` be a quasi-sober `T₀` space of Krull dimension at most `d`, ordered by specialization so
that a point lies below its generizations, and let `S ⊆ X` be a closed subset every point of
which has coheight at least `j` (on a scheme the coheight of a point is the dimension of its local
ring). Then `S` has Krull dimension at most `d - j`, and if `j > d` then `S` is empty.

A chain of irreducible closed subsets of `S` is a chain of irreducible closed subsets of `X`
ending at the closure of a point `η` of `S`, and it can be continued above that closure by a
chain of length `coheight η ≥ j`; the concatenation has length at most `d`.

## Main results

* `Stacks.Topology.coheight_le_of_topologicalKrullDim_le`: every point has coheight at most the
  dimension of the space.
* `Stacks.Topology.topologicalKrullDim_le_of_le_coheight`: the dimension bound for `S`.

## References

* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3), the step "the modules
  `SheafExt^q(F, G)` have support of dimension at most `d - q`".
-/

@[expose] public section

open Order TopologicalSpace Topology

namespace Stacks.Topology

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

/-- The coheight of an irreducible closed subset of `X` is the coheight of its generic point for
the specialization order. -/
lemma coheight_irreducibleCloseds_eq (T : IrreducibleCloseds X) :
    coheight T = @coheight X (specializationPreorder X) T.2.genericPoint := by
  let : PartialOrder X := specializationOrder X
  exact (coheight_orderIso (irreducibleSetEquivPoints (α := X)) T).symm

/-- **Every point has coheight at most the dimension.** -/
theorem coheight_le_of_topologicalKrullDim_le {d : ℕ} (hX : topologicalKrullDim X ≤ d)
    (x : X) : (@coheight X (specializationPreorder X) x : WithBot ℕ∞) ≤ d := by
  let : PartialOrder X := specializationOrder X
  have h := coheight_le_krullDim ((irreducibleSetEquivPoints (α := X)).symm x)
  rw [coheight_orderIso (irreducibleSetEquivPoints (α := X)).symm x] at h
  exact h.trans hX

/-- **A closed set of points of coheight at least `j` has dimension at most `d - j`.** -/
theorem topologicalKrullDim_le_of_le_coheight (S : Set X) (hS : IsClosed S) {d j : ℕ}
    (hX : topologicalKrullDim X ≤ d)
    (hj : ∀ x ∈ S, (j : ℕ∞) ≤ @coheight X (specializationPreorder X) x) :
    topologicalKrullDim S ≤ ((d - j : ℕ) : WithBot ℕ∞) := by
  -- the inclusion of irreducible closed subsets of `S` into those of `X`
  let φ : IrreducibleCloseds S → IrreducibleCloseds X := fun T =>
    ⟨Subtype.val '' (T : Set S), T.2.image _ continuous_subtype_val.continuousOn,
      hS.isClosedEmbedding_subtypeVal.isClosedMap _ T.3⟩
  have hφ : StrictMono φ := fun _ _ h => Subtype.val_injective.image_strictMono h
  have hsub : ∀ T : IrreducibleCloseds S, ((φ T : Set X)) ⊆ S := by
    rintro T _ ⟨y, -, rfl⟩
    exact y.2
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_height]
  refine iSup_le fun T => ?_
  have h2 : (j : ℕ∞) ≤ coheight (φ T) := by
    rw [coheight_irreducibleCloseds_eq]
    exact hj _ (hsub T ((φ T).2.isGenericPoint_genericPoint (φ T).3).mem)
  have h3 : ((height (φ T) + coheight (φ T) : ℕ∞) : WithBot ℕ∞) ≤ d := by
    refine le_trans ?_ hX
    have hne : Nonempty (IrreducibleCloseds X) := ⟨φ T⟩
    unfold topologicalKrullDim
    rw [krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
    exact le_iSup (fun a : IrreducibleCloseds X => height a + coheight a) (φ T)
  have h4 : height T + j ≤ (d : ℕ∞) :=
    (add_le_add (height_le_height_apply_of_strictMono φ hφ T) h2).trans (WithBot.coe_le_coe.mp h3)
  have hfin : height T ≠ ⊤ := by
    intro h
    rw [h, top_add] at h4
    exact ENat.natCast_ne_top d (top_le_iff.mp h4)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hm] at h4 ⊢
  have h5 : m + j ≤ d := by exact_mod_cast h4
  exact WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : m ≤ d - j))

end Stacks.Topology
