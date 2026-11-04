module

public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoverings

/-!
# Reindexing a standard ph covering

The index type of a standard ph covering is finite but otherwise arbitrary, and in particular
its universe is unrelated to the universe of the schemes involved. This file records that the
notion is invariant under a bijection of index types, which is what moves a standard ph
covering into a prescribed index universe.

## Main results

* `AlgebraicGeometry.StandardPHCovering.reindex`: a standard ph covering stays one after
  reindexing its members along a bijection of index types.

## References

* [Stacks Project, Tag 0DBD](https://stacks.math.columbia.edu/tag/0DBD)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- Reindexing a standard ph covering along a bijection of index types gives a standard ph
covering. Since the index type is finite it is in bijection with `ULift (Fin n)` for a
suitable `n`, so this moves a standard ph covering into any prescribed index universe. -/
theorem StandardPHCovering.reindex {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} {ι' : Type w} (hf : StandardPHCovering f)
    (e : ι' ≃ ι) : StandardPHCovering (X := fun i => X (e i)) fun i => f (e i) := by
  have : Finite ι := hf.finite
  obtain ⟨U, g, j, hg, hg', hj, hcover, hcomp⟩ := hf.exists_presentation
  refine ⟨Finite.of_equiv ι e.symm, fun i => hf.isAffine (e i), U, g, fun i => j (e i), hg,
    hg', fun i => hj (e i), ?_, fun i => hcomp (e i)⟩
  rw [e.surjective.iUnion_comp fun i => Set.range (j i)]
  exact hcover

end AlgebraicGeometry

end
