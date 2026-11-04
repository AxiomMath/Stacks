module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.CoveringRefinement

/-!
# Standard fpqc coverings indexed by an arbitrary finite type

`AlgebraicGeometry.Scheme.ofArrows_mem_fpqcPrecoverage_of_finite` shows that a jointly surjective
family of flat morphisms from affine schemes to an affine scheme, indexed by `Fin m`, belongs to
`AlgebraicGeometry.Scheme.fpqcPrecoverage`. Families met in practice are indexed by the members of
a finite covering, a finite type which is not literally `Fin m`; this file removes the restriction
by reindexing along an equivalence with `Fin m`, which does not change the presieve.

## Main results

* `AlgebraicGeometry.Scheme.ofArrows_mem_fpqcPrecoverage_of_finite_index`: a finite, jointly
  surjective family of flat morphisms of affine schemes, indexed by any finite type, is an fpqc
  covering family.

## References

* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A **standard fpqc covering** indexed by an arbitrary finite type is an fpqc covering family: a
finite, jointly surjective family of flat morphisms from affine schemes to an affine scheme belongs
to `AlgebraicGeometry.Scheme.fpqcPrecoverage`. This is
`AlgebraicGeometry.Scheme.ofArrows_mem_fpqcPrecoverage_of_finite` after reindexing the family along
an equivalence of its index type with `Fin m`. -/
theorem Scheme.ofArrows_mem_fpqcPrecoverage_of_finite_index {T : Scheme.{u}} (hT : IsAffine T)
    {ι : Type*} [Finite ι] (Y : ι → Scheme.{u}) (q : ∀ i, Y i ⟶ T) (hY : ∀ i, IsAffine (Y i))
    (hq : ∀ i, Flat (q i)) (hcov : ∀ x : T, ∃ i, x ∈ Set.range (q i)) :
    Presieve.ofArrows Y q ∈ Scheme.fpqcPrecoverage T := by
  let e : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  rw [← Presieve.ofArrows_comp_eq_of_surjective q e.surjective]
  exact Scheme.ofArrows_mem_fpqcPrecoverage_of_finite hT (fun j ↦ Y (e j))
    (fun j ↦ q (e j)) (fun j ↦ hY (e j)) (fun j ↦ hq (e j)) fun x ↦ by
      obtain ⟨i, hi⟩ := hcov x
      obtain ⟨j, rfl⟩ := e.surjective i
      exact ⟨j, hi⟩

end AlgebraicGeometry
