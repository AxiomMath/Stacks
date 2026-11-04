module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Normal locally Noetherian schemes as disjoint unions

A locally Noetherian scheme is normal exactly when it is a disjoint union of normal integral
schemes, and a Noetherian scheme is normal exactly when it is a *finite* such disjoint union.

## Main results

* `AlgebraicGeometry.isNormal_iff_exists_iso_coproduct_integral_normal` characterizes normal
  locally Noetherian schemes as coproducts of normal integral schemes.
* `AlgebraicGeometry.isNormal_iff_exists_iso_finite_coproduct_integral_normal` characterizes
  normal Noetherian schemes as finite coproducts of normal integral schemes.

## Implementation notes

A disjoint union is represented by an isomorphism with the categorical coproduct of a family of
schemes; the index type may be empty, as required for the empty scheme, and is required to be
finite only in the Noetherian case.

## References

* [Stacks Project, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
* [Stacks Project, Tag 033N](https://stacks.math.columbia.edu/tag/033N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A locally Noetherian scheme is normal if and only if it is isomorphic to a coproduct of normal
integral schemes. -/
@[stacks 033N]
public theorem isNormal_iff_exists_iso_coproduct_integral_normal
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsNormal X ↔
      ∃ (ι : Type u) (Y : ι → Scheme.{u})
          (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsIntegral (Y i)),
        Nonempty (X ≅ ∐ Y) :=
  isNormal_iff_exists_iso_coproduct (X := X) (finite_irreducibleComponents_of_isCompact X)

/-- A Noetherian scheme is normal if and only if it is isomorphic to a finite coproduct of normal
integral schemes. -/
@[stacks 033M]
public theorem isNormal_iff_exists_iso_finite_coproduct_integral_normal
    (X : Scheme.{u}) [IsNoetherian X] :
    IsNormal X ↔
      ∃ (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u})
          (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsIntegral (Y i)),
        Nonempty (X ≅ ∐ Y) := by
  have h := isNormal_iff_exists_iso_coproduct_integral_normal X
  constructor
  · intro hnormal
    obtain ⟨ι, Y, hnormalY, hintegralY, ⟨e⟩⟩ := h.mp hnormal
    let : CompactSpace (Σ i, Y i) := (e.hom.homeomorph.trans (sigmaMk Y).symm).compactSpace
    let : TopologicalSpace ι := ⊥
    let : DiscreteTopology ι := ⟨rfl⟩
    have hsurj : Function.Surjective (Sigma.fst : (Σ i, Y i) → ι) := fun i ↦ by
      let : IsIntegral (Y i) := hintegralY i
      exact ⟨⟨i, Classical.choice (IsIntegral.nonempty : Nonempty (Y i))⟩, rfl⟩
    have hc : IsCompact (Set.univ : Set ι) := by
      simpa [Set.range_eq_univ.mpr hsurj] using isCompact_univ.image
        (continuous_sigma fun _ ↦ continuous_const : Continuous (Sigma.fst : (Σ i, Y i) → ι))
    let : Finite ι := Finite.of_finite_univ hc.finite_of_discrete
    exact ⟨ι, inferInstance, Y, hnormalY, hintegralY, ⟨e⟩⟩
  · rintro ⟨ι, _, Y, hnormalY, hintegralY, e⟩; exact h.mpr ⟨ι, Y, hnormalY, hintegralY, e⟩

end AlgebraicGeometry

end
