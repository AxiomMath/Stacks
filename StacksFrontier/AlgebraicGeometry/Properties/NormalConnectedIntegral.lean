module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct

/-!
# Connected normal schemes are integral

A locally Noetherian normal scheme is a disjoint union of normal integral schemes
(Tag 033N), so a connected one is integral. A scheme smooth over a field is normal
(`AlgebraicGeometry.isNormal_of_smooth_over_field`), so a connected scheme smooth over a field is
integral.

## Main results

* `AlgebraicGeometry.isIntegral_of_isNormal_of_connectedSpace` — a connected locally Noetherian
  normal scheme is integral.
* `AlgebraicGeometry.isIntegral_of_smooth_of_connectedSpace` — a connected scheme smooth over a
  field is integral.

## References

* [Stacks Project, Tag 033N](https://stacks.math.columbia.edu/tag/033N)
* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A connected locally Noetherian normal scheme is integral.** By Tag 033N it is a disjoint
union of normal integral schemes, and a connected disjoint union has a single summand: the
underlying space of a coproduct of schemes is the disjoint union of the underlying spaces, and a
connected subset of a disjoint union lies in one summand. -/
theorem isIntegral_of_isNormal_of_connectedSpace (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsNormal X] [ConnectedSpace X] : IsIntegral X := by
  obtain ⟨ι, Y, -, hI, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct_integral_normal X).1 inferInstance
  have : ConnectedSpace (∐ Y : Scheme.{u}) :=
    e.hom.homeomorph.surjective.connectedSpace e.hom.homeomorph.continuous
  have : ConnectedSpace (Σ i, Y i) :=
    (sigmaMk Y).symm.surjective.connectedSpace (sigmaMk Y).symm.continuous
  obtain ⟨i, t, -, ht⟩ := Sigma.isConnected_iff.1 (isConnected_univ (α := Σ i, Y i))
  have hsurj : Function.Surjective (Sigma.ι Y i) := by
    intro z
    obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk Y).surjective z
    have hmem : (⟨j, y⟩ : Σ i, Y i) ∈ Sigma.mk i '' t := ht ▸ Set.mem_univ _
    obtain ⟨y', -, hy'⟩ := hmem
    cases hy'
    exact ⟨y', (sigmaMk_mk Y i y').symm⟩
  have : Surjective (Sigma.ι Y i) := ⟨hsurj⟩
  have : IsIso (Sigma.ι Y i) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩
  have := hI i
  have : IsIntegral (∐ Y : Scheme.{u}) := IsIntegral.of_isIso (Sigma.ι Y i)
  exact IsIntegral.of_isIso e.inv

/-- **A connected scheme smooth over a field is integral.** -/
theorem isIntegral_of_smooth_of_connectedSpace {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [ConnectedSpace X] : IsIntegral X :=
  have := isNormal_of_smooth_over_field f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isIntegral_of_isNormal_of_connectedSpace X

end AlgebraicGeometry
