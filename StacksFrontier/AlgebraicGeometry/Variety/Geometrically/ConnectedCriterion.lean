module

public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedGalois
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure

/-!
# A criterion for geometric connectedness

Let `T ⟶ X` be a morphism of schemes over a field. If `T` is geometrically connected and
`X` is connected, then `X` is geometrically connected.

## Main results

* `AlgebraicGeometry.geometricallyConnected_of_comp_of_connectedSpace` gives geometric
  connectedness of `X` from connectedness of `X` and geometric connectedness of a scheme
  mapping to it over the base field.

## Implementation notes

A scheme over `k` is represented by its structure morphism to `Spec k`. Given
`f : T ⟶ X` and the structure morphism `p : X ⟶ Spec k`, the induced structure morphism on
`T` is the composite `f ≫ p`; this incorporates the condition that `f` is a morphism over `k`.

## References

* [EGA IV, Corollaire 4.5.13.1(i)]
* [Stacks Project, Tag 056R](https://stacks.math.columbia.edu/tag/056R)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If a connected scheme over a field admits a morphism over that field from a geometrically
connected scheme, then it is geometrically connected. -/
@[stacks 056R]
public lemma geometricallyConnected_of_comp_of_connectedSpace
    (k : Type u) [Field k] {T X : Scheme.{u}} (f : T ⟶ X)
    (p : X ⟶ Spec (.of k)) [GeometricallyConnected (f ≫ p)] [ConnectedSpace X] :
    GeometricallyConnected p := by
  let K := SeparableClosure k
  apply (geometricallyConnected_iff_connectedSpace_baseChange k K p).2
  by_contra h
  exact (not_connectedSpace_of_galois_baseChange k K f p
    (AlgebraicGeometry.pullback_of_geometrically
      (inferInstance : GeometricallyConnected (f ≫ p)).geometrically_connectedSpace K
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) h) ‹ConnectedSpace X›

end AlgebraicGeometry
