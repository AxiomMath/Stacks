module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Products of geometrically integral schemes over a field

The fibre product over a field `k` of two geometrically integral `k`-schemes is geometrically
integral. A morphism is geometrically integral exactly when it is geometrically reduced and
geometrically irreducible. The product of two geometrically reduced schemes over a field is
geometrically reduced (Stacks 035Z, `AlgebraicGeometry.geometricallyReduced_pullback_over_field`),
and geometric irreducibility is stable under composition of universally open morphisms
(`AlgebraicGeometry.GeometricallyIrreducible.comp`). Every morphism to the spectrum of a field is
universally open, and the first projection is a base change of the second structure morphism.

This is the form in which the theorem of the cube uses the product `P ×_k Z` of two abelian
varieties (or varieties) over `k`.

## Main results

* `AlgebraicGeometry.Cube.geometricallyIntegral_fst_comp` — the product over `k` of two
  geometrically integral `k`-schemes is geometrically integral over `k`.

## References

* [Stacks Project, Tag 035Z](https://stacks.math.columbia.edu/tag/035Z)
* [Stacks Project, Tag 038F](https://stacks.math.columbia.edu/tag/038F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cube

/-- The fibre product over a field `k` of two geometrically integral `k`-schemes is
geometrically integral over `k`: it is geometrically reduced (Stacks 035Z) and geometrically
irreducible (Stacks 038F), the structure morphisms to `Spec k` being universally open. -/
@[ega "IV 4.5.8" "(ii), special case", ega "IV 4.6.5"]
instance geometricallyIntegral_fst_comp {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyIntegral f] [GeometricallyIntegral g] :
    GeometricallyIntegral (pullback.fst f g ≫ f) :=
  have := geometricallyReduced_pullback_over_field f g
  have := GeometricallyIrreducible.comp (pullback.fst f g) f
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end AlgebraicGeometry.Cube

end
