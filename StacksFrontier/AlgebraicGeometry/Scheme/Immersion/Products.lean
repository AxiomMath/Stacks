module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Immersions and binary products of schemes

A binary product of open immersions of schemes is an open immersion, and the morphism to
`U ⨯ U` assembled from a kernel pair `t, s : R ⟶ U` of a morphism `g : U ⟶ V` is an
immersion.

Both are instances of the same mechanism: a morphism property of schemes stable under
composition and base change is stable under binary products, and a kernel pair presents the
base change of the diagonal of the target.

## Main results

* `AlgebraicGeometry.isOpenImmersion_prod_map`: a product of open immersions is an open
  immersion.
* `AlgebraicGeometry.isImmersion_prod_lift_of_isPullback`: the pair of the two projections of
  a kernel pair is an immersion into the self-product.
* `AlgebraicGeometry.isImmersion_comp_prod_lift_of_isPullback`: the restriction of a relation
  along an open immersion is an immersion into the self-product.

## Implementation notes

The product here is the categorical binary product `U ⨯ U` of schemes, that is the fibre
product over `Spec ℤ`, and not a fibre product over a chosen base. The diagonal of `U` for
that product is an immersion by Mathlib's instance for `prod.lift (𝟙 U) (𝟙 U)`.

## References

* [Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A binary product of open immersions of schemes is an open immersion.** Open immersions
are stable under composition and under base change, and `prod.map f g` is a composite of base
changes of `f` and of `g`. -/
@[ega "I 4.3.1" "special case"]
theorem isOpenImmersion_prod_map {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ W)
    [IsOpenImmersion f] [IsOpenImmersion g] : IsOpenImmersion (prod.map f g) :=
  MorphismProperty.prod_map (@IsOpenImmersion.{u}) f g inferInstance inferInstance

/-- **A kernel pair gives an immersion into the self-product.** If `t, s : R ⟶ U` is a kernel
pair of `g : U ⟶ V`, then `prod.lift t s : R ⟶ U ⨯ U` is an immersion, being a base change
of the diagonal of `V` along `prod.map g g`. -/
theorem isImmersion_prod_lift_of_isPullback {R U V : Scheme.{u}} (t s : R ⟶ U) (g : U ⟶ V)
    (h : IsPullback t s g g) : IsImmersion (prod.lift t s) :=
  MorphismProperty.of_isPullback (P := @IsImmersion.{u})
    (isPullback_diagonal_prod_of_kernelPair t s g h) inferInstance

/-- **The restriction of a relation along an open immersion is an immersion into the
self-product.** Let `t, s : R ⟶ U` be a pair of morphisms, let `i : W ⟶ U` be an open
immersion and let `e : L ⟶ R`, `p : L ⟶ W` satisfy `e ≫ t = p ≫ i`. Suppose `j : L ⟶ W` is
such that `j, p` is a kernel pair of some `g : W ⟶ W'` and `j ≫ i = e ≫ s`.

Then `e ≫ prod.lift s t` is an immersion: it equals the immersion `prod.lift j p` followed
by the open immersion `prod.map i i`.

This is the shape in which the relation of a presentation of an algebraic space, restricted
over an open subscheme of its chart, is tested for being an immersion. -/
theorem isImmersion_comp_prod_lift_of_isPullback {R U W W' L : Scheme.{u}}
    (t s : R ⟶ U) {i : W ⟶ U} (hi : IsOpenImmersion i) {g : W ⟶ W'}
    {e : L ⟶ R} {p j : L ⟶ W} (hjg : IsPullback j p g g)
    (hji : j ≫ i = e ≫ s) (hcond : e ≫ t = p ≫ i) :
    IsImmersion (e ≫ prod.lift s t) := by
  have := hi
  have := isImmersion_prod_lift_of_isPullback j p g hjg
  have := isOpenImmersion_prod_map i i
  have heq : e ≫ prod.lift s t = prod.lift j p ≫ prod.map i i := by
    refine prod.hom_ext ?_ ?_
    · simp [hji]
    · simp [hcond]
  rw [heq]
  infer_instance

end AlgebraicGeometry

end
