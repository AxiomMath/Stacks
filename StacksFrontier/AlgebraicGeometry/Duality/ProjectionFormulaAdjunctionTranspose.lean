module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula

/-!
# The abstract adjunction-tensor morphism, read through the adjunction

Let `L ⊣ R` be an adjunction, let `A` and `B` be binary functors on the two categories and let
`α : A ⋙ L ⟶ (L × L) ⋙ B` be a morphism of bifunctors.
`CategoryTheory.adjunctionTensorMap` is the adjoint transpose of `α`
followed by the counit of `L ⊣ R` in the first argument of `B`.  The equation that transpose
satisfies is `CategoryTheory.map_adjunctionTensorMap_comp_counit`, beside the definition itself;
this file records the other form a calculation needs, the criterion that the equation
*determines* the morphism.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit`: any
  morphism satisfying that equation **is** the adjunction-tensor morphism.  This is the form a
  consumer uses: to identify a candidate with the canonical morphism it suffices to verify the
  equation, and no other morphism of the same type satisfies it.

## Implementation notes

*Why this is stated separately rather than unfolded at the point of use.*  The statement is one
step from the definition — `adjunctionTensorMap` is literally `adj.homEquiv _ _` of the
displayed composite — but that step must not be taken at the point of use.  Unfolding
`adjunctionTensorMap` and then transposing by rewriting with
`CategoryTheory.Adjunction.homEquiv_symm_apply` in a concrete instance leaves the two sides of
the equivalence to be matched by unification, and on the instance at the derived categories of a
ringed space that unification exhausts the default heartbeat limit inside the definitional
equality check.  Stated here, in bare categories and with both sides written out, there is
nothing left to unify: the consumer supplies the arguments and the proof is a single `exact`.
This is why the declaration below is phrased with every endpoint explicit.

## References

* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.AlgebraicGeometry.ProjectionFormula

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The transposed equation determines the abstract adjunction-tensor morphism.**  A morphism
`φ` of the same type whose image under `L`, followed by the counit of `L ⊣ R`, is the composite
of `CategoryTheory.map_adjunctionTensorMap_comp_counit` is equal to `adjunctionTensorMap`.

This is the shape in which the identification of a canonical morphism with a composite of
comparisons is proved: verify the equation after transposing, where every factor is computable,
and conclude the equation before transposing. -/
theorem eq_adjunctionTensorMap_of_map_comp_counit (G : D) (H : C)
    (φ : A.obj (R.obj G, H) ⟶ R.obj (B.obj (G, L.obj H)))
    (hφ : L.map φ ≫ adj.counit.app (B.obj (G, L.obj H)) =
      α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H))) :
    adjunctionTensorMap adj A B α G H = φ := by
  apply (adj.homEquiv (A.obj (R.obj G, H)) (B.obj (G, L.obj H))).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hφ,
    map_adjunctionTensorMap_comp_counit]

end Stacks.AlgebraicGeometry.ProjectionFormula

end
