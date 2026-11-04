module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DiagonalRepresentation

/-!
# Uniqueness of the diagonal pro-object

An inverse sequence representing the functor of points of the colimit of a countable system of
pro-objects is determined up to pro-isomorphism. In particular, the diagonal sequence of
`CategoryTheory.Pro.exists_diagonalRepresentation` is uniquely pro-isomorphic to any other
representation of that functor of points.

## Main results

* `CategoryTheory.Pro.diagonalRepresentation_uniqueUpToIso`: there is a unique pro-morphism from
  the diagonal sequence to any other system representing the same colimit compatible with the
  comparison isomorphisms, and it has a two-sided inverse.

## References

* [Stacks Project, Tag 0G53](https://stacks.math.columbia.edu/tag/0G53)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace CategoryTheory.Pro

/-- The diagonal inverse sequence is uniquely pro-isomorphic to any other representation `G` of
the same functor of points: there is a unique pro-morphism to `G` compatible with the comparison
isomorphisms, and it has a two-sided inverse. -/
@[stacks 0G53 "diagonal_uniqueness"]
public theorem diagonalRepresentation_uniqueUpToIso {C : Type u} [Category.{v} C]
    (P : Functor ℕ (Functor C (Type v))) (M : ℕ → Functor ℕᵒᵖ C)
    (e : ∀ i, P.obj i ≅ Pro.coyonedaColim (liftedInverseSequence (M i)))
    (r : DiagonalRepresentation P M e) {I : Type v} [Category.{v} I]
    (G : Functor I C) (eG : colimit P ≅ Pro.coyonedaColim G) :
    ∃! φ : Pro.Hom (liftedInverseSequence r.system) G,
      (∃ ψ : Pro.Hom G (liftedInverseSequence r.system),
        (Pro.homEquiv G (liftedInverseSequence r.system)).symm ψ ≫
            (Pro.homEquiv (liftedInverseSequence r.system) G).symm φ =
          𝟙 (Pro.coyonedaColim (liftedInverseSequence r.system)) ∧
        (Pro.homEquiv (liftedInverseSequence r.system) G).symm φ ≫
            (Pro.homEquiv G (liftedInverseSequence r.system)).symm ψ =
          𝟙 (Pro.coyonedaColim G)) ∧
      eG.hom ≫ (Pro.homEquiv (liftedInverseSequence r.system) G).symm φ =
        r.comparison.hom := by
  refine ⟨Pro.homEquiv _ _ (eG.inv ≫ r.comparison.hom), ?_, ?_⟩
  · refine ⟨⟨Pro.homEquiv _ _ (r.comparison.inv ≫ eG.hom), ?_, ?_⟩, ?_⟩ <;> simp [Category.assoc]
  · rintro φ' ⟨_, h⟩
    apply (Pro.homEquiv _ _).symm.injective
    simpa [Category.assoc] using congrArg (eG.inv ≫ ·) h

end CategoryTheory.Pro
