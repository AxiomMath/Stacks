module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationCompleteLocalProjective

/-!
# A proper algebraic space of fibre dimension one over a complete local ring is a projective scheme

**[Stacks, Tag 0AE7].** Let `(A, 𝔪, κ)` be a complete Noetherian local ring and `X` an algebraic
space over `Spec A`. If `X ⟶ Spec A` is proper and `dim(X_κ) ≤ 1`, then `X` is a scheme projective
over `A`.

This is
`AlgebraicGeometry.Space.C1605.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModificationCompleteLocalProjective.lean`), registered
here:
there are a scheme `Y` of the site, a projective (indeed H-projective) morphism `Y ⟶ Spec A` and an
isomorphism of `X` with the algebraic space `Y` over `Spec A`. The fibre `X_κ` is the adic fibre of
index `0` along `𝔪`.

## References

* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
-/

add_to_stacks 0AE7
  AlgebraicGeometry.Space.C1605.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one
