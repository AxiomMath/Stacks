module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaStalks

/-!
# The projection formula at a morphism which is a closed embedding on spaces

Let `h : T ⟶ S` be a morphism of schemes, let `G` be a sheaf of `𝒪_T`-modules and let `H` be a
sheaf of `𝒪_S`-modules.  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` is the
comparison morphism

`h_* G ⊗_{𝒪_S} H ⟶ h_* (G ⊗_{𝒪_T} h^* H)`

of [Stacks, Tag 0FZE].  The tag proves it invertible for an affine `h` and quasi-coherent `G` and
`H`.  This module records that **the quasi-coherence hypotheses are not needed when the underlying
continuous map of `h` is a homeomorphism onto a closed subset**: for such an `h` the morphism is
invertible for arbitrary `G` and `H`.

That statement is already proved, for a morphism of ringed spaces, as
`Stacks.ClosedEmbeddingProjectionFormula.isIso_projectionFormulaMap'_of_isClosedEmbedding` — step
one of [Stacks, Tag 0B55], by two stalk computations. The only thing missing was that the
morphism it is about, `Stacks.ProjectionFormula.projectionFormulaMap'`, is the same morphism as the
scheme-level `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` — both are the
abstract comparison `Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap` of the
adjunction `h^* ⊣ h_*` and the pullback-tensor comparison of [Stacks, Tag 01CD], so the two `rfl`
lemmas `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq` and
`Stacks.ProjectionFormula.projectionFormulaMap'_eq` identify them.

## Main results

* `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq_projectionFormulaMap'` —
  the two spellings of the projection-formula morphism agree.
* `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding` —
  **the projection-formula morphism is invertible, with no quasi-coherence hypothesis, whenever
  the underlying continuous map is a closed embedding.**

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.ProjectionFormula

variable {T S : Scheme.{u}} (h : T ⟶ S)
  (G : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace))
  (H : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace))

/-- **The scheme-level and ringed-space-level projection-formula morphisms are the same
morphism.**  Both are the abstract comparison morphism of
`Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap` for the adjunction `h^* ⊣ h_*`
and the pullback-tensor comparison of [Stacks, Tag 01CD]; the two spellings differ only in which
abbreviation of the tensor bifunctor and of the adjunction is written down. -/
theorem projectionFormulaMap_eq_projectionFormulaMap' :
    projectionFormulaMap h G H =
      Stacks.ProjectionFormula.projectionFormulaMap' h.toLRSHom.toShHom G H :=
  (projectionFormulaMap_eq h G H).trans
    (Stacks.ProjectionFormula.projectionFormulaMap'_eq h.toLRSHom.toShHom G H).symm

/-- **The projection-formula morphism of [Stacks, Tag 0FZE] is invertible with no quasi-coherence
hypothesis, as soon as the underlying continuous map of `h` is a homeomorphism onto a closed
subset.**

The tag itself asks for an affine morphism and quasi-coherent modules.  Neither is needed here:
for a closed embedding of ringed spaces the morphism is invertible for arbitrary modules, by the
stalkwise argument of
`Stacks.ClosedEmbeddingProjectionFormula.isIso_projectionFormulaMap'_of_isClosedEmbedding` — the
stalk of a direct image along an inducing map is the stalk itself, the stalk of a tensor product
is the tensor product of the stalks ([Stacks, Tag 01CB]) and the stalk of a pullback is the base
change of the stalk ([Stacks, Tag 0098]), and off the image both stalks vanish. -/
theorem isIso_projectionFormulaMap_of_isClosedEmbedding
    (hh : Topology.IsClosedEmbedding (ConcreteCategory.hom h.toLRSHom.toShHom.hom.base)) :
    IsIso (projectionFormulaMap h G H) := by
  rw [projectionFormulaMap_eq_projectionFormulaMap']
  exact Stacks.ClosedEmbeddingProjectionFormula.isIso_projectionFormulaMap'_of_isClosedEmbedding
    h.toLRSHom.toShHom G H hh

end Stacks.AlgebraicGeometry.ProjectionFormula

end

end
