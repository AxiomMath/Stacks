module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaRight
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaRightDerived

/-!
# The right-handed projection formula along a closed embedding

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying continuous map is a
homeomorphism onto a closed subset.  This file states [Stacks, Tag 0B55] with the pushforward in
the right tensor factor: the right-handed projection-formula map

`K ⊗^𝐋_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗^𝐋_{𝒪_X} E)`

of `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaRight` is an
isomorphism for all `K` and `E`.

## Main results

* `isIso_projectionFormulaMapRight_of_isClosedEmbedding`: for `f` a closed embedding, the
  right-handed projection-formula map is an isomorphism for all `K` and `E`.

## Implementation notes

The module containing the proof is imported privately: its closure carries sheaf-level monoidal
coherence instances that make the `Abelian` instance on modules over a ringed space exceed
`synthInstance.maxSize` downstream, so this module exposes only the statement.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

/-! ### [Stacks, Tag 0B55], with the pushforward in the right tensor factor -/

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The projection formula along a closed embedding, with the pushforward in the right tensor
factor.**  Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying
continuous map is a homeomorphism onto a closed subset.  Then the projection-formula morphism

`K ⊗^𝐋_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗^𝐋_{𝒪_X} E)`

is an isomorphism for every `K` in `D(𝒪_Y)` and every `E` in `D(𝒪_X)`. -/
@[stacks 0B55 "the right-handed form: the pushforward in the right tensor factor, \
K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E), for an arbitrary morphism of ringed spaces whose underlying \
map is a homeomorphism onto a closed subset and arbitrary K and E"]
theorem isIso_projectionFormulaMapRight_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMapRight f K E) := by
  obtain ⟨B, g, hB, -, hg, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y
    (DerivedCategory.Q.objPreimage K)
  have hgiso : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  have eK : DerivedCategory.Q.obj B ≅ K :=
    asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  rw [← isIso_projectionFormulaMapRight_congr f eK (DerivedCategory.Q.objObjPreimageIso E)]
  exact
    Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_projectionFormulaMapRight_Q
      f hf B (DerivedCategory.Q.objPreimage E) hB

end Stacks.Cohomology.DerivedProjectionFormula

end

end
