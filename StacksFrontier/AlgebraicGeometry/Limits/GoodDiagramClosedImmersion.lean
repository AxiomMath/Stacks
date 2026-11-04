module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteTypeModel

/-!
# Good diagrams along a closed immersion

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, in the sense of `AlgebraicGeometry.LimitNoetherianSituation`, and let
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram` be the finite-type model diagram of Tag
0CNN. A closed immersion `u : X ⟶ Z` over `S` transports a good diagram for `Z` to a good
diagram for `X` with the *same* stage, model and model morphism.

This is the step "choose a closed immersion `X ⟶ X'` with `X' ⟶ S` proper and of finite
presentation, and use the model of `X'`" in the proof of Tag 0CNV, and more generally the reason
one may enlarge `X` before choosing a model: by Remark 0CNS the choice is immaterial.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofIsClosedImmersion` transports a good
  diagram along a closed immersion over the limit.

## Implementation notes

`GoodDiagram.ofIsClosedImmersion` keeps the index, the model and the model morphism of the given
diagram and composes only the horizontal morphism; the induced morphism into the base change of
the model is then `u ≫ GZ.induced`, a composite of two closed immersions. No hypothesis on the
index type is needed, in particular no smallness: the construction uses only the commuting
square of the given diagram.

## References

* [Stacks Project, Tag 0CNN](https://stacks.math.columbia.edu/tag/0CNN)
* [Stacks Project, Tag 0CNV](https://stacks.math.columbia.edu/tag/0CNV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

namespace LimitNoetherianSituation

namespace GoodDiagram

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I}

section ClosedImmersion

variable {X Z : Scheme.{u}} {pZ : Z ⟶ D.limitScheme} {pX : X ⟶ D.limitScheme}

/-- A good diagram for `pZ : Z ⟶ S` and a closed immersion `u : X ⟶ Z` over `S` give a good
diagram for `pX : X ⟶ S` with the same stage, model and model morphism. -/
noncomputable def ofIsClosedImmersion (GZ : GoodDiagram D pZ) {u : X ⟶ Z}
    [IsClosedImmersion u] (hu : u ≫ pZ = pX) : GoodDiagram D pX :=
  have hcomm : pX ≫ D.limitCone.π.app (op GZ.index) = (u ≫ GZ.toModel) ≫ GZ.modelMap := by
    rw [← hu, Category.assoc, GZ.commutes, Category.assoc]
  have hlift : pullback.lift pX (u ≫ GZ.toModel) hcomm = u ≫ GZ.induced := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact hu.symm
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  { index := GZ.index
    W := GZ.W
    modelMap := GZ.modelMap
    toModel := u ≫ GZ.toModel
    commutes := hcomm
    locallyOfFiniteType := GZ.locallyOfFiniteType
    quasiCompact := GZ.quasiCompact
    isClosedImmersion := by
      rw [hlift]
      have : IsClosedImmersion GZ.induced := GZ.isClosedImmersion
      infer_instance }

/-- The good diagram `GZ.ofIsClosedImmersion hu` has the same stage index as `GZ`. -/
@[simp]
lemma ofIsClosedImmersion_index (GZ : GoodDiagram D pZ) {u : X ⟶ Z} [IsClosedImmersion u]
    (hu : u ≫ pZ = pX) : (GZ.ofIsClosedImmersion hu).index = GZ.index := rfl

/-- The good diagram `GZ.ofIsClosedImmersion hu` has the same model as `GZ`. -/
@[simp]
lemma ofIsClosedImmersion_W (GZ : GoodDiagram D pZ) {u : X ⟶ Z} [IsClosedImmersion u]
    (hu : u ≫ pZ = pX) : (GZ.ofIsClosedImmersion hu).W = GZ.W := rfl

/-- The good diagram `GZ.ofIsClosedImmersion hu` has the same model morphism as `GZ`. -/
@[simp]
lemma ofIsClosedImmersion_modelMap (GZ : GoodDiagram D pZ) {u : X ⟶ Z} [IsClosedImmersion u]
    (hu : u ≫ pZ = pX) : (GZ.ofIsClosedImmersion hu).modelMap = GZ.modelMap := rfl

/-- The morphism of `GZ.ofIsClosedImmersion hu` into the model is `u ≫ GZ.toModel`. -/
@[simp]
lemma ofIsClosedImmersion_toModel (GZ : GoodDiagram D pZ) {u : X ⟶ Z} [IsClosedImmersion u]
    (hu : u ≫ pZ = pX) : (GZ.ofIsClosedImmersion hu).toModel = u ≫ GZ.toModel := rfl

end ClosedImmersion

end GoodDiagram

end LimitNoetherianSituation

end AlgebraicGeometry

end
