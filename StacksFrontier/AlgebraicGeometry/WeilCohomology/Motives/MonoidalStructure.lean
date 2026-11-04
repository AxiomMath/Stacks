module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Category
public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal

/-!
# The symmetric monoidal structure on Chow motives

The category `M_k` of Chow motives is symmetric monoidal for the tensor product
`(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)`, with unit `𝟏 = (Spec(k), 1, 0)` and with the
obvious associativity and commutativity constraints. The structure is inherited from the
symmetric monoidal structure on correspondences, `M_k` being the Karoubi envelope of the
category of correspondences.

## Main results

* `Stacks.WeilCohomology.CorrespondenceStructure.motiveMonoidalCategory`: `M_k` is monoidal.
* `Stacks.WeilCohomology.CorrespondenceStructure.motiveSymmetricCategory`: `M_k` is symmetric
  monoidal.
* `Stacks.WeilCohomology.CorrespondenceStructure.motive_tensorObj_X` and
  `Stacks.WeilCohomology.CorrespondenceStructure.motive_tensorObj_p`: the tensor product of
  `(X, p, m)` and `(Y, q, n)` is `(X × Y, p ⊗ q, m + n)`.
* `Stacks.WeilCohomology.CorrespondenceStructure.motive_tensorUnit_as` and
  `Stacks.WeilCohomology.CorrespondenceStructure.motive_tensorUnit_p`: the unit is
  `𝟏 = (Spec(k), 1, 0)`.
* `Stacks.WeilCohomology.CorrespondenceStructure.motive_associator_hom_f` and
  `Stacks.WeilCohomology.CorrespondenceStructure.motive_braiding_hom_f`: the associativity and
  commutativity constraints are the "obvious" ones, those of the ambient category.

## Implementation notes

The Tate twist `m` of a motive `(X, p, m)` is carried by the ambient symmetric monoidal category
rather than by a separate integer, so the twists add under the tensor product because the ambient
tensor product does; and the unit `(Spec(k), 1, 0)` is the unit of the ambient category with the
diagonal as its projector. The associativity and commutativity constraints are those of the
category of correspondences cut down by the projectors.

## References

* [Stacks Project, Tag 0FGC](https://stacks.math.columbia.edu/tag/0FGC)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Idempotents

universe v u w

namespace Stacks.WeilCohomology.CorrespondenceStructure

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
  (S : CorrespondenceStructure.{v, u, w} D)

/-- The category `M_k` of Chow motives is monoidal for the tensor product
`(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)`, given the monoidal structure on the category of
correspondences, which is taken as a hypothesis and passes to the Karoubi envelope. -/
@[stacks 0FGC "M_k is monoidal for (X,p,m) ⊗ (Y,q,n) = (X × Y, p ⊗ q, m+n)", instance_reducible]
def motiveMonoidalCategory : MonoidalCategory S.Motive :=
  inferInstance

/-- The category `M_k` of Chow motives is symmetric monoidal, with the associativity and
commutativity constraints of the category of correspondences cut down by the projectors, and with
unit `𝟏 = (Spec(k), 1, 0)`. -/
@[stacks 0FGC "M_k is symmetric monoidal with unit 1 = (Spec(k), 1, 0)", instance_reducible]
def motiveSymmetricCategory : SymmetricCategory S.Motive :=
  inferInstance

/-- The scheme underlying the tensor product of two motives is the product of the two schemes:
`(X, p, m) ⊗ (Y, q, n)` has first entry `X × Y`. -/
@[simp]
theorem motive_tensorObj_X (M N : S.Motive) : (M ⊗ N).X = M.X ⊗ N.X :=
  rfl

/-- The projector of a tensor product of motives is the exterior product of the two projectors:
`(X, p, m) ⊗ (Y, q, n)` has second entry `p ⊗ q`. -/
@[simp]
theorem motive_tensorObj_p (M N : S.Motive) : (M ⊗ N).p = M.p ⊗ₘ N.p :=
  rfl

/-- The associativity constraint of `M_k` is the graph of the associativity constraint of the
ambient category, cut down by the projectors. -/
@[stacks 0FGC "the associativity constraint of M_k is the obvious one"]
theorem motive_associator_hom_f (M N P : S.Motive) :
    (α_ M N P).hom.f = ((M ⊗ N) ⊗ P).p ≫ S.graph (α_ M.X.as N.X.as P.X.as).hom := by
  rw [Karoubi.associator_hom, Karoubi.ofComm_f, associator_hom]

/-- The commutativity constraint of `M_k` is the graph of the factor switch of the ambient
category, cut down by the projectors. -/
@[stacks 0FGC "the commutativity constraint of M_k is the obvious one"]
theorem motive_braiding_hom_f (M N : S.Motive) :
    (β_ M N).hom.f = (M ⊗ N).p ≫ S.graph (β_ M.X.as N.X.as).hom := by
  rw [Karoubi.braiding_hom, Karoubi.ofComm_f, braiding_hom]

/-- The scheme underlying the unit motive `𝟏 = (Spec(k), 1, 0)` is `Spec(k)`, the unit of the
ambient category. -/
@[stacks 0FGC "the unit of M_k is 1 = (Spec(k), 1, 0)"]
theorem motive_tensorUnit_as : (𝟙_ S.Motive).X.as = 𝟙_ D :=
  rfl

/-- The projector of the unit motive `𝟏 = (Spec(k), 1, 0)` is the diagonal correspondence. -/
@[stacks 0FGC "the projector of the unit of M_k is the diagonal 1"]
theorem motive_tensorUnit_p : (𝟙_ S.Motive).p = S.id (𝟙_ D) :=
  rfl

end Stacks.WeilCohomology.CorrespondenceStructure

end
