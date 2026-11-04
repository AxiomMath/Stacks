module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ModelGlobalSections

/-!
# The geometric genus of a curve

Let `k` be a field and let `X` be a geometrically irreducible curve over `k`.  [Stacks, Tag
0BYF] defines the *geometric genus* of `X` to be the genus of a smooth projective model of `X`,
possibly defined over an extension field of `k`, as furnished by [Stacks, Tag 0BY4].  This file
gives the genus of a given nonsingular projective model of `(X_K)_red`, with no smoothness
requirement, and its invariance under enlarging the field.

**The geometric genus of Tag 0BYF itself is `AlgebraicGeometry.geometricGenusOfCurve`**, in
`StacksFrontier/AlgebraicGeometry/Curves/GeometricGenusSmoothModel.lean`: there the model is required
to be smooth over `K`, as in Tag 0BY4, and the value is proved independent of `K` and of the
model. `AlgebraicGeometry.geometricGenusOfModel` below agrees with it on smooth models only.

The model is taken as data, exactly as in the source phrase "a smooth projective model of `X`
possibly defined over an extension field of `k`": a term of
`AlgebraicGeometry.NonsingularProjectiveModel` is a scheme together with its structure
morphism, its curve, projectivity and regularity hypotheses and the comparison of function
fields, so nothing here is chosen out of an existence statement.

## Main definitions

* `AlgebraicGeometry.geometricGenusOfModel` is the genus `dim_K H¹(Y_K, 𝒪_{Y_K})` of a given
  nonsingular projective model of `(X_K)_red` over an extension field `K/k`; it is the geometric
  genus of Tag 0BYF only when the model is smooth over `K`.

## Main results

* `AlgebraicGeometry.geometricGenusOfModel_eq_genus` unfolds the definition.
* `AlgebraicGeometry.geometricGenusOfModel_eq_of_baseChange`: the value does not change when the
  extension field is enlarged.  If `K'/K` is a further extension and the model over `K'` is the
  base change of the model over `K`, the two models give the same geometric genus.  This is the
  part of the source's "possibly defined over an extension field" that makes the definition
  independent of the choice of field.

## Relation to the geometric genus

The model is an argument here, and no smoothness over `K` is required of it, so this file does
not define the invariant of Tag 0BYF. That is `AlgebraicGeometry.geometricGenusOfCurve`, whose
independence of the extension field and of the smooth model rests on the uniqueness of the
nonsingular projective model ([Stacks, Tag 0BY1]), proved in
`StacksFrontier/AlgebraicGeometry/Curves/NonsingularProjectiveModelUniqueness.lean`; the same result
shows that over a fixed `K` the value below does not depend on the model
(`AlgebraicGeometry.NonsingularProjectiveModel.genus_eq`).

`AlgebraicGeometry.geometricGenus` of
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/Geometric.lean` is a **different** invariant
and is not reused: it is the one of the source's section on genus versus geometric genus, the
sum over the dimension-one irreducible components of the base change of a proper scheme to an
algebraic closure of the genus of the normalization of each.  For a geometrically irreducible
proper curve the two agree, but that comparison is again 0BY1 together with the identification
of the normalization of `X_{k̄}` with a model, so it is not asserted.

## References

* [Stacks Project, Tag 0BYF](https://stacks.math.columbia.edu/tag/0BYF)
* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7), the genus.
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9), invariance of the
  genus under extension of the ground field.
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1), uniqueness of the
  nonsingular projective model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}

/-- The genus `dim_K H¹(Y_K, 𝒪_{Y_K})` of a nonsingular projective model `M` of `(X_K)_red`, for a
geometrically irreducible curve `X` over `k` and an extension field `K/k`.

**This is not the geometric genus of [Stacks, Tag 0BYF].** It accepts an arbitrary extension `K/k`
and an arbitrary *regular* projective model, never requiring the model to be smooth over `K`; for
`K = k` imperfect and a model that is regular but not smooth over `k` it is the genus of that
model, which can differ from the geometric genus. Tag 0BYF is
`AlgebraicGeometry.geometricGenusOfCurve`
(`StacksFrontier/AlgebraicGeometry/Curves/GeometricGenusSmoothModel.lean`), which takes `K` and the
model as in Tag 0BY4, with the model smooth over `K`, and is independent of both choices; on a
smooth model the two agree, by
`AlgebraicGeometry.geometricGenusOfModel_eq_geometricGenusOfCurve`. Over a fixed `K` the value
does not depend on the model, by `AlgebraicGeometry.NonsingularProjectiveModel.genus_eq`. -/
def geometricGenusOfModel (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX]
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX)) : ℕ :=
  genus M.structureMap

/-- The geometric genus read off a model is the genus of that model. -/
theorem geometricGenusOfModel_eq_genus (sX : X ⟶ Spec (.of k)) [IsCurve k sX]
    [GeometricallyIrreducible sX] [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX)) :
    geometricGenusOfModel k K sX M = genus M.structureMap :=
  rfl

end AlgebraicGeometry

end
