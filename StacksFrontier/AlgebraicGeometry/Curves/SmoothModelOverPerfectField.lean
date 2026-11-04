module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# The nonsingular projective model over a perfect field is smooth

Let `k` be a field and let `X` be a curve over `k`. A nonsingular projective model of `X` is a
regular projective curve over `k` whose function field is `k`-isomorphic to that of `X`. Such a
model is regular by construction, but regularity of a scheme over `k` is in general weaker than
smoothness of its structure morphism, and the two can differ in positive characteristic. When
`k` is perfect they agree, so the model is a smooth projective curve.

## Main results

* `AlgebraicGeometry.NonsingularProjectiveModel.smooth_structureMap`: over a perfect field the
  structure morphism of a nonsingular projective model is smooth.
* `AlgebraicGeometry.NonsingularProjectiveModel.isSmoothProjectiveCurve`: Tag 0BY3, the
  nonsingular projective model of a curve over a perfect field is a smooth projective curve.

## Implementation notes

Smoothness is Mathlib's `AlgebraicGeometry.Smooth`, the morphism property, rather than a
pointwise condition; it is reached from the pointwise condition through
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff`, which needs the structure morphism to be
locally of finite presentation. The model is a curve, hence locally of finite type, and the base
`Spec k` is Noetherian, so `AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType`
supplies that. Point by point, the regularity field of the model gives a regular local ring at
every point by `AlgebraicGeometry.isRegular_tfae`, Tag 0B8X
(`AlgebraicGeometry.smoothAt_locus_eq_regular_locus`) converts this to pointwise smoothness over
the perfect field, and `InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap` identifies that
with membership in the smooth locus.

The projectivity and curve clauses of the conclusion are the corresponding fields of
`AlgebraicGeometry.NonsingularProjectiveModel`, exactly as in the source, where they are part of
Definition 0BY2 of a nonsingular projective model; the content of the lemma is the smoothness
clause. The statement quantifies over all nonsingular projective models rather than over a chosen
one, which is the stronger reading and avoids appealing to the uniqueness of Theorem 0BY1.

## References

* [Stacks Project, Tag 0BY3](https://stacks.math.columbia.edu/tag/0BY3)
* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace NonsingularProjectiveModel

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsCurve k sX]

/-- The structure morphism of a nonsingular projective model is locally of finite presentation:
it is locally of finite type because the model is a curve, and the base is Noetherian. -/
public theorem locallyOfFinitePresentation_structureMap
    (M : NonsingularProjectiveModel k X sX) :
    LocallyOfFinitePresentation M.structureMap := by
  let _ : IsCurve k M.structureMap := M.isCurve
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance

/-- Over a perfect field the structure morphism of a nonsingular projective model is smooth: the
model is regular, so its local rings are regular, which over a perfect field is smoothness at
every point, and the smooth locus is then the whole model. -/
public theorem smooth_structureMap [PerfectField k]
    (M : NonsingularProjectiveModel k X sX) :
    Smooth M.structureMap := by
  let _ : IsCurve k M.structureMap := M.isCurve
  let _ : LocallyOfFinitePresentation M.structureMap :=
    M.locallyOfFinitePresentation_structureMap
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  have hreg : IsRegularLocalRing (M.Y.presheaf.stalk x) :=
    (((isRegular_tfae M.Y).out 1 2 rfl rfl).mp M.isRegular).2 x
  exact InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap M.structureMap x
    ((Set.ext_iff.mp (smoothAt_locus_eq_regular_locus k M.structureMap) x).2 hreg)

/-- **Stacks Project, Tag 0BY3.** Let `k` be a field, let `X` be a curve over `k` and let `Y` be
a nonsingular projective model of `X`. If `k` is perfect then `Y` is a smooth projective
curve. -/
@[stacks 0BY3]
public theorem isSmoothProjectiveCurve [PerfectField k]
    (M : NonsingularProjectiveModel k X sX) :
    Smooth M.structureMap ∧ IsProjectiveVariety k M.structureMap ∧
      IsCurve k M.structureMap :=
  ⟨M.smooth_structureMap, M.isProjectiveVariety, M.isCurve⟩

end NonsingularProjectiveModel

end AlgebraicGeometry

end
