module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.Representability
public import StacksFrontier.AlgebraicGeometry.Curves.BaseChangeTwistInputs
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.BaseChangeTwistLowCohomology

/-!
# The Picard functor of a smooth projective curve over a separably closed field is representable

[Stacks, Tag 0B9Z]. Since `k` is separably closed, `X` has a `k`-rational point
([Stacks, Tag 056U]) and is geometrically irreducible; the translation property of the gluing
step is [Stacks, Tag 0B9Y], `exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed`.

## Main results

* `Stacks.PicardFunctor.isRepresentable_picardFunctor_of_isSepClosed`: [Stacks, Tag 0B9Z].

## References

* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- **[Stacks, Tag 0B9Y]** for a smooth projective curve over a separably closed field, in the
form used by the gluing step. -/
theorem twistToNormalized_of_isSepClosed_of_isProjectiveVariety [IsSepClosed k]
    [IsCurve k (B.inclusion.map f)]
    [GeometricallyIrreducible (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
    [IsProper (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)] :
    TwistToNormalized B hX hk f := fun K _ _ _ f' p hp L hL =>
  have := hL
  exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed k K
    (B.inclusion.map f) f' p hp (IsProjectiveVariety.isProjective.isProjective) L

/-- **Stacks Project, Tag 0B9Z.** Let `k` be a separably closed field and `X` a smooth projective
curve over `k`. The Picard functor `Pic_{X/k}` is representable. -/
@[stacks 0B9Z]
theorem isRepresentable_picardFunctor_of_isSepClosed [IsSepClosed k]
    [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
    [IsProjectiveVariety k (B.inclusion.map f)] :
    (picardFunctor B hX hk f).IsRepresentable := by
  have : IsProper (B.inclusion.map f) := inferInstance
  have : IrreducibleSpace X := inferInstance
  have : GeometricallyIrreducible (B.inclusion.map f) :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X (B.inclusion.map f)
  have : Nonempty X := inferInstance
  obtain ⟨σ, hσ⟩ := Stacks.AbelMap.exists_section_of_isSepClosed (B.inclusion.map f)
  exact isRepresentable_picardFunctor_of_twistToNormalized B hX hk f σ hσ
    (twistToNormalized_of_isSepClosed_of_isProjectiveVariety B hX hk f)

end Stacks.PicardFunctor

end
