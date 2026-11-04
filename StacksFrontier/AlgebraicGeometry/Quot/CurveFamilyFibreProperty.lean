module

public import StacksFrontier.AlgebraicGeometry.Quot.SemistableCurveFamilies

/-!
# Properties of the fibres of a family of curves

Let `f : X → S` be a family of curves and `P` a property of schemes over a field. The fibre of
`f` at a field-valued point `Spec(k) → S` is the base change `X_k`, an algebraic space over `k`;
the family *has fibre satisfying `P` at the point* when that fibre is presented by a scheme over
`k` which has `P`. Such a statement passes to every family mapping to `f`, at every point of its
base: a morphism of families is a cartesian square, so the fibre of the source at a point is the
fibre of the target at the image point.

The case of interest is `P` = "has no rational tail" ([Stacks, Tag 0E3H]), which is condition
(1) of [Stacks, Tag 0E6Y] and one of the fibre conditions of semistability
([Stacks, Tag 0E6Z]).

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasFibreSatisfying`: the fibre at a field-valued point of the
  base is presented by a scheme over the field which satisfies a given property.
* `AlgebraicGeometry.CurveFamily.HasNoRationalTailFibre`: the fibre at a field-valued point has
  no rational tail.

## Main results

* `AlgebraicGeometry.CurveFamily.hasFibreSatisfying_of_hom`: a family mapping to a family whose
  fibre at the image of a point satisfies `P` has fibre satisfying `P` at that point.
* `AlgebraicGeometry.CurveFamily.hasNoRationalTailFibre_of_hom`: the same for the absence of
  rational tails.
* `AlgebraicGeometry.IsSemistableCurveFamily.hasNoRationalTailFibre`: the fibres of a semistable
  family have no rational tail.

## Implementation notes

As in `AlgebraicGeometry.IsSemistableCurveFamily`, a point of the base is a field-valued point
in the sense of Stacks 03BU, and the fibre, a priori an algebraic space, is presented by a
scheme `V` of the site together with a structure morphism to the spectrum of the field which
exhibits `V` as the fibre product. The property is asked of some presentation; since two
presentations are isomorphic over the field, this is no restriction for a property invariant
under isomorphism.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The fibre of a family of curves at a field-valued point `p` of its base is presented by a
scheme over the field of `p` which satisfies `P`. -/
def CurveFamily.HasFibreSatisfying
    (P : ∀ (k : Type u) [Field k] {V : Scheme.{u}}, (V ⟶ Spec (.of k)) → Prop)
    (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) : Prop :=
  ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
    (q : yoneda.obj V ⟶ X.total.obj),
    IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) ∧
      P p.carrier ((BigFppfOver.toScheme B integerBase hZ).map v)

/-- The fibre of a family of curves at a field-valued point of its base has no rational tail
([Stacks, Tag 0E3H]). -/
abbrev CurveFamily.HasNoRationalTailFibre (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) : Prop :=
  X.HasFibreSatisfying B hZ
    (fun k _ V f => letI : V.Over (Spec (.of k)) := ⟨f⟩; ∀ C : V.IdealSheafData,
      ¬ IsRationalTail k V C) p

/-- **Fibre conditions pass along morphisms of families of curves.** For a morphism `φ : X ⟶ Y`
of families and a field-valued point `p` of the base of `X`, if the fibre of `Y` at the image of
`p` satisfies `P` then so does the fibre of `X` at `p`: pasting the cartesian square of `φ`
with the presentation of the fibre of `Y` presents the fibre of `X`. -/
theorem CurveFamily.hasFibreSatisfying_of_hom
    {P : ∀ (k : Type u) [Field k] {V : Scheme.{u}}, (V ⟶ Spec (.of k)) → Prop}
    {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hY : Y.HasFibreSatisfying B hZ P
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p)) :
    X.HasFibreSatisfying B hZ P p := by
  obtain ⟨V, v, q, hpb, hV⟩ := hY
  have hval : yonedaEquiv.symm
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap φ.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  rw [hval] at hpb
  have hc := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  let q' : yoneda.obj V ⟶ X.total.obj :=
    hc.lift q (yoneda.map v ≫ yonedaEquiv.symm p.value) (by rw [hpb.w, Category.assoc]; rfl)
  have hq' : q' ≫ φ.totalMap.hom = q := hc.lift_fst _ _ _
  refine ⟨V, v, q', ?_, hV⟩
  refine IsPullback.of_right (h₁₂ := φ.totalMap.hom) (h₂₂ := (schemeSpaceMap φ.baseMap).hom)
    (v₁₃ := Y.toBase.hom) ?_ (hc.lift_snd _ _ _) hc
  rw [hq']
  exact hpb

/-- **Absence of rational tails in the fibres passes along morphisms of families of curves**:
the fibre of `X` at a point is the fibre of `Y` at the image point. -/
theorem CurveFamily.hasNoRationalTailFibre_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hY : Y.HasNoRationalTailFibre B hZ
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p)) :
    X.HasNoRationalTailFibre B hZ p :=
  CurveFamily.hasFibreSatisfying_of_hom B hZ φ p hY

/-- The fibres of a semistable family of curves have no rational tail. -/
theorem IsSemistableCurveFamily.hasNoRationalTailFibre {X : CurveFamily B hZ}
    (hX : IsSemistableCurveFamily B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    X.HasNoRationalTailFibre B hZ p := by
  obtain ⟨V, v, q, hpb, hV⟩ := hX.2 p
  exact ⟨V, v, q, hpb, hV.2⟩

end AlgebraicGeometry

end
