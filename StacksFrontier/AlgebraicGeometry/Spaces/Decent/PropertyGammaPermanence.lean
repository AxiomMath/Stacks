module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RepresentablePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Decency passes to the source of a representable morphism

Let `f : X ⟶ Y` be a relatively representable morphism of presheaves on the big fppf site of a
scheme `S`, with `X` an algebraic space. If `Y` is decent, that is, every point of `Y` is
presented by a quasi-compact monomorphism from the spectrum of a field
(`AlgebraicGeometry.Space.IsDecentSpace`), then so is `X`. Between algebraic spaces this is
property `(γ)` of Stacks 03JX passing from the target of a representable morphism to its source.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_fieldMorphism_yoneda`: a field-valued point of a
  presheaf represented by an object of the site presents it by a quasi-compact morphism.
* `AlgebraicGeometry.Space.isDecentSpace_yoneda`: a presheaf represented by an object of the
  site is a decent algebraic space over `S`.
* `AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable`: decency passes from the
  target of a representable morphism to its source, when the source is an algebraic space.
* `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_relativelyRepresentable`:
  the same for `AlgebraicGeometry.Space.HasFiniteChartAndRelationFibersAtEveryPoint`, between
  algebraic spaces.
* `AlgebraicGeometry.Space.isDecentSpace_of_isClosedSubspace`: a closed subspace of a decent
  algebraic space is decent.

## References

* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A field-valued point of a presheaf represented by an object of the big fppf site over `S`
presents it by a quasi-compact morphism. -/
theorem isQuasiCompact_fieldMorphism_yoneda (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsQuasiCompact B S hS (fieldMorphism B S hS (yoneda.obj U) p) := by
  rw [fieldMorphism_yoneda]
  refine quasiCompact_schemeMap_isQuasiCompact B S hS p.siteHom ?_
  have := finite_toScheme_siteObject B S hS (yoneda.obj U) p
  rw [quasiCompact_iff_forall_isAffineOpen]
  exact fun V _ ↦ (Set.toFinite _).isCompact

/-- A presheaf represented by an object of the big fppf site over `S` is a decent algebraic
space over `S`. -/
theorem isDecentSpace_yoneda (U : BigFppfOver B S hS) :
    IsDecentSpace B S hS (yoneda.obj U) := fun x =>
  let ⟨p, hp, hmono⟩ := hasMonomorphicFieldRepresentative_yoneda B S hS U x
  ⟨p, hp, hmono, isQuasiCompact_fieldMorphism_yoneda B S hS U p⟩

/-- Decency passes from the target of a representable morphism of presheaves on the big fppf
site of `S` to its source, when the source is an algebraic space. -/
@[stacks 03KF "property_gamma, as condition (4) of Stacks 03JV"]
theorem isDecentSpace_of_relativelyRepresentable
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (hY : IsDecentSpace B S hS Y) :
    IsDecentSpace B S hS X := by
  intro x
  obtain ⟨r, hry, hrmono, hrqc⟩ := hY (pointsMap B S hS X f x)
  have hcomm : pointsMap B S hS X f x =
      pointsMap B S hS (yoneda.obj (FieldValuedPoint.siteObject B S hS Y r))
        (fieldMorphism B S hS Y r)
        ((FieldValuedPoint.tautologicalPoint B S hS Y r).class B S hS
          (yoneda.obj (FieldValuedPoint.siteObject B S hS Y r))) := by
    rw [pointsMap_fieldMorphism_tautologicalPoint, hry]
  obtain ⟨z, hz, -⟩ :=
    exists_points_of_isPullback B S hS (hf.isPullback (fieldMorphism B S hS Y r)) x _ hcomm
  have hqmono : Mono (hf.fst (fieldMorphism B S hS Y r)) :=
    (hf.isPullback (fieldMorphism B S hS Y r)).mono_fst_of_mono hrmono
  have hqqc : IsQuasiCompact B S hS (hf.fst (fieldMorphism B S hS Y r)) :=
    isQuasiCompact_of_isPullback B S hS (hf.isPullback (fieldMorphism B S hS Y r)).flip hrqc
  obtain ⟨r', hr'z, hr'mono⟩ :=
    hasMonomorphicFieldRepresentative_yoneda B S hS (hf.pullback (fieldMorphism B S hS Y r)) z
  refine ⟨FieldValuedPoint.map B S hS _ (hf.fst (fieldMorphism B S hS Y r)) r', ?_, ?_, ?_⟩
  · rwa [← pointsMap_class, hr'z]
  · rw [fieldMorphism_map]
    exact mono_comp' hr'mono hqmono
  · rw [fieldMorphism_map]
    exact isQuasiCompact_comp B S hS
      (isAlgebraicSpace_yoneda B S hS (hf.pullback (fieldMorphism B S hS Y r))) hX _ _
      (isQuasiCompact_fieldMorphism_yoneda B S hS _ r') hqqc

/-- Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over `S`. If every étale
chart of `Y` by an affine scheme and the self-intersection of that chart have finite fibres
above every point, then the same holds for `X`. -/
@[stacks 03KF "property_gamma"]
theorem hasFiniteChartAndRelationFibersAtEveryPoint_of_relativelyRepresentable
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f)
    (hYγ : HasFiniteChartAndRelationFibersAtEveryPoint B S hS Y) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).1
    (isDecentSpace_of_relativelyRepresentable B S hS hX f hf
      ((isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS Y hY).2 hYγ))

/-- A closed subspace of a decent algebraic space over `S` is decent. -/
theorem isDecentSpace_of_isClosedSubspace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hdec : IsDecentSpace B S hS X) {Z : Subfunctor X}
    (hZ : IsClosedSubspace B S hS Z) :
    IsDecentSpace B S hS Z.toFunctor :=
  isDecentSpace_of_relativelyRepresentable B S hS hZ.1 Z.ι hZ.2.rep hdec

end AlgebraicGeometry.Space

add_to_stacks 0ABT "decent"
  AlgebraicGeometry.Space.isDecentSpace_of_relativelyRepresentable

end
