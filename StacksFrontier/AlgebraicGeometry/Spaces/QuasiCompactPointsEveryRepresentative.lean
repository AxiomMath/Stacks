module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions

/-!
# Condition (4) of Stacks 03JV implies condition (6)

Let `F` be an algebraic space over a scheme `S` and let `x` be a point of `|F|` which is the
class of a field-valued point whose presenting morphism `Spec(k) ⟶ F` is a quasi-compact
monomorphism — condition (4) of Stacks 03JV. Then condition (6) holds: *every* field-valued
point in the class of `x` presents it by a quasi-compact morphism.

## Main results

* `HasQuasiCompactMonomorphicFieldRepresentative.everyFieldRepresentativeIsQuasiCompact`, in
  the namespace `AlgebraicGeometry.Space`: condition (4) implies condition (6).

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- If a point `x` of an algebraic space `F` over `S` is the class of a field-valued point whose
presenting morphism `Spec(k) ⟶ F` is a quasi-compact monomorphism, then the presenting morphism
of *every* field-valued point in the class of `x` is quasi-compact. -/
@[stacks 03JV "part (4) implies part (6)"]
theorem HasQuasiCompactMonomorphicFieldRepresentative.everyFieldRepresentativeIsQuasiCompact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    EveryFieldRepresentativeIsQuasiCompact B S hS F x := by
  obtain ⟨p, hpx, hmono, hqc⟩ := h
  have : Mono (fieldMorphism B S hS F p) := hmono
  intro q hqx
  obtain ⟨c, hc, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
    B S hS F hF p q (hpx.trans hqx.symm)
  have hfac : yoneda.map c ≫ fieldMorphism B S hS F p = fieldMorphism B S hS F q := by
    rw [yonedaEquiv_symm_naturality_left c F p.value, hc]
  rw [← hfac]
  refine IsQuasiCompact.comp B S hS (isAlgebraicSpace_yoneda B S hS _) hF ?_ hqc
  refine isQuasiCompact_of_presheaf_quasiCompact B S hS
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ c).2 ?_)
  have affine (r : FieldValuedPoint B S hS F) :
      IsAffine ((BigFppfOver.toScheme B S hS).obj r.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of r.carrier)))
  have := affine p
  have := affine q
  exact inferInstance

end AlgebraicGeometry.Space

end
