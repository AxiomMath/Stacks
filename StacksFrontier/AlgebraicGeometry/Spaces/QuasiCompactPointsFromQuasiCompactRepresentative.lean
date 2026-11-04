module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection

/-!
# Condition (5) of Stacks 03JV implies condition (6)

Let `F` be an algebraic space over a scheme `S` and let `x` be a point of `|F|` which is the
class of *some* field-valued point whose presenting morphism `Spec(k) ⟶ F` is quasi-compact —
condition (5) of Stacks 03JV. This file proves condition (6): the presenting morphism of
*every* field-valued point in the class of `x` is quasi-compact. Together with
`AlgebraicGeometry.Space.EveryFieldRepresentativeIsQuasiCompact.hasQuasiCompactFieldRepresentative`
this makes conditions (5) and (6) equivalent.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_fieldValuedPoint`: a morphism of the
  site between the objects underlying two field-valued points induces a quasi-compact morphism
  of presheaves.
* `AlgebraicGeometry.Space.isSurjective_yoneda_map_of_fieldValuedPoint`: the same morphism is
  surjective on points.
* `HasQuasiCompactFieldRepresentative.everyFieldRepresentativeIsQuasiCompact`, in the
  namespace `AlgebraicGeometry.Space`: condition (5) of Stacks 03JV implies condition (6).
* `hasQuasiCompactFieldRepresentative_iff_everyFieldRepresentativeIsQuasiCompact`, in the same
  namespace: conditions (5) and (6) of Stacks 03JV are equivalent.

## Implementation notes

**The source's route is not taken, and no monomorphism is used.** Stacks 03JV reaches
condition (6) from condition (5) through the already-established equivalence of (1)–(5), so
that a representative as in condition (4) is available; Stacks 0H2X then factors an arbitrary
representative through the monomorphic one and the composite is quasi-compact by Stacks 03HG.
That is the argument of
`HasQuasiCompactMonomorphicFieldRepresentative.everyFieldRepresentativeIsQuasiCompact`, whose
hypothesis is condition (4): the monomorphism is needed there, since Stacks 0H2X uses it.

Condition (5) grants no monomorphism, so no factorization of one representative through
another is available. What *is* available is a **common extension**: by Stacks 03BU two
field-valued points define the same point of `|F|` exactly when they are dominated by a third
(`AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff`), the relevant transitivity
being the compositum construction of that tag. So for `p` as in condition (5) and an arbitrary
`q` in the class of `x` there is `r` with morphisms `f : r ⟶ p` and `g : r ⟶ q` of the site
satisfying `yoneda.map f ≫ fieldMorphism p = fieldMorphism r` and
`yoneda.map g ≫ fieldMorphism q = fieldMorphism r`, both by naturality of the Yoneda
equivalence. The first exhibits `fieldMorphism r` as a composition of quasi-compact morphisms,
hence quasi-compact by Stacks 03HG; the second runs the *other* way, and quasi-compactness is
transferred down it by Stacks 040W part (2)
(`AlgebraicGeometry.Space.IsQuasiCompact.of_isSurjective_comp`), whose hypothesis is that
`yoneda.map g` be surjective on points. It is: both objects have the spectrum of a field as
underlying scheme, so the source is nonempty and the target is a subsingleton.

So the direction of the argument is reversed relative to the source — descent along a
surjection rather than composition along a factorization — and Stacks 040W replaces Stacks
0H2X. The two facts about `yoneda.map c` used here do not depend on the point `x`: a morphism
between spectra of fields in the site is affine, hence quasi-compact, and the represented
reading passes to the reading of Stacks 03HE by Stacks 03HD, condition (1) implies
condition (2).

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms of the site between the spectra underlying field-valued points -/

/-- A morphism `c` of the big fppf site between the objects underlying two field-valued points
of a presheaf induces a quasi-compact morphism `h_{r} ⟶ h_{q}` of presheaves, in the sense of
Stacks 03HE. -/
theorem isQuasiCompact_yoneda_map_of_fieldValuedPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p q : FieldValuedPoint B S hS F)
    (c : p.siteObject ⟶ q.siteObject) :
    IsQuasiCompact B S hS (yoneda.map c) := by
  refine isQuasiCompact_of_presheaf_quasiCompact B S hS
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ c).2 ?_)
  have hpaff : IsAffine ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  have hqaff : IsAffine ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of q.carrier)))
  exact inferInstance

/-- A morphism `c` of the big fppf site between the objects underlying two field-valued points
of a presheaf induces a morphism `h_{r} ⟶ h_{q}` of presheaves which is surjective in the
sense of Stacks 03ME. -/
theorem isSurjective_yoneda_map_of_fieldValuedPoint
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p q : FieldValuedPoint B S hS F)
    (c : p.siteObject ⟶ q.siteObject) :
    IsSurjective B S hS (yoneda.map c) := by
  refine (surjective_pointsMap_yoneda_iff B S hS c).2 ?_
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of p.carrier)))
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj q.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
  exact fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

/-! ### Condition (5) implies condition (6) -/

/-- **Stacks 03JV, condition (5) implies condition (6).** If some field-valued point in the
class of a point `x` of an algebraic space `F` over `S` presents it by a quasi-compact
morphism `Spec(k) ⟶ F`, then *every* field-valued point in the class of `x` does. -/
@[stacks 03JV "part (5) implies part (6)"]
theorem HasQuasiCompactFieldRepresentative.everyFieldRepresentativeIsQuasiCompact
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F}
    (h : HasQuasiCompactFieldRepresentative B S hS F x) :
    EveryFieldRepresentativeIsQuasiCompact B S hS F x := by
  obtain ⟨p, hpx, hqc⟩ := h
  intro q hqx
  obtain ⟨r, ⟨f, hf⟩, ⟨g, hg⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS F p q).1 (hpx.trans hqx.symm)
  have hfp : yoneda.map f ≫ fieldMorphism B S hS F p = fieldMorphism B S hS F r := by
    rw [yonedaEquiv_symm_naturality_left f F p.value, hf]
  have hgq : yoneda.map g ≫ fieldMorphism B S hS F q = fieldMorphism B S hS F r := by
    rw [yonedaEquiv_symm_naturality_left g F q.value, hg]
  have hr : IsQuasiCompact B S hS (fieldMorphism B S hS F r) := by
    rw [← hfp]
    exact IsQuasiCompact.comp B S hS (isAlgebraicSpace_yoneda B S hS _) hF
      (isQuasiCompact_yoneda_map_of_fieldValuedPoint B S hS r p f) hqc
  exact IsQuasiCompact.of_isSurjective_comp B S hS
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hF hgq
    (isSurjective_yoneda_map_of_fieldValuedPoint B S hS r q g) hr

/-! ### Conditions (5) and (6) are equivalent -/

/-- **Stacks 03JV, conditions (5) and (6) are equivalent.** For a point `x` of an algebraic
space `F` over `S`, *some* field-valued point in the class of `x` has quasi-compact presenting
morphism if and only if *every* one does. -/
@[stacks 03JV "conditions (5) and (6)"]
theorem hasQuasiCompactFieldRepresentative_iff_everyFieldRepresentativeIsQuasiCompact
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {x : points B S hS F} :
    HasQuasiCompactFieldRepresentative B S hS F x ↔
      EveryFieldRepresentativeIsQuasiCompact B S hS F x :=
  ⟨fun h ↦ h.everyFieldRepresentativeIsQuasiCompact B S hS F hF,
   fun h ↦ h.hasQuasiCompactFieldRepresentative B S hS F⟩

end AlgebraicGeometry.Space

end
