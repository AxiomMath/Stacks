module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.LocalRingProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.GermPropertyAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.RingTheory.Etale.ReducedLocalization

/-!
# Properties of the local rings of an algebraic space, and reducedness

The local ring of an algebraic space at a point is only defined up to the choice of an étale
scheme chart through that point, so a property of local rings may be asked of it exactly when
the property is invariant under étale localization. This file records that predicate and
proves the first instance of it: an algebraic space is reduced if and only if all of its local
rings are reduced.

## Main definitions

* `AlgebraicGeometry.Space.HasLocalRingPropertyAtPoint`: a property of local rings, invariant
  under étale localization, holds for the local ring of an algebraic space at a point.

## Main results

* `AlgebraicGeometry.Space.isReduced_localization_etale_invariant`: reducedness of local
  rings is invariant under étale localization, in the form the predicate demands.
* `AlgebraicGeometry.Space.isReduced_iff_forall_localRing_isReduced`: an algebraic space is
  reduced — it has a reduced surjective étale scheme chart — exactly when its local ring at
  every point is reduced.

## Implementation notes

The predicate is the chart condition of Stacks 04RC specialized to a property of the stalk at
the chart point: there is an étale scheme chart and a point of it above the given point of the
space whose stalk has the property. By Stacks 04N2 the choice of chart is immaterial, which is
what the invariance hypothesis buys; the hypothesis is carried as an unused argument of the
predicate so that no consumer can state it without having checked the invariance.

Both directions of the main result go through the stalkwise criterion for reducedness of a
scheme. The one-chart condition of Stacks 03E6 is turned into reducedness of *every* étale
chart by Stacks 03E8, and reducedness of a chart is turned into reducedness of the stalks at
all of its field-valued points by `AlgebraicGeometry.Space.isReduced_iff_fieldPoints` below;
the point of a chart selected by a field-valued point is
`AlgebraicGeometry.Space.schemePoint`, and every scheme point of a chart arises that way by
`AlgebraicGeometry.Space.exists_fieldValuedPoint_schemePoint_eq`. The two chart conditions are
matched by Stacks 04N2 applied to the étale-local property of germs that
`AlgebraicGeometry.GermOfScheme.isEtaleLocal_stalk_property` builds out of reducedness of
local rings.

## References

* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
* [Stacks Project, Tag 0BGS](https://stacks.math.columbia.edu/tag/0BGS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BBL, the local ring of an algebraic space.** A property `P` of local rings which
is invariant under étale localization holds for the local ring of an algebraic space `F` at a
point `x` when it holds for the stalk of some étale scheme chart at some point above `x`. By
Stacks 04N2 the chart is immaterial, and the invariance hypothesis `_hP` is what makes that
so; it is carried as an argument of the predicate rather than assumed of `P` globally. -/
@[stacks 0BBL "local_ring_of_an_algebraic_space_has_p"]
abbrev HasLocalRingPropertyAtPoint (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (P : (R : Type u) → [CommRing R] → Prop)
    (_hP : ∀ {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C]
      (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime],
      q.comap (algebraMap A C) = p →
        (P (Localization.AtPrime p) ↔ P (Localization.AtPrime q))) : Prop :=
  ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a ∧
    ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x ∧
      P (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk (schemePoint B S hS U p))

/-- Reducedness of local rings is invariant under étale localization: this is
`isReduced_localizationAtPrime_iff_of_etale` in the shape
`AlgebraicGeometry.Space.HasLocalRingPropertyAtPoint` asks for. -/
theorem isReduced_localization_etale_invariant :
    ∀ {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C]
      (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime],
      q.comap (algebraMap A C) = p →
        (_root_.IsReduced (Localization.AtPrime p) ↔
          _root_.IsReduced (Localization.AtPrime q)) :=
  fun p _ q _ hq => isReduced_localizationAtPrime_iff_of_etale p q hq

/-- Reducedness of a scheme of the big fppf site over `S` is reducedness of its stalks at the
points selected by the field-valued points of its represented presheaf. Every point of the
scheme is such a point, by `AlgebraicGeometry.Space.exists_fieldValuedPoint_schemePoint_eq`. -/
theorem isReduced_iff_fieldPoints (U : BigFppfOver B S hS) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj U) ↔
      ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
        _root_.IsReduced (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
          (schemePoint B S hS U p)) := by
  constructor
  · intro h p
    have : IsReduced ((BigFppfOver.toScheme B S hS).obj U) := h
    exact isReduced_stalk_of_isReduced _ (schemePoint B S hS U p)
  · intro h
    refine @isReduced_of_isReduced_stalk ((BigFppfOver.toScheme B S hS).obj U) fun y => ?_
    obtain ⟨p, rfl⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS U y
    exact h p

/-- **Stacks 0BGS.** An algebraic space is reduced exactly when all of its local rings are
reduced. Reducedness of the space is the étale-local scheme property of Stacks 03E6 — a
reduced surjective étale scheme chart — and reducedness of its local ring at a point is the
chart condition of `AlgebraicGeometry.Space.HasLocalRingPropertyAtPoint`. -/
@[stacks 0BGS "reduced_iff_local_rings_reduced"]
theorem isReduced_iff_forall_localRing_isReduced (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsReduced X) ↔
      ∀ x : points B S hS F,
        HasLocalRingPropertyAtPoint B S hS F hF x
          (fun (R : Type u) => fun [CommRing R] => _root_.IsReduced R)
          isReduced_localization_etale_invariant := by
  have hQEtale : GermOfScheme.IsEtaleLocal
      (fun g : GermOfScheme.{u} => _root_.IsReduced (g.scheme.presheaf.stalk g.point)) := by
    refine GermOfScheme.isEtaleLocal_stalk_property
      (P := fun (R : Type u) => fun [CommRing R] => _root_.IsReduced R)
      isReduced_localization_etale_invariant ?_
    intro R R' _ _ _ _ e
    exact ⟨fun h => isReduced_of_injective e.symm e.symm.injective,
      fun h => isReduced_of_injective e e.injective⟩
  have hPointChart :
      (∀ x : points B S hS F,
        HasLocalRingPropertyAtPoint B S hS F hF x
          (fun (R : Type u) => fun [CommRing R] => _root_.IsReduced R)
          isReduced_localization_etale_invariant) ↔
      (∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a →
        ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
          _root_.IsReduced (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
            (schemePoint B S hS U p))) := by
    constructor
    · exact fun h U a ha p => (forall_etale_chart_iff_exists_etale_chart B S hS F hF _ _
        hQEtale).2 (h _) U a ha p rfl
    · exact fun h x => (forall_etale_chart_iff_exists_etale_chart B S hS F hF x _
        hQEtale).1 fun U a ha p _ => h U a ha p
  exact (exists_atlas_iff_forall_etale B S hS F (fun X : Scheme.{u} => IsReduced X) hF).trans
    (by simpa only [isReduced_iff_fieldPoints] using hPointChart.symm)

end AlgebraicGeometry.Space

end

