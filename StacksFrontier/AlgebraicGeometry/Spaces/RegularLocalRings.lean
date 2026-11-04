module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.LocalRingProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.GermPropertyAtPoint
public import StacksFrontier.RingTheory.Etale.PermanenceOfProperties

/-!
# Regularity of an algebraic space at a point

An algebraic space is *regular at a point* when every étale scheme chart has a regular local ring
at every one of its points above that point; equivalently, when some chart does at some point
above it. A point of a chart `U` is recorded as a field-valued point of `yoneda.obj U`, whose
scheme point is `AlgebraicGeometry.Space.schemePoint`, and it lies above a point of the space
when its class maps to that point under `AlgebraicGeometry.Space.pointsMap`.

## Main definitions

* `AlgebraicGeometry.Space.IsRegularAt` is regularity of an algebraic space at a point of it.

## Main results

* `AlgebraicGeometry.isEtaleLocal_isRegularLocalRing_stalk`: regularity of the local ring at
  the marked point is an étale-local property of germs of schemes.
* `AlgebraicGeometry.Space.isRegularAt_iff_exists_etale_chart`: an algebraic space is regular at
  a point if and only if some étale scheme chart has a regular local ring at some point above it.

## References

* [Stacks Project, Tag 0AH9](https://stacks.math.columbia.edu/tag/0AH9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Regularity of local rings is invariant under étale localization: along an étale ring map a
prime of the source and a prime above it have simultaneously regular localizations. -/
theorem isRegularLocalRing_localization_etale_invariant :
    ∀ {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C]
      (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime],
      q.comap (algebraMap A C) = p →
        (IsRegularLocalRing (Localization.AtPrime p) ↔
          IsRegularLocalRing (Localization.AtPrime q)) := by
  intro A C _ _ _ _ p _ q _ hpq
  have : q.LiesOver p := ⟨hpq.symm⟩
  exact isRegularLocalRing_localization_iff_of_etale p q

/-- Regularity of the local ring at the marked point is an étale-local property of germs of
schemes: an étale morphism of germs has a regular local ring at its source exactly when it has
one at its target. -/
theorem isEtaleLocal_isRegularLocalRing_stalk :
    GermOfScheme.IsEtaleLocal
      (fun g : GermOfScheme.{u} ↦ IsRegularLocalRing (g.scheme.presheaf.stalk g.point)) := by
  refine GermOfScheme.isEtaleLocal_stalk_property
    (P := fun (R : Type u) ↦ fun [CommRing R] ↦ IsRegularLocalRing R)
    isRegularLocalRing_localization_etale_invariant ?_
  intro R R' _ _ _ _ e
  exact ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space is *regular at a point* when every étale scheme chart has a regular local
ring at every point of it above that point. -/
@[stacks 0AH9]
abbrev IsRegularAt (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (x : points B S hS F) : Prop :=
  ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a →
    ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
      pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x →
      IsRegularLocalRing
        (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk (schemePoint B S hS U p))

/-- An algebraic space is regular at a point if and only if some étale scheme chart has a regular
local ring at some point of it above that point. -/
@[stacks 0AH9 "some étale chart characterization"]
theorem isRegularAt_iff_exists_etale_chart (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    IsRegularAt B S hS F x ↔
      ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a ∧
        ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
          pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x ∧
          IsRegularLocalRing
            (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk (schemePoint B S hS U p)) :=
  forall_etale_chart_iff_exists_etale_chart B S hS F hF x _
    isEtaleLocal_isRegularLocalRing_stalk

end Space

end AlgebraicGeometry

end
