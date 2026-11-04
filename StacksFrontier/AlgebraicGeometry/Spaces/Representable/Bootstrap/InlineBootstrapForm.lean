module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion

/-!
# The inline form of the bootstrap theorem, from its condition (3)

[Stacks, Tag 04S6] condition (3),
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection`, says that a sheaf which
receives a morphism from an algebraic space that is representable by algebraic spaces, surjective,
flat and locally of finite presentation is an algebraic space. This module derives from it the
*inline* form, in which the chart is representable by objects of the site with surjective, flat,
locally finitely presented represented base changes.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap`: the
  inline form from condition (3).

## Implementation notes

Such a chart is representable by algebraic spaces by Stacks 025Z.  Its represented base changes
are morphisms of schemes, so their surjectivity, flatness and local finite presentation give the
corresponding properties of Stacks 03XZ, via
`AlgebraicGeometry.Space.hasProperty_surjectiveMorphismProperty_of_presheaf` and the étale-chart
bridge of Stacks 03MJ.

The module needs neither the proof of condition (3) nor the quotient forms of
`StacksFrontier.AlgebraicGeometry.Spaces.Bootstrap04S6Carriers`, so it sits low in the import graph:
modules below that one (Stacks 04SK among them) can import it together with the proof of
condition (3), `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04S6, condition (3), for a chart representable by objects of the site.**  A sheaf
which receives a morphism from an algebraic space that is representable by objects of the site,
with surjective, flat and locally finitely presented represented base changes, is an algebraic
space, granted condition (3).

The conclusion is the inline `h04S6` binder of Stacks 04SK, 04U0 and 04TB. -/
theorem isAlgebraicSpace_of_relativelyRepresentable_of_isBootstrap
    (hboot : IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS) :
    ∀ F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) F' →
      ∀ G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS G' →
      ∀ g : G' ⟶ F', yoneda.relativelyRepresentable g →
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
            MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g →
        IsAlgebraicSpace B S hS F' := by
  intro F' hF' G' hG' g hrel hg
  have hrep : IsRepresentableByAlgebraicSpaces B S hS g :=
    IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hrel
  have key : ∀ {P : MorphismProperty Scheme.{u}}, (∀ {X Y : Scheme.{u}} {f : X ⟶ Y},
      (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u} :
        MorphismProperty Scheme.{u}) f → P f) →
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf g :=
    fun hP => presheaf_inverseImage_mono B S hS
      (Q := @Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) (fun _ => hP) hg
  refine hboot g hF' hG' hrep
    (hasProperty_surjectiveMorphismProperty_of_presheaf B S hS g
      (key fun hk => hk.1.1) hrep) ?_ ?_
  · intro U ξ
    exact presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS (@Flat.{u})
      (fun i p (_ : Etale i) (_ : Flat p) => inferInstance) _
      (presheaf_of_isPullback B S hS (IsPullback.of_hasPullback ξ g).flip (key fun hk => hk.1.2))
  · intro U ξ
    exact presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS
      (@LocallyOfFinitePresentation.{u})
      (fun i p (_ : Etale i) (_ : LocallyOfFinitePresentation p) => inferInstance) _
      (presheaf_of_isPullback B S hS (IsPullback.of_hasPullback ξ g).flip (key fun hk => hk.2))

end AlgebraicGeometry.Space

end
