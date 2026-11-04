module

public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamilyMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChartFamilyHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover

/-!
# The glued morphism of a family of closed immersions is a closed immersion

Let `X` be an algebraic space over `S`, `F`, `G` two cartesian chart families over `X` and
`α : F ⟶ G` a morphism of them (`AlgebraicGeometry.Space.CartesianChartFamily.Hom`). Glued over
one relation of charts `pr₁, pr₂ : V' ⇉ V₂` with `V₂` surjective, the glued morphism
`F_X ⟶ G_X` (`AlgebraicGeometry.Space.CartesianChartFamily.Hom.glued`) fits in a cartesian square
with `α_{V₂}` (`AlgebraicGeometry.Space.CartesianChartFamily.Hom.isPullback_glued`). Being a
closed immersion is étale local on the target, so the glued morphism is a closed immersion when
`α_{V₂}` is one.

## Main results

* `AlgebraicGeometry.Space.CartesianChartFamily.Hom.isClosedImmersion_glued`: the glued
  morphism of a family of closed immersions is a closed immersion.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CartesianChartFamily

variable {X : AlgebraicSpaces B S hS}

namespace Hom

variable {F G : CartesianChartFamily X} (α : F.Hom G)

variable {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
  (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
    (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)

variable (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
  (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) V₂.obj.hom)
include hsurj

/-- **The glued morphism of a family of closed immersions is a closed immersion**: it is one after
the base change along the surjective étale chart `G(V₂) ⟶ G_X`, where it is `α_{V₂}`. -/
theorem isClosedImmersion_glued
    (hα : _root_.AlgebraicGeometry.IsClosedImmersion (α.app V₂)) :
    IsClosedImmersion B S hS (α.glued pr₁ pr₂ hsq).hom := by
  have hrep : IsClosedImmersion B S hS (yoneda.map (α.siteApp V₂)) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance _ hα
  have hpb := α.isPullback_glued pr₁ pr₂ hsq hsurj
  have : (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : MorphismProperty.RespectsIso (closedImmersionPresheafProperty B S hS) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsnd : IsClosedImmersion B S hS
      (pullback.snd (α.glued pr₁ pr₂ hsq).hom (G.quotientChart pr₁ pr₂ hsq)) := by
    refine ((closedImmersionPresheafProperty B S hS).cancel_left_of_respectsIso
      hpb.isoPullback.hom _).1 ?_
    rw [hpb.isoPullback_hom_snd]
    exact hrep
  exact (isAlgebraicSpace_and_isClosedImmersion_of_surjectiveEtaleChart
    (F.quotient pr₁ pr₂ hsq).property.isSheaf (G.quotient pr₁ pr₂ hsq).property
    (G.surjective_quotientChart pr₁ pr₂ hsq) (G.etale_quotientChart pr₁ pr₂ hsq) hsnd).2

end Hom

end CartesianChartFamily

end AlgebraicGeometry.Space

end
