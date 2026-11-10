module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProj.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# Universal closedness of the relative Proj of an algebraic space

In the relative Proj situation of Stacks 0849, if the degree-zero part of the graded algebra is
integral over the structure sheaf and the graded algebra is of finite type over its degree-zero
part, the structure morphism `π : Proj_X(𝒜) ⟶ X` is universally closed.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_relativeProj` is **Stacks 084H**.

## Implementation notes

As for Stacks 084E, 084F and 084G in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean`, the relative Proj enters through a
surjective étale scheme chart of the base, as a `AlgebraicGeometry.Space.RelativeProjChart`.
That structure is exactly what Stacks 084B supplies, and it is all the source's proof uses: the
proof reads the property off the one cartesian square by an étale-local-on-the-target criterion
and then quotes the case of schemes. The construction of the relative Proj of an algebraic
space, Stacks 084A–084C, is not in this library, and
`AlgebraicGeometry.Space.exists_relativeProjChart` shows the chart hypothesis is inhabited for
every situation of Stacks 01NN, so the statement is not vacuous.

The hypotheses are the scheme-level hypotheses of Stacks 07ZZ on the situation living on the
chart, which is the restriction `g^*𝒜` of the algebra on the base. That is not a weakening:
both conditions are affine-local on the base, so for a quasi-coherent graded algebra on the
base they hold exactly when they hold for the restriction to a surjective étale chart.

Universal closedness is étale local on the target — the leg used is
`AlgebraicGeometry.Space.universallyClosed_of_etale_atlas` of Stacks 03IT — so the conclusion
follows from the case of schemes,
`Stacks.RelativeProj.Situation.universallyClosed_relativeProjToBase_of_isIntegralInDegreeZero`.

## References

* [Stacks Project, Tag 084H](https://stacks.math.columbia.edu/tag/084H)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
* [Stacks Project, Tag 07ZZ](https://stacks.math.columbia.edu/tag/07ZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves of sets times out at the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_RelativeProjUniversallyClosed
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_RelativeProjUniversallyClosed
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace RelativeProjChart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X}
    {t : Stacks.RelativeProj.Situation.{u}} (d : RelativeProjChart B S hS π t)

/-- The base change of `π` along the chart of the target is universally closed as soon as the
structure morphism of the relative Proj is.

The chart of the source is a fibre product of `π` and the chart of the target, so it is
isomorphic over the chart to the canonical one; universal closedness of a represented morphism
is universal closedness of the underlying morphism of schemes, which `map_projHom_property`
transports from the relative Proj. -/
theorem universallyClosed_pullback_fst
    (hQ : _root_.AlgebraicGeometry.UniversallyClosed t.relativeProjToBase) :
    UniversallyClosed B S hS (pullback.fst d.chartHom π) := by
  have hmap : _root_.AlgebraicGeometry.UniversallyClosed
      ((BigFppfOver.toScheme B S hS).map d.projHom) :=
    d.map_projHom_property (@_root_.AlgebraicGeometry.UniversallyClosed.{u})
      MorphismProperty.IsStableUnderBaseChange.respectsIso hQ
  have hpre := presheaf_yoneda_map_of_inverseImage B S hS
    _root_.AlgebraicGeometry.universallyClosed_isStableUnderBaseChange d.projHom hmap
  have hyon : UniversallyClosed B S hS (yoneda.map d.projHom) :=
    universallyClosed_of_presheaf_universallyClosed B S hS
      (isAlgebraicSpace_yoneda B S hS d.proj) (isAlgebraicSpace_yoneda B S hS d.chart)
      hpre.1 hpre
  have hc := universallyClosed_comp B S hS
    (isAlgebraicSpace_yoneda B S hS d.proj) (isAlgebraicSpace_yoneda B S hS d.chart)
    d.isPullback.flip.isoPullback.inv (yoneda.map d.projHom)
    (universallyClosed_of_isIso B S hS d.isPullback.flip.isoPullback.inv) hyon
  rwa [d.isPullback.flip.isoPullback_inv_fst] at hc

end RelativeProjChart

section Main

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 084H.** In the relative Proj situation of Stacks 0849, if the structure sheaf maps
integrally into `𝒜₀` and `𝒜` is of finite type as an `𝒜₀`-algebra, then the structure morphism
`π : Proj_X(𝒜) ⟶ X` is universally closed.

The relative Proj enters through a surjective étale scheme chart of `X`, as Stacks 084B
presents it, and the two hypotheses are the hypotheses of Stacks 07ZZ on the restricted algebra
living on that chart. Universal closedness is étale local on the target — the leg used is
`AlgebraicGeometry.Space.universallyClosed_of_etale_atlas` of Stacks 03IT — so the conclusion
follows from the case of schemes, which is
`Stacks.RelativeProj.Situation.universallyClosed_relativeProjToBase_of_isIntegralInDegreeZero`. -/
@[stacks 084H]
theorem universallyClosed_relativeProj {X P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (π : P ⟶ X)
    {t : Stacks.RelativeProj.Situation.{u}} (d : RelativeProjChart B S hS π t)
    (hint : t.IsIntegralInDegreeZero) (hft : t.IsFiniteTypeOverDegreeZero) :
    UniversallyClosed B S hS π :=
  universallyClosed_of_etale_atlas B S hS hX π d.chart d.chartHom
    (isSurjective_of_presheafSurjective B S hS d.chartHom d.chartHom_surjective)
    ((isEtale_iff_presheaf_of_yoneda B S hS d.chartHom).2 d.chartHom_etale)
    (d.universallyClosed_pullback_fst
      (Stacks.RelativeProj.Situation.universallyClosed_relativeProjToBase_of_isIntegralInDegreeZero
        t hint hft))

end Main

end AlgebraicGeometry.Space

end
