module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSlicingSequenceFromIsUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartFibreRegularity
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# The projection of the fibre over an unramified field-valued point is unramified

The chart construction of **Stacks 06N3** forms the cartesian diagram `F = U ×_𝒳 Spec k` over a
field-valued point `g : Spec k ⟶ 𝒳` which is **unramified in the relative sense of Properties of
Stacks, Section 04XB** — that is what
`AlgebraicGeometry.Stack.exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint`
delivers at a finite type point of a DM algebraic stack. What the slicing sequence of that
construction consumes is instead `AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**,
part (1)) of the *morphism of algebraic spaces* `p : F ⟶ U`, read through an algebraic space
`Fsp` representing the 2-fibre product.

This file performs that reading. The two statements are about the same morphism but presented
through different 2-fibre products: the relative condition of Stacks 03YK quantifies over the
algebraic spaces representing the base change of `g` along an arbitrary scheme-valued point of
`𝒳`, whereas `Fsp` represents the 2-fibre product
`AlgebraicGeometry.Stack.fibreOverFieldPoint` taken in the 2-category of algebraic stacks over
`S`. Matching them is **Stacks 045C** followed by the bridge of **Stacks 04XB** for a represented
source and target.

## Main results

* `AlgebraicGeometry.Stack.isUnramified_fibreSpaceProjection_of_relativeProperty`: the projection
  `p : F ⟶ U` of the cartesian diagram is an unramified morphism of algebraic spaces as soon as
  the field-valued point is unramified in the relative sense.
* `AlgebraicGeometry.Stack.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_fibre`: the
  slicing sequence of the chart construction of **Stacks 06N3** in the étale local ring
  `𝒪_{F, z̄}`, off the stack-level hypotheses — a smooth chart and a relatively unramified
  field-valued point.

## How it is proved

**Stacks 045C** for a 2-fibre product square of algebraic stacks,
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange_algebraicStacks`, carries the relative
condition from `g` to the first projection of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks B S hS f g`, which *is*
`AlgebraicGeometry.Stack.fibreProjection`. The projection is representable by algebraic spaces
because the field-valued point is
(`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_baseChange`), so the bridge
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` applies to it with the
representing algebraic spaces `Fsp` and `U` and reads the relative condition as the property of
the induced morphism `Fsp ⟶ U`, which is
`AlgebraicGeometry.Stack.fibreSpaceProjection` on the nose. The property is
`AlgebraicGeometry.Space.unramifiedMorphismProperty`, whose two standing hypotheses are
`AlgebraicGeometry.Space.isUnramified_isStableUnderBaseChange` and **Stacks 03ZK** restricted
from the fpqc to the fppf precoverage.

The slicing sequence then follows from
`AlgebraicGeometry.Space.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_isUnramified`
together with the regularity of `Fsp`,
`AlgebraicGeometry.Stack.hasEtaleLocalProperty_isRegular_fibreSpace` (**Stacks 06M1** at the
structure morphism `F ⟶ Spec k`, smooth by **Stacks 075W**).

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 03ZK](https://stacks.math.columbia.edu/tag/03ZK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)

variable (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

include hU hFsp in
/-- **The projection of the fibre over an unramified field-valued point is unramified.** Let
`f : U ⟶ 𝒳` be a 1-morphism from an algebraic space, let `g : Spec k ⟶ 𝒳` be a field-valued point
which is unramified in the relative sense of Properties of Stacks, Section **04XB**, and let
`Fsp` represent the 2-fibre product `F = U ×_𝒳 Spec k`. Then the induced morphism of algebraic
spaces `p : Fsp ⟶ U` is unramified in the sense of **Stacks 03ZH**, part (1). -/
theorem isUnramified_fibreSpaceProjection_of_relativeProperty
    (hgunr : RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) g.hom) :
    Space.IsUnramified B S hS
      (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) := by
  have : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  have : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.isUnramified_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  -- the field-valued point is representable by algebraic spaces, `𝒳` being an algebraic stack
  have hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
        (fieldPointObject B S hS k hk toBase)) g.hom
  have hD : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS f g) :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g
  -- the projection `F ⟶ U` is representable, being a base change of the field-valued point
  have hfst : IsRepresentableByAlgebraicSpaces B S hS
      (fibreProjection B S hS 𝒳 U hU k hk toBase f g).hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ g.hom f.hom
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f g))
      (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _ hD) hg
  -- Stacks 045C: the relative condition passes to the projection
  have hpr : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.unramifiedMorphismProperty B S hS)
      (fibreProjection B S hS 𝒳 U hU k hk toBase f g).hom hfst :=
    hasRelativeProperty_baseChange_algebraicStacks B S hS
      (Space.unramifiedMorphismProperty B S hS) g f
      (twoFibreProductSquareAlgebraicStacks B S hS f g) hD hg hfst hgunr
  -- the bridge of Stacks 04XB at the representing algebraic spaces `Fsp` and `U`
  exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.unramifiedMorphismProperty B S hS)
    (fibreProjection B S hS 𝒳 U hU k hk toBase f g).hom hfst Fsp U hFsp hU eF
    (StacksRepresentableCFG.EquivalenceOver.refl _)).1 hpr

include hU hFsp in
/-- **The slicing sequence of the chart construction of Stacks 06N3, off the stack-level
hypotheses.** Let `f : U ⟶ 𝒳` be a **smooth** 1-morphism from an algebraic space, let
`g : Spec k ⟶ 𝒳` be a field-valued point unramified in the relative sense of **Stacks 04XB**,
let `Fsp` represent `F = U ×_𝒳 Spec k`, let `z` be a geometric point of `F` and let a small étale
neighbourhood `N` of `z` map to an étale chart `Uch` of `U` over the projection. Then there are
`d = (𝔪_v).spanFinrank` elements of the maximal ideal of `𝒪_{U, u}` whose images in the étale
local ring `𝒪_{F, z̄}` form a regular sequence **generating** the maximal ideal of `𝒪_{F, z̄}`.

This is the source's *"choose `f₁, …, f_d ∈ 𝒪_{U, u}` whose images give a basis of
`𝔪_v / 𝔪_v²`"*, read where **Stacks 06MD** reads its hypothesis, with both of its space-level
inputs discharged from the data the construction has at a finite type point: unramifiedness of
the projection is
`AlgebraicGeometry.Stack.isUnramified_fibreSpaceProjection_of_relativeProperty` and regularity of
`F` is `AlgebraicGeometry.Stack.hasEtaleLocalProperty_isRegular_fibreSpace`, **Stacks 06M1** at
the structure morphism `F ⟶ Spec k`, which is smooth by **Stacks 075W**. -/
theorem exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_fibre
    (hfsm : AlgebraicStacks.IsSmooth B S hS f)
    (hgunr : RelativeProperty B S hS (Space.unramifiedMorphismProperty B S hS) g.hom)
    {z : Space.GeometricPoint B S hS Fsp} (N : Space.SmallEtaleNeighborhood z)
    (Uch : Space.SmallEtale B S hS U) (gNU : N.chart.obj.left ⟶ Uch.obj.left)
    (hsq : N.chart.obj.hom ≫ fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF =
      yoneda.map gNU ≫ Uch.obj.hom) :
    letI : IsLocalRing (Space.etaleLocalRing B S hS Fsp z) :=
      Space.isLocalRing_etaleLocalRing B S hS Fsp hFsp z
    ∃ t : Fin (maximalIdeal (Space.chartLocalRing B S hS Fsp N)).spanFinrank →
        Space.chartLocalRing B S hS U (Space.targetNeighborhood B S hS N Uch gNU hsq),
      (∀ i, t i ∈ maximalIdeal
        (Space.chartLocalRing B S hS U (Space.targetNeighborhood B S hS N Uch gNU hsq))) ∧
        RingTheory.Sequence.IsRegular (Space.etaleLocalRing B S hS Fsp z)
            (List.ofFn fun i => Space.etaleLocalRingMap hFsp
              (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z
              (Space.chartLocalRingToEtaleLocalRing B S hS U hU
                (Space.targetNeighborhood B S hS N Uch gNU hsq) (t i))) ∧
          Ideal.ofList (List.ofFn fun i => Space.etaleLocalRingMap hFsp
              (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z
              (Space.chartLocalRingToEtaleLocalRing B S hS U hU
                (Space.targetNeighborhood B S hS N Uch gNU hsq) (t i))) =
            maximalIdeal (Space.etaleLocalRing B S hS Fsp z) :=
  Space.exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_isUnramified B S hS
    (Xs := ⟨U, hU⟩) (Fs := ⟨Fsp, hFsp⟩)
    (ObjectProperty.homMk (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF))
    (isUnramified_fibreSpaceProjection_of_relativeProperty B S hS 𝒳 U hU k hk toBase f g
      Fsp hFsp eF hgunr)
    (hasEtaleLocalProperty_isRegular_fibreSpace B S hS 𝒳 U hU k hk toBase f g Fsp hFsp eF hfsm)
    N Uch gNU hsq

end AlgebraicGeometry.Stack

end
