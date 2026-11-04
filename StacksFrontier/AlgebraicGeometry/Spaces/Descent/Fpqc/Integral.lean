module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integrality of morphisms of algebraic spaces is fpqc local on the base

**Stacks 0425**: the property "`f` is integral" of a morphism of algebraic spaces over a scheme
`S` is local on the base for the fpqc topology of Stacks 03YH. An integral morphism is the same
thing as an affine universally closed one (**Stacks 0415**), so the assertion is the conjunction
of **Stacks 041O**, universal closedness is fpqc local on the base, and **Stacks 041Z**,
affineness is fpqc local on the base; locality on the base passes to an infimum of morphism
properties, and this file carries out that composition.

## Main definitions

* `AlgebraicGeometry.Space.integralMorphismProperty`: integrality of a morphism (Stacks 03ZP)
  as a `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`, the spelling at
  which locality on the base is stated.

## Main results

* `AlgebraicGeometry.Space.integralMorphismProperty_isLocalAtTarget_fpqc`: **Stacks 0425** —
  integrality of morphisms of algebraic spaces over `S` is local on the base for the fpqc
  topology.
* `AlgebraicGeometry.Space.integralMorphismProperty_isStableUnderBaseChange`: Stacks 03ZS at
  the packaged spelling, which is the base-change half of locality on the base (Stacks 03YH).
* `AlgebraicGeometry.Space.integralMorphismProperty_eq_inf`: Stacks 0415 at the packaged
  spelling — integrality *is* affineness together with universal closedness, as morphism
  properties.

## Implementation notes

The statements `…_of_isAffineHom`, `…_of_affineDescent` and `…_of_isSheaf_fpqc` record the same
composition with affineness descent left as a hypothesis, in the three forms in which it enters
this development: Stacks 041Z itself, the effective descent property
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` to which
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc` reduces it, and Gabber's Stacks 0APL
that an algebraic space is a sheaf for the fpqc topology. Stacks 0425 is the first of them
instantiated at `AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc`.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 041O](https://stacks.math.columbia.edu/tag/041O)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0425](https://stacks.math.columbia.edu/tag/0425)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Integrality as a morphism property -/

/-- Integrality of a morphism (Stacks 03ZP) as a property of morphisms in the category of
algebraic spaces over `S`. This is the spelling at which locality on the base, Stacks 03YH, is
stated. -/
abbrev integralMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ IsIntegralHom B S hS f.hom

/-- **Stacks 03ZS at the packaged spelling**: integrality, as a morphism property of algebraic
spaces over `S`, is stable under base change.

This is the direct implication of the definition of locality on the base, Stacks 03YH: it
supplies the `pullbackSnd` field of `CategoryTheory.MorphismProperty.IsLocalAtTarget` for every
precoverage at once, and it is unconditional. The descent implication is the content of the
statements below. -/
instance integralMorphismProperty_isStableUnderBaseChange :
    (integralMorphismProperty B S hS).IsStableUnderBaseChange where
  of_isPullback sq hg :=
    isIntegralHom_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom _ _ _ sq) hg

/-- **Stacks 0415 at the packaged spelling**: integrality of morphisms of algebraic spaces over
`S` is the infimum of affineness (Stacks 03WF) and universal closedness (Stacks 03HI, part (2))
as morphism properties. -/
theorem integralMorphismProperty_eq_inf :
    integralMorphismProperty B S hS =
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsAffineHom B S hS f.hom) ⊓
        universallyClosedProperty B S hS := by
  funext X Y f
  exact propext (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS
    X.property Y.property f.hom)

/-! ### The conclusion of Stacks 0425, from affineness descent -/

/-- **The conclusion of Stacks 0425 from Stacks 041Z**, which is the source's proof. If
affineness of morphisms of algebraic spaces over `S` is local on the base for the fpqc topology
of Stacks 03YH, then so is integrality.

An integral morphism is an affine universally closed one (Stacks 0415), universal closedness is
fpqc local on the base (Stacks 041O), and locality on the base passes to an infimum of morphism
properties. -/
theorem integralMorphismProperty_isLocalAtTarget_fpqc_of_isAffineHom
    (haffine : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsAffineHom B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS)) :
    (integralMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have := haffine
  rw [integralMorphismProperty_eq_inf]
  exact MorphismProperty.IsLocalAtTarget.inf
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsAffineHom B S hS f.hom)
    (universallyClosedProperty B S hS)

/-- **The conclusion of Stacks 0425 from effective descent for affine morphisms along an fpqc
covering.** Integrality of morphisms of algebraic spaces over `S` is local on the base for the
fpqc topology of Stacks 03YH, granting
`AlgebraicGeometry.Space.IsEffectiveAffineDescentAlongFpqc` — the named hypothesis to which
`AlgebraicGeometry.Space.isAffineHom_isLocalAtTarget_fpqc` reduces Stacks 041Z. -/
theorem integralMorphismProperty_isLocalAtTarget_fpqc_of_affineDescent
    (hdesc : IsEffectiveAffineDescentAlongFpqc B S hS) :
    (integralMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  integralMorphismProperty_isLocalAtTarget_fpqc_of_isAffineHom B S hS
    (isAffineHom_isLocalAtTarget_fpqc B S hS hdesc)

/-- **The conclusion of Stacks 0425 from Stacks 0APL alone.** If every algebraic space over `S`
is a sheaf for the fpqc topology of the big fppf site of `S` — Gabber's Stacks 0APL — then
integrality of morphisms of algebraic spaces over `S` is local on the base for the fpqc topology
of Stacks 03YH.

Stacks 0APL supplies effective descent for affine morphisms along an fpqc covering, by
`AlgebraicGeometry.Space.isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc`, and hence Stacks
041Z; the rest is the reduction of
`AlgebraicGeometry.Space.integralMorphismProperty_isLocalAtTarget_fpqc_of_isAffineHom`. This is
the weakest hypothesis under which this development reaches the tag. -/
theorem integralMorphismProperty_isLocalAtTarget_fpqc_of_isSheaf_fpqc
    (hAPL : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      Presheaf.IsSheaf
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck F) :
    (integralMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  integralMorphismProperty_isLocalAtTarget_fpqc_of_affineDescent B S hS
    (isEffectiveAffineDescentAlongFpqc_of_isSheaf_fpqc B S hS hAPL)

/-! ### Stacks 0425 -/

/-- **Stacks 0425.** Integrality of morphisms of algebraic spaces over `S` is local on the base
for the fpqc topology of Stacks 03YH.

An integral morphism is an affine universally closed one (Stacks 0415), affineness is fpqc local
on the base (Stacks 041Z) and so is universal closedness (Stacks 041O), and locality on the base
passes to an infimum of morphism properties. -/
@[stacks 0425, sga "4 IV 8.5.5" "more general"]
instance integralMorphismProperty_isLocalAtTarget_fpqc :
    (integralMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  integralMorphismProperty_isLocalAtTarget_fpqc_of_isAffineHom B S hS
    (isLocalAtTarget_isAffineHom_fpqc.{u, v} B S hS)

end AlgebraicGeometry.Space

end
