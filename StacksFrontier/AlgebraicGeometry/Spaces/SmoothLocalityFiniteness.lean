module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSourceLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer

/-!
# Smooth locality of the finiteness conditions on algebraic spaces (Stacks 06FC)

**Stacks 06FC** lists the properties of morphisms of algebraic spaces to which the criterion of
**Stacks 06FB** applies. The flat case is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion` and the smooth case in
`StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer`; this module proves the two
finiteness cases, *locally of finite type* and *locally of finite presentation*.

The three fields of Stacks 06F8 that Stacks 06FB asks for are obtained exactly as in the flat and
smooth cases:

* source locality for the smooth topology of algebraic spaces is the smooth case of
  **Stacks 06ER**, `AlgebraicGeometry.Space.isLocalAtSource_smooth_of_schemes`, applied to the
  corresponding property of morphisms of schemes, which is étale local on the source and target
  by **Stacks 04R3** and local on the source for the smooth topology of schemes by the smooth
  case of **Stacks 036H** — the two instances in
  `StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSourceLocalityFiniteness`;
* target locality for the smooth topology is the restriction of the fpqc statement along
  `AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`, the smooth case of **Stacks 0DFQ**. For
  local finite presentation the fpqc statement is **Stacks 041T**; for local finite
  type it is **Stacks 041S**, obtained here from the same generic chart criterion
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isLocalAtTarget_fpqc`;
* the postcomposition hypothesis is composition of the property (**Stacks 03XG** and
  **Stacks 03XQ**) applied to the fact that a smooth morphism has it (**Stacks 06MH** and
  **Stacks 04AJ**).

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtTarget_fpqc`: being locally of finite
  type is local on the target for the fpqc topology of algebraic spaces.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtSource_smooth` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtSource_smooth`: the two
  finiteness cases of Stacks 06ER at the smooth topology.
* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType`:
  **Stacks 06FC**, the locally-of-finite-type case.
* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation`:
  **Stacks 06FC**, the locally-of-finite-presentation case.

## Implementation notes

`isLocallyOfFiniteType_isLocalAtTarget_fpqc` is the content of **Stacks 041S** for the fpqc
precoverage of algebraic spaces, the mirror of
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fpqc` (**Stacks 041T**)
one property over. Its scheme-level input is the root-level
`Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fpqc` in
`StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget` (**Stacks 02KX**), a statement about
morphisms of *schemes*.

The two source-locality declarations are registered as `instance`s, which is the form the
criterion of Stacks 06FB consumes them in, exactly as
`AlgebraicGeometry.Space.isFlat_isLocalAtSource_fpqc` and
`AlgebraicGeometry.Space.isSmooth_isLocalAtSource_smooth` are. They are *not* obtained from the
étale case of Stacks 06ER: an étale covering is a smooth covering and not conversely, so source
locality for the smooth topology is the stronger assertion and
`CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` runs the wrong way. The Stacks source
reaches them through the fppf statements (Stacks 036O and Stacks 036N); here they come from the
smooth case of Stacks 036H directly.

## References

* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 041S](https://stacks.math.columbia.edu/tag/041S)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 06FB](https://stacks.math.columbia.edu/tag/06FB)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 041S -/

/-- **Stacks 041S.** Being locally of finite type, as a property of morphisms of algebraic spaces
over `S`, is local on the target for the fpqc topology. -/
instance isLocallyOfFiniteType_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        IsLocallyOfFiniteType B S hS f.hom)
      (Topology.fpqc.precoverage.{u, v} B S hS) :=
  holdsOnEveryEtaleChart_isLocalAtTarget_fpqc B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget

/-! ### Stacks 06ER, the two finiteness cases at the smooth topology -/

/-- **Stacks 06ER**, local finite type at the smooth topology: being locally of finite type is
local on the source for the smooth topology of algebraic spaces over `S`.

One application of the smooth case of Stacks 06ER to local finite type of morphisms of schemes,
which is étale local on the source and target (Stacks 04R3) and local on the source for the
smooth topology of schemes (the smooth case of Stacks 036H). -/
instance isLocallyOfFiniteType_isLocalAtSource_smooth :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFiniteType B S hS f.hom)
      (Topology.precoverage.{u, v} .smooth B S hS) :=
  isLocalAtSource_smooth_of_schemes B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget

/-- **Stacks 06ER**, local finite presentation at the smooth topology: being locally of finite
presentation is local on the source for the smooth topology of algebraic spaces over `S`. -/
instance isLocallyOfFinitePresentation_isLocalAtSource_smooth :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFinitePresentation B S hS f.hom)
      (Topology.precoverage.{u, v} .smooth B S hS) :=
  isLocalAtSource_smooth_of_schemes B S hS
    (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget

/-! ### Stacks 06FC, the two finiteness cases -/

/-- **Stacks 06FC**, the locally-of-finite-type case. Being locally of finite type for morphisms
of algebraic spaces over `S` is smooth local on the source-and-target.

The source locality hypothesis of Stacks 06FB is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isLocalAtSource_smooth`; the target locality one
comes from the fpqc statement of Stacks 041S along
`AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`, and the postcomposition hypothesis is
composition of morphisms locally of finite type (Stacks 03XG) applied to the fact that a smooth
morphism is locally of finite type (Stacks 06MH). -/
@[stacks 06FC "locally_of_finite_type"]
theorem isSmoothLocalOnSourceAndTarget_locallyOfFiniteType :
    IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ f => IsLocallyOfFiniteType B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsLocallyOfFiniteType B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    isLocallyOfFiniteType_isLocalAtSource_smooth B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isLocallyOfFiniteType_isLocalAtTarget_fpqc B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (smooth_precoverage_le_fpqc B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    (fun hX hY hZ f g hf hg => isLocallyOfFiniteType_comp B S hS hX hY hZ f g hf
      (isLocallyOfFiniteType_of_isSmooth B S hS hg))

/-- **Stacks 06FC**, the locally-of-finite-presentation case. Being locally of finite
presentation for morphisms of algebraic spaces over `S` is smooth local on the
source-and-target.

The source locality hypothesis of Stacks 06FB is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtSource_smooth`; the target
locality one comes from the fpqc statement of Stacks 041T along
`AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`, and the postcomposition hypothesis is
composition of morphisms locally of finite presentation (Stacks 03XQ) applied to the fact that a
smooth morphism is locally of finite presentation (Stacks 04AJ). -/
@[stacks 06FC "locally_of_finite_presentation"]
theorem isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation :
    IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ f => IsLocallyOfFinitePresentation B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsLocallyOfFinitePresentation B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    isLocallyOfFinitePresentation_isLocalAtSource_smooth B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    isLocallyOfFinitePresentation_isLocalAtTarget_fpqc B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (smooth_precoverage_le_fpqc B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    (fun hX hY hZ f g hf hg => isLocallyOfFinitePresentation_comp B S hS hX hY hZ f g hf
      (isLocallyOfFinitePresentation_of_isSmooth B S hS hg))

end AlgebraicGeometry.Space

end
