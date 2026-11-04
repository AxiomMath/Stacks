module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Etale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# Properties preserved by a cartesian finite-order deformation of algebraic spaces

In a cartesian finite-order deformation of algebraic spaces the morphism `f` of special fibres
and its ambient deformation `f'` share every property on the list of Stacks 0CG6 which is
étale local on the source and target, because
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation` turns
each such case into the corresponding case for morphisms of schemes, which is Stacks 06AG.

Eight such cases are proved here: local finite type, local quasi-finiteness, local finite
presentation, flatness, syntomicity, smoothness, unramifiedness and étaleness. Each is an
instance of the same two inputs — the property is étale local on the source and target
(Stacks 04R3) and it is invariant under every cartesian finite-order deformation of schemes
(Stacks 06AG) — so the proofs are one line each.

Surjectivity is on the list of 0CG6 as well, but it is not étale local on the source: it is a
condition on the map of point sets, and both thickenings are bijections there. It therefore holds
for an arbitrary morphism of thickenings, which is the surjectivity clause of Stacks 09ZY, and is
recorded here by instantiating that clause at the morphism of thickenings underlying the
deformation.

## Main results

* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isFlat_iff`: **Stacks 0CG6**,
  part 0CG8.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isSurjective_iff`: **Stacks 0CG6**,
  part 0CGF.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isLocallyOfFiniteType_iff`:
  **Stacks 0CG6**, part 0CGI.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isLocallyQuasiFinite_iff`:
  **Stacks 0CG6**, part 0CGJ.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isLocallyOfFinitePresentation_iff`:
  **Stacks 0CG6**, part 0CGK.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isSyntomic_iff`: **Stacks 0CG6**,
  part 0CGN.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isSmooth_iff`: **Stacks 0CG6**,
  part 0CGP.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isUnramified_iff`: **Stacks 0CG6**,
  part 0CGQ.
* `AlgebraicGeometry.Space.CartesianFiniteOrderDeformation.isEtale_iff`: **Stacks 0CG6**,
  part 0CGR.

## Implementation notes

Following Stacks 03XJ, local quasi-finiteness of a morphism of algebraic spaces is the chart
condition for the conjunction of Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, which is exactly the shape in which the scheme-level
statement `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.locallyQuasiFinite_iff`
is available.

Seven of the eight chart conditions are the definitions of the corresponding property of
morphisms of algebraic spaces. Étaleness is instead Tag 03FR, the condition that composing with
an étale morphism from a representable presheaf stays étale; it agrees with the chart condition
by Tag 03XT, `AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`, which is what the
étale statement below inserts on both sides.

## References

* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

namespace CartesianFiniteOrderDeformation

variable {T : BigFppfSite.{u}} {S : Scheme.{u}} {hS : T.Contains S}
    (D : CartesianFiniteOrderDeformation T S hS)

/-- **Stacks 0CG6, part 0CG8.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is flat if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CG8: flat"]
theorem isFlat_iff : IsFlat T S hS D.f ↔ IsFlat T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    Flat.isEtaleLocalOnSourceAndTarget fun E ↦ E.flat_iff

/-- **Stacks 0CG6, part 0CGF.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is surjective if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGF: surjective"]
theorem isSurjective_iff : IsSurjective T S hS D.f ↔ IsSurjective T S hS D.f' :=
  isSurjective_iff_isSurjective_of_isThickening T S hS D.source_thickening D.target_thickening
    (Arrow.homMk D.f D.f' D.comm_f)

/-- **Stacks 0CG6, part 0CGI.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is locally of finite type if and only if its ambient deformation
is. -/
@[stacks 0CG6 "0CGI: locally of finite type"]
theorem isLocallyOfFiniteType_iff :
    IsLocallyOfFiniteType T S hS D.f ↔ IsLocallyOfFiniteType T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    fun E ↦ E.locallyOfFiniteType_iff

/-- **Stacks 0CG6, part 0CGJ.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is locally quasi-finite if and only if its ambient deformation
is. -/
@[stacks 0CG6 "0CGJ: locally quasi-finite"]
theorem isLocallyQuasiFinite_iff :
    IsLocallyQuasiFinite T S hS D.f ↔ IsLocallyQuasiFinite T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    fun E ↦ E.locallyQuasiFinite_iff

/-- **Stacks 0CG6, part 0CGK.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is locally of finite presentation if and only if its ambient
deformation is. -/
@[stacks 0CG6 "0CGK: locally of finite presentation"]
theorem isLocallyOfFinitePresentation_iff :
    IsLocallyOfFinitePresentation T S hS D.f ↔ IsLocallyOfFinitePresentation T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
    fun E ↦ E.locallyOfFinitePresentation_iff

/-- **Stacks 0CG6, part 0CGN.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is syntomic if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGN: syntomic"]
theorem isSyntomic_iff : IsSyntomic T S hS D.f ↔ IsSyntomic T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    syntomic_isEtaleLocalOnSourceAndTarget fun E ↦ E.syntomic_iff

/-- **Stacks 0CG6, part 0CGP.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is smooth if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGP: smooth"]
theorem isSmooth_iff : IsSmooth T S hS D.f ↔ IsSmooth T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    Smooth.isEtaleLocalOnSourceAndTarget fun E ↦ E.smooth_iff

/-- **Stacks 0CG6, part 0CGQ.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is unramified if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGQ: unramified"]
theorem isUnramified_iff : IsUnramified T S hS D.f ↔ IsUnramified T S hS D.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
    unramified_isEtaleLocalOnSourceAndTarget fun E ↦ E.unramified_iff

/-- **Stacks 0CG6, part 0CGR.** In a cartesian finite-order deformation of algebraic spaces the
morphism of special fibres is étale if and only if its ambient deformation is. -/
@[stacks 0CG6 "0CGR: étale"]
theorem isEtale_iff : IsEtale T S hS D.f ↔ IsEtale T S hS D.f' :=
  (isEtale_iff_holdsOnEveryEtaleChart T S hS D.source_thickening.1.1 D.target_thickening.1.1
      D.f).trans
    ((holdsOnEveryEtaleChart_iff_of_cartesianFiniteOrderDeformation T S hS D _
        etale_isEtaleLocalOnSourceAndTarget fun E ↦ E.etale_iff).trans
      (isEtale_iff_holdsOnEveryEtaleChart T S hS D.X'.property D.Y'.property D.f').symm)

end CartesianFiniteOrderDeformation

end AlgebraicGeometry.Space

end
