module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Limits.DescendingMorphismPropertiesSiteConvention

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# DescendingMorphismProperties under the site convention

The declarations below accompany
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties`: they state its
results under the chapter's standing convention of Section 70.2 (tag 07SD) on the size of the
site, in the form the absolute Noetherian approximation of Stacks 07SU consumes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe w v u

namespace CategoryTheory

variable {A : Type*} [Category* A]

variable [HasPullbacks A]

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Flatness of a pulled back module over the second factor of a fibre product -/

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Chart squares of a base change -/

section BaseChangeSquares

variable {A : Type*} [Category* A] [HasPullbacks A]

end BaseChangeSquares

/-! ### Relative étaleness and surjectivity of charts -/

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-! ### Transferring a chart-local property to the morphism of charts -/

section Transfer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end Transfer

/-! ### Transferring surjectivity to the morphism of charts -/

section SurjectiveTransfer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end SurjectiveTransfer

/-! ### The descent results for the situation of Stacks 084W

The results above, stated for `AlgebraicGeometry.Space.MorphismDescentSituation`, which imposes
no condition on the size of the index. What the proofs need is that the limits of the affine
charts of the system are formed inside the site, which is the chapter's convention of Section
70.2 (tag 07SD), the explicit hypothesis
`hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D.base`. Each result is
also stated under `hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`, which implies the
convention by `AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`. -/

section SituationChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

namespace BridgedSituationChartSquare

end BridgedSituationChartSquare

/-! ### Descending a property of the morphism along the limit -/

/-! ### Reading flatness of a pulled back module on the chart square -/

namespace MorphismDescentSituation

add_to_stacks 08K0 "flatness of a module, under the convention of Section 70.2 (tag 07SD) and \
  with no condition on the index"
  C1573.exists_isFlatOver_mapAt_of_siteContainsBaseChangeLimits

/-! ### The covariant indexing of Stacks 07SK

Stacks 084W, and every statement above, indexes the system by a directed preorder `I` and carries
it as the *contravariant* diagram `base : Iᵒᵖ ⥤ …`, reading a stage beyond the distinguished one
as an inequality `0 ≤ i`. The library's Stacks 07SK —
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` and its fullness and faithfulness
companions — instead consumes a *cofiltered category* together with a *covariant* diagram out of
it, and states its conclusions over a morphism `j ⟶ i` of that category.

These are two readings of one and the same system: `base` is already a covariant functor on the
category `Iᵒᵖ`, which is cofiltered because a directed preorder is filtered. The declarations
below record that, and restate Stacks 0CN2 over a morphism of `Iᵒᵖ` rather than over an
inequality in `I`, so that it composes with Stacks 07SK without either result being reindexed.
-/

end MorphismDescentSituation

end SituationChartData

/-! ### The affine chart square of a morphism descent system -/

section ChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

namespace ChartSquare

end ChartSquare

/-! ### Descending a property of the morphism along the limit -/

/-! ### Reading flatness of a pulled back module on the chart square -/

namespace MorphismDescentSystem

/-! ### The covariant indexing of Stacks 07SK

Stacks 084W, and every statement above, indexes the system by a directed preorder `I` and carries
it as the *contravariant* diagram `base : Iᵒᵖ ⥤ …`, reading a stage beyond the distinguished one
as an inequality `0 ≤ i`. The library's Stacks 07SK —
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` and its fullness and faithfulness
companions — instead consumes a *cofiltered category* together with a *covariant* diagram out of
it, and states its conclusions over a morphism `j ⟶ i` of that category.

These are two readings of one and the same system: `base` is already a covariant functor on the
category `Iᵒᵖ`, which is cofiltered because a directed preorder is filtered. The declarations
below record that, and restate Stacks 0CN2 over a morphism of `Iᵒᵖ` rather than over an
inequality in `I`, so that it composes with Stacks 07SK without either result being reindexed.
-/

end MorphismDescentSystem

end ChartData

end AlgebraicGeometry.Space

end
