module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianChartFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleChart

/-!
# The projective bundle of a finite locally free module on an algebraic space

Let `X` be an algebraic space over a scheme `S` and `ℰ` a finite locally free `𝒪_X`-module on
the small étale site of `X`.  Its *projective bundle* is the relative homogeneous spectrum

`π : 𝐏(ℰ) = Proj_X(Sym^*(ℰ)) ⟶ X`

of the symmetric algebra of `ℰ` (Stacks 084C, applied to the graded algebra of Stacks 01OB).
It is glued from the case of schemes: over an étale scheme chart `V` of `X` it is the projective
bundle `𝐏(ℰ|_V) ⟶ V` of the restriction of `ℰ` to the chart, and these form a cartesian family
over the charts (`AlgebraicGeometry.Space.chartBundleMap_comp`).  So `𝐏(ℰ)` is the glued space of
`AlgebraicGeometry.Space.CartesianChartFamily` at the relation of charts of a presentation of
`X`, and over the presenting chart `U` it is `𝐏(ℰ|_U) = 𝐏(ℰ) ×_X U`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleChartFamily`: the cartesian family `V ↦ 𝐏(ℰ|_V)`.
* `AlgebraicGeometry.Space.projectiveBundlePresentation`: the presentation of `X` the bundle is
  glued over, with its presenting chart and relation chart.
* `AlgebraicGeometry.Space.projectiveBundle`: **the projective bundle `𝐏(ℰ)`**, an algebraic
  space over `S`.
* `AlgebraicGeometry.Space.projectiveBundleProj`: **its projection `π : 𝐏(ℰ) ⟶ X`.**

## Main results

* `AlgebraicGeometry.Space.isProper_chartBundleToChart`: over a chart the projection of the
  chart bundle is proper.
* `AlgebraicGeometry.Space.isPullback_projectiveBundleProj`: **`𝐏(ℰ|_U) = 𝐏(ℰ) ×_X U`** over the
  presenting chart of `X`.

## Implementation notes

The finite local freeness of `ℰ` is the one of Stacks 03DL (2) on the small étale site of `X`.
It is used to put the chart bundles in the site: by
`AlgebraicGeometry.Space.isFiniteLocallyFree_restrictToChartScheme` the chart restriction is
finite locally free, so the chart bundle is proper over the chart, and a scheme of finite type
over an object of the site is an object of the site (Stacks 000R (5)).

The chart bundles are formed with the relative `Proj` of `Stacks.RelativeProj.Situation`, whose
base change is functorial (`Stacks.RelativeProj.projectiveBundleBaseChange_comp`); the second
presentation `Stacks.Chow.bundle` of the projective bundle of a finite locally free module, which
carries the properties of the projection, is compared with it by
`Stacks.ProjectiveBundle.presentationIso`.

The glued space depends on a presentation of `X`, which is chosen once and for all by
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]

/-! ### The chart bundles are proper and lie in the site -/

section Chart

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)
include hfree

/-- The chart restriction of a finite locally free module is finite locally free. -/
theorem isFiniteLocallyFree_chartBundleModule (V : SmallEtale B S hS X.1) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (chartBundleModule E V) :=
  have := isFiniteLocallyFree_restrictToChartScheme B S hS X E hE hfree V
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    (chartBundleModuleRestrictIso E V).symm

/-- **Over an étale chart the projection of the chart bundle is proper**: the chart restriction
is of finite type, and the projective bundle of a quasi-coherent module of finite type is proper
(Stacks 0800). -/
theorem isProper_chartBundleToChart (V : SmallEtale B S hS X.1) :
    _root_.AlgebraicGeometry.IsProper (chartBundleToChart E V) := by
  have := isFiniteLocallyFree_chartBundleModule E hfree V
  have : (chartBundleModule E V).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree _
  exact Stacks.RelativeProj.isProper_projectiveBundleToBase_of_isFiniteType (chartScheme V)
    (chartBundleModule E V)

/-- **The chart bundle over an étale chart is an object of the site**: it is of finite type over
the scheme of the chart, which is. -/
theorem contains_chartBundle (V : SmallEtale B S hS X.1) : B.Contains (chartBundle E V) := by
  have := isProper_chartBundleToChart E hfree V
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (chartBundleToChart E V)
    ((SmallEtale.toOver B S hS X.1).obj V).left.property

/-- **The cartesian family of chart projective bundles** `V ↦ 𝐏(ℰ|_V)` of a finite locally free
module. -/
def projectiveBundleChartFamily : CartesianChartFamily X where
  obj := chartBundle E
  toChart := chartBundleToChart E
  map := chartBundleMap E
  isPullback := isPullback_chartBundleMap E
  map_comp := chartBundleMap_comp E
  contains := contains_chartBundle E hfree

end Chart

/-! ### The presentation the bundle is glued over -/

/-- The presentation of `X` over which the projective bundle is glued. -/
abbrev projectiveBundlePresentation (X : AlgebraicSpaces B S hS) :
    Presentation B S hS X.obj X.property :=
  presentationOfIsAlgebraicSpace B S hS X.1 X.2

/-- The relation chart of the presentation is the fibre product of the presenting chart with
itself over `X`. -/
theorem isPullback_projectiveBundlePresentation (X : AlgebraicSpaces B S hS) :
    IsPullback
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map
        (presentationRelationTargetHom (projectiveBundlePresentation X))))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map
        (presentationRelationSourceHom (projectiveBundlePresentation X))))
      (presentationChart (projectiveBundlePresentation X)).obj.hom
      (presentationChart (projectiveBundlePresentation X)).obj.hom :=
  (projectiveBundlePresentation X).isPullback

/-- The presenting chart is surjective. -/
theorem surjective_projectiveBundlePresentation (X : AlgebraicSpaces B S hS) :
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
      (presentationChart (projectiveBundlePresentation X)).obj.hom :=
  (projectiveBundlePresentation X).surjective

/-! ### The projective bundle -/

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The projective bundle `𝐏(ℰ) = Proj_X(Sym^*(ℰ))` of a finite locally free module on an
algebraic space**, glued from the projective bundles of the restrictions of `ℰ` to the étale
charts of `X`. -/
def projectiveBundle : AlgebraicSpaces B S hS :=
  (projectiveBundleChartFamily E hfree).quotient
    (presentationRelationTargetHom (projectiveBundlePresentation X))
    (presentationRelationSourceHom (projectiveBundlePresentation X))
    (isPullback_projectiveBundlePresentation X)

/-- **The projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle.** -/
def projectiveBundleProj : projectiveBundle E hfree ⟶ X :=
  (projectiveBundleChartFamily E hfree).quotientHom
    (presentationRelationTargetHom (projectiveBundlePresentation X))
    (presentationRelationSourceHom (projectiveBundlePresentation X))
    (isPullback_projectiveBundlePresentation X)

/-- The étale chart `𝐏(ℰ|_U) ⟶ 𝐏(ℰ)` of the projective bundle over the presenting chart `U`. -/
def projectiveBundleChart :
    yoneda.obj ((projectiveBundleChartFamily E hfree).site
        (presentationChart (projectiveBundlePresentation X))) ⟶ (projectiveBundle E hfree).1 :=
  Stacks.Groupoids.quotientChart (BigFppfOver.topology B S hS)
    (Over.post (X := B.obj hS) B.inclusion)
    ((projectiveBundleChartFamily E hfree).site
      (presentationChart (projectiveBundlePresentation X)))
    (relation B S hS ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationSourceHom (projectiveBundlePresentation X)))
      ((projectiveBundleChartFamily E hfree).siteMap
        (presentationRelationTargetHom (projectiveBundlePresentation X))))

/-- **Over the presenting chart `U` of `X`, the projective bundle is the projective bundle of the
restriction of `ℰ`**: the square formed by the chart of `𝐏(ℰ)`, the projection of `𝐏(ℰ|_U)` to
`U`, the projection `π` and the chart `U ⟶ X` is cartesian. -/
theorem isPullback_projectiveBundleProj :
    IsPullback (projectiveBundleChart E hfree)
      (yoneda.map ((projectiveBundleChartFamily E hfree).siteToChart
        (presentationChart (projectiveBundlePresentation X))))
      (projectiveBundleProj E hfree).hom
      (presentationChart (projectiveBundlePresentation X)).obj.hom :=
  (projectiveBundleChartFamily E hfree).isPullback_quotientHom _ _
    (isPullback_projectiveBundlePresentation X) (surjective_projectiveBundlePresentation X)

end AlgebraicGeometry.Space

end
