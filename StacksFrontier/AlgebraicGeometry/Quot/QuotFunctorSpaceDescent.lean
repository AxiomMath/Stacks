module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportDescent

/-!
# The points of the Quot functor over an algebraic space, read on a chart

In Situation 09TR, Stacks 0D3V identifies the morphisms of sheaves from an algebraic space `T`
into `Quot_{F/X/B}` with the pairs `(h, F_T ⟶ Q)` where `h : T ⟶ B` and `Q` is of finite
presentation, flat over `T`, with support proper over `T`.  Its proof observes that both sides
are subsets of the two sides of the second identification of Stacks 0D3U, for `Q^{fp}_{F/X/B}`,
and that the subsets correspond because, for a surjective étale chart `U ⟶ T`, a finite type
quasi-coherent module on `X_T` has support proper over `T` exactly when its pullback to `X_U`
has support proper over `U` (Stacks 0422 and 089C).

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `QuotientSituation.isPullback_spaceChartMap`: for `U ⟶ T` out of a scheme of the site,
  `X_U ⟶ X_T` is the base change of `X_T ⟶ T`.
* `QuotientSituation.spaceQuotientRestrict_mem_finitePresentationQuotients`: the restriction of
  a pair of `Q^{fp}` over `T` to a scheme of the site is a pair of `Q^{fp}`.
* `QuotSituation.isProperlySupportedOver_spaceQuotientRestrict` and
  `QuotSituation.spaceIsProperlySupportedOver_of_spaceQuotientRestrict`: proper support of a
  quotient over `T` passes to every scheme mapping to `T` (Stacks 0CZJ) and is detected on a
  surjective étale chart (Stacks 0422 with 089C).

## References

* [Stacks Project, Tag 0D3V](https://stacks.math.columbia.edu/tag/0D3V)
* [Stacks Project, Tag 0D3U](https://stacks.math.columbia.edu/tag/0D3U)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 089C](https://stacks.math.columbia.edu/tag/089C)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

-- The modules here have their sections in the universe `u` of the schemes; the ambient-universe
-- abelian structure of the cohomology of modules would be selected ahead of
-- `SheafOfModules.instAbelian` and leave the module universe of every subobject unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- **The base change at a chart is a base change of the base change at the algebraic space.**
For `h : T ⟶ Y` out of an algebraic space and `α : U ⟶ T` out of a scheme of the site, the
square formed by `X_U ⟶ X_T`, the projections to `U` and `T`, and `α` is cartesian: pasted onto
the cartesian square of `X_T` it gives the cartesian square of `X_U`. -/
theorem isPullback_spaceChartMap {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T) :
    IsPullback (D.spaceChartMap h α) (D.projection (D.testAt (α ≫ h))) (D.spaceBaseToSpace h)
      α := by
  refine IsPullback.of_right ?_ ?_ (D.isPullback_spaceBaseChange h)
  · rw [D.spaceChartMap_comp_toSource h α]
    exact AlgebraicSpaces.isPullback_fiberProduct B S hS D.f (α ≫ h)
  · exact (D.isPullback_spaceBaseChange h).lift_snd _ _ _

/-- **The restriction of a pair of `Q^{fp}` over an algebraic space to a scheme of the site is a
pair of `Q^{fp}`.**  The restricted quotient is the inverse image of the quotient along
`X_U ⟶ X_T` (`AlgebraicGeometry.Space.QuotientSituation.spaceQuotientRestrictCokernelIso`),
quasi-coherent by Stacks 03GA, flat over `U` by Stacks 05VW at the cartesian square
`AlgebraicGeometry.Space.QuotientSituation.isPullback_spaceChartMap`, and of finite presentation
by Stacks 03DO. -/
theorem spaceQuotientRestrict_mem_finitePresentationQuotients {T : AlgebraicSpaces B S hS}
    (h : T ⟶ D.Y) {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T)
    {K : Subobject (D.spaceBaseModule h)} (hK : K ∈ D.spaceFinitePresentationQuotients h) :
    D.spaceQuotientRestrict h α K ∈ D.finitePresentationQuotients (D.testAt (α ≫ h)) := by
  obtain ⟨⟨hqc, hflat⟩, hfp⟩ := hK
  have hpb := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (D.spaceChartMap h α) (cokernel K.arrow) hqc
  let e := (D.spaceQuotientRestrictCokernelIso h α K).symm
  exact ⟨⟨.of_iso e hpb,
    IsFlatOver.of_iso B S hS (D.space (D.testAt (α ≫ h))).2 e
      (isFlatOver_modulePullback B S hS (D.isPullback_spaceChartMap h α) (cokernel K.arrow)
        hflat)⟩,
    .of_iso e (isFinitePresentationOnSite_modulePullback B S hS (D.spaceChartMap h α)
      (cokernel K.arrow) hfp)⟩

end QuotientSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **Stacks 0CZJ at a chart of an algebraic space.**  The pullback along `X_U ⟶ X_T` of a finite
type quasi-coherent module on `X_T` whose support is proper over `T` has support proper over the
test scheme `U`, for any morphism `U ⟶ T` out of a scheme of the site. -/
theorem isProperlySupportedOver_modulePullback_spaceChartMap {T : AlgebraicSpaces B S hS}
    (h : T ⟶ D.Y) {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T)
    (G : Modules.{u, u} B S hS (D.spaceBaseChange h).1 (D.spaceBaseChange h).2)
    (hqc : G.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite G)
    (hG : D.SpaceIsProperlySupportedOver h G) :
    D.IsProperlySupportedOver (D.testAt (α ≫ h))
      ((modulePullback B S hS (D.spaceChartMap h α)).obj G) := by
  obtain ⟨_, hproper⟩ := hG
  exact ⟨isClosed_supportOfSheaf_modulePullback B S hS (D.spaceChartMap h α) G hft,
    isProperOver_supportOfSheaf_modulePullback B S hS (D.isPullback_spaceChartMap h α)
      (D.isLocallyOfFiniteType_spaceBaseToSpace h) G hqc hft hproper⟩

/-- **Proper support over an algebraic space is read on a surjective étale chart.**  For
`h : T ⟶ Y` out of an algebraic space and a surjective étale scheme chart `a : U ⟶ T`, a finite
type quasi-coherent module on `X_T` whose pullback to `X_U` has support proper over `U` has
support proper over `T` (Stacks 0422 and 089C). -/
theorem spaceIsProperlySupportedOver_of_chart {T : AlgebraicSpaces B S hS} (h : T ⟶ D.Y)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ T.obj}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (G : Modules.{u, u} B S hS (D.spaceBaseChange h).1 (D.spaceBaseChange h).2)
    (hqc : G.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite G)
    (hG : D.IsProperlySupportedOver
      (D.testAt ((ObjectProperty.homMk a : (schemeSpaceFunctor B S hS).obj U ⟶ T) ≫ h))
      ((modulePullback B S hS (D.spaceChartMap h (ObjectProperty.homMk a))).obj G)) :
    D.SpaceIsProperlySupportedOver h G := by
  have hcov := ofArrows_atlas_mem_fppf_precoverage.{u, 0} B S hS T.property hsurj hetale
  rw [Presieve.ofArrows_pUnit] at hcov
  exact hasProperSupport_of_isPullback_of_mem_fppf.{0} B S hS
    (D.isPullback_spaceChartMap h (ObjectProperty.homMk a))
    (D.isLocallyOfFiniteType_spaceBaseToSpace h) hcov
    (isFlat_atlas B S hS T.property ((isEtale_iff_presheaf_of_yoneda B S hS a).2 hetale))
    G hqc hft hG

/-- The restriction of a quotient of `F_T` with proper support to a scheme `U` of the site
mapping to `T` has support proper over `U`. -/
theorem isProperlySupportedOver_spaceQuotientRestrict {T : AlgebraicSpaces B S hS}
    (h : T ⟶ D.Y) {U : BigFppfOver B S hS} (α : (schemeSpaceFunctor B S hS).obj U ⟶ T)
    (K : Subobject (D.spaceBaseModule h)) (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite (cokernel K.arrow))
    (hK : D.SpaceIsProperlySupportedOver h (cokernel K.arrow)) :
    D.IsProperlySupportedOver (D.testAt (α ≫ h))
      (D.quotientModule (D.testAt (α ≫ h)) (D.spaceQuotientRestrict h α K)) :=
  D.isProperlySupportedOver_of_iso (D.spaceQuotientRestrictCokernelIso h α K).symm
    (D.isProperlySupportedOver_modulePullback_spaceChartMap h α _ hqc hft hK)

/-- A quotient of `F_T`, of finite type and quasi-coherent, whose restriction to a surjective
étale scheme chart of `T` has support proper over the chart has support proper over `T`. -/
theorem spaceIsProperlySupportedOver_of_spaceQuotientRestrict {T : AlgebraicSpaces B S hS}
    (h : T ⟶ D.Y) {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ T.obj}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (K : Subobject (D.spaceBaseModule h)) (hqc : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite (cokernel K.arrow))
    (hK : D.IsProperlySupportedOver
      (D.testAt ((ObjectProperty.homMk a : (schemeSpaceFunctor B S hS).obj U ⟶ T) ≫ h))
      (D.quotientModule _ (D.spaceQuotientRestrict h (ObjectProperty.homMk a) K))) :
    D.SpaceIsProperlySupportedOver h (cokernel K.arrow) :=
  D.spaceIsProperlySupportedOver_of_chart h hsurj hetale _ hqc hft
    (D.isProperlySupportedOver_of_iso (D.spaceQuotientRestrictCokernelIso h _ K) hK)

end QuotSituation

end AlgebraicGeometry.Space

end
