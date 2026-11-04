module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of a morphism locally of finite type is of finite type

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type. Stacks 05ZE asserts that `Ω_{X/Y}` is an `𝒪_X`-module of finite type. This file proves it
with no further hypothesis, by the source's argument: étale localization reduces it to the
scheme case, Morphisms, Lemma 01V2.

An atlas `q : V ⟶ Y` of the target lifts, by Stacks 02X1, to a surjective étale chart
`p : U ⟶ X` of the source together with a morphism `α : U ⟶ V` of schemes over `q`. Since `f`
is locally of finite type (Stacks 03XF(1)), so is `α`. On the chart, the pullback of `Ω_{X/Y}`
is the sheaf of differentials of `α` (Stacks 04CU), that is the small-étale module associated
to the Zariski sheaf `Ω_{U/V}`, which is of finite type by Stacks 01V2; the associated module of
a finite type module is of finite type (Stacks 08HD), and finite type descends from one
surjective étale chart.

The base's `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials` reaches the same
conclusion from two carried hypotheses; this file needs neither.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeOnSite_representedAssociatedModule`: the small-étale
  module on a represented algebraic space attached to a finite type module on its scheme is of
  finite type.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_of_etaleModulePullback_chartToSpace`: finite type
  descends from the étale pullback to one surjective étale chart.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_hom`:
  **Stacks 05ZE**.

## References

* [Stacks Project, Tag 05ZE](https://stacks.math.columbia.edu/tag/05ZE)
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small-étale module attached to a finite type module on a scheme of the big fppf site is
of finite type on the small étale site of the algebraic space the scheme represents.**

The associated module on the scheme's own small étale site is of finite type by Stacks 08HD, and
finite type is invariant under the equivalence of that site with the small étale site of the
represented algebraic space, the two structure sheaves being equal. -/
theorem isFiniteTypeOnSite_representedAssociatedModule
    (U : BigFppfOver B S hS) (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hM : SheafOfModules.IsFiniteTypeOnSite M) :
    ((representedAssociatedModule B S hS U hU).obj M).IsFiniteTypeOnSite := by
  have := AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M hM
  exact Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex
    (J' := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    ((AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)

/-- **Finite type descends from the étale pullback to one surjective étale chart.** If the
pullback of an `𝒪_X`-module along the structure morphism of an étale scheme chart `V` of `X`
which is surjective on points is of finite type, then so is the module.

The étale pullback along the chart is the restriction to the slice at `V` read through the
comparison of Stacks 04M0, and finite type is tested on the slice at a surjective chart. -/
theorem isFiniteTypeOnSite_of_etaleModulePullback_chartToSpace
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS V.1.hom)
    (h : ((etaleModulePullback B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V)).obj M).IsFiniteTypeOnSite) :
    M.IsFiniteTypeOnSite :=
  (isFiniteTypeOnSite_iff_over_of_isSurjective B S hS X.1 X.2 M V hsurj).2
    ((isFiniteTypeOnSite_chartSmallEtaleRestriction_iff B S hS X M V).1
      (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
        (chartSmallEtaleRestrictionFunctorObjIso X M V).symm h))

/-- **Stacks 05ZE.** If `f : X ⟶ Y` is a morphism of algebraic spaces over `S` which is locally
of finite type, then the sheaf of differentials `Ω_{X/Y}` is an `𝒪_X`-module of finite type.

The proof is the source's. An atlas `q : V ⟶ Y` lifts, by Stacks 02X1, to a surjective étale
chart `p : U ⟶ X` and a morphism `α : U ⟶ V` of schemes over `q`; `α` is locally of finite type
because `f` is. The pullback of `Ω_{X/Y}` to `U` is the sheaf of differentials of `α`
(Stacks 04CU), which is the small-étale module associated to `Ω_{U/V}`; that is of finite type by
Stacks 01V2 and Stacks 08HD, and finite type descends from the surjective chart. -/
@[stacks 05ZE]
theorem isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_hom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite := by
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  obtain ⟨U, p, α, hdiag, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.property Y.property f.hom V q hqS hqE
  let W : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk p, hpE⟩
  let a : chartSpace B S hS X W ⟶ X := chartToSpace B S hS X W
  let ψ : schemeSpace U ⟶ schemeSpace V := schemeSpaceMap α
  let bb : schemeSpace V ⟶ Y := ObjectProperty.homMk q
  have haE : IsEtale B S hS a.hom := isEtale_chartToSpace B S hS X W
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V p q α hpE hqE hdiag.symm
  obtain ⟨echart⟩ := sheafOfDifferentialsSchemeComparison B S hS U V α
  have hψ : (sheafOfDifferentials B S hS ψ).IsFiniteTypeOnSite :=
    Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso echart.symm
      (isFiniteTypeOnSite_representedAssociatedModule B S hS U _ _
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ inferInstance))
  exact isFiniteTypeOnSite_of_etaleModulePullback_chartToSpace B S hS X _ W
    (isSurjective_of_presheafSurjective B S hS p hpS)
    (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS a haE).app (sheafOfDifferentials B S hS f))
      (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
        (sheafOfDifferentialsEtaleLocalizationIso B S hS f a ψ bb haE
          (isEtale_of_presheaf_etale B S hS hqE) (ObjectProperty.hom_ext _ hdiag)).symm hψ))

end AlgebraicGeometry.Space

end
