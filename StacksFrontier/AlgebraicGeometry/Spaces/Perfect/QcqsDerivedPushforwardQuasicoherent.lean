module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineDerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentDerivedTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
import all StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion

/-!
# The derived direct image out of a quasi-compact quasi-separated algebraic space preserves
`D_QCoh`

Let `x : W ⟶ X` be a morphism of algebraic spaces over a scheme `S`, with `W` quasi-compact and
quasi-separated and `X` quasi-separated.  Then every right derived functor of `x_*` carries
`D_QCoh(𝒪_W)` into `D_QCoh(𝒪_X)`.  This is the case of Stacks 08FA (1) that the first proof of
Stacks 0CR4 consumes (for `W` affine and étale over `X`).

The proof does not pass through the cohomological dimension bounds of Stacks 073G.  Membership in
`D_QCoh(𝒪_X)` is tested on the affine étale charts `A` of `X` (Stacks 08F2); over such a chart
the restriction of `Rx_*L` is the derived direct image along the base change
`W ×_X A ⟶ A` (Stacks 08GE); `W ×_X A` is quasi-compact and quasi-separated, so the induction
principle of Stacks 08GP together with the relative Mayer–Vietoris triangle of Stacks 08JK
reduces to a morphism between affine algebraic spaces, which is affine, where
`AlgebraicGeometry.Space.qcohDerivedProp_derivedPushforward_of_isAffineHom` applies.

## Main results

* `AlgebraicGeometry.Space.qcohDerivedProp_derivedPushforward_of_affine_target`: the case of an
  affine target.
* `AlgebraicGeometry.Space.qcohDerivedProp_derivedPushforward_of_qcqs`: the general case.

## References

* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_QcqsDerivedPushforwardQuasicoherent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_QcqsDerivedPushforwardQuasicoherent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

include hZ in
/-- **`Rx_*` preserves `D_QCoh` for `x` with quasi-compact quasi-separated source and affine
target**, by the induction of `AlgebraicGeometry.Space.prop_derivedPushforward_of_affine` down
to morphisms between affine algebraic spaces. -/
theorem qcohDerivedProp_derivedPushforward_of_affine_target {W A : AlgebraicSpaces B S hS}
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hA : IsAffineSpace B S hS A.1) (x : W ⟶ A)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS A.1 A.2))
    (α : (modulePushforward B S hS x).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (L : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (hL : qcohDerivedProp B S hS W L) :
    qcohDerivedProp B S hS A (R.obj L) :=
  prop_derivedPushforward_of_affine B S hS hZ hWqc hWqs x (qcohDerivedProp B S hS A)
    (fun Y => qcohDerivedProp B S hS Y)
    (fun e he E hE => derivedQuasicoherent_etaleModulePullback B S hS e he E hE)
    (fun _ y _ hY E hE R α hR =>
      have := hR
      qcohDerivedProp_derivedPushforward_of_isAffineHom B S hS (y ≫ x)
        (isAffineHom_of_isAffineSpace B S hS _ hY hA)
        R α E hE)
    L hL R α

include hZ in
/-- **`Rx_*` preserves `D_QCoh` for `x` with quasi-compact quasi-separated source and
quasi-separated target.**  Membership of `Rx_*L` in `D_QCoh(𝒪_X)` is tested on the affine étale
charts `A` of `X` (Stacks 08F2); there `(Rx_*L)|_A` is the derived direct image of `L|_{W ×_X A}`
along `W ×_X A ⟶ A` (Stacks 08GE), and `W ×_X A` is quasi-compact and quasi-separated, so
`AlgebraicGeometry.Space.qcohDerivedProp_derivedPushforward_of_affine_target` applies. -/
theorem qcohDerivedProp_derivedPushforward_of_qcqs {W X : AlgebraicSpaces B S hS}
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (x : W ⟶ X)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (α : (modulePushforward B S hS x).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (L : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (hL : qcohDerivedProp B S hS W L) :
    qcohDerivedProp B S hS X (R.obj L) := by
  refine ((derivedQuasicoherent_tfae B S hS (R.obj L)).out 1 2).2 fun A hA => ?_
  let g := chartToSpace B S hS X A
  have hg : IsEtale B S hS g.hom := isEtale_chartToSpace B S hS X A
  let T := AlgebraicSpaces.fiberProduct B S hS x g
  let i : T ⟶ W := ObjectProperty.homMk (pullback.fst x.hom g.hom)
  let f' : T ⟶ chartSpace B S hS X A := ObjectProperty.homMk (pullback.snd x.hom g.hom)
  have sq : IsPullback i f' x g := AlgebraicSpaces.isPullback_fiberProduct B S hS x g
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g x sq.flip hg
  have hTqc : IsQuasiCompactSpace B S hS T.1 :=
    isQuasiCompactSpace_pullback B S hS hZ x.hom g.hom W.2 X.2 hWqc
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hA) hXqs
  have hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1 :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ x.hom g.hom W.2 (chartSpace B S hS X A).2 X.2
      hWqs (isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ _ hA)
  have := hasRightDerivedFunctor_mapMayerVietorisFunctor_modules B S hS
    (X := T) (Z := chartSpace B S hS X A) (modulePushforward B S hS f')
  let Rf' := ((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αf' := ((modulePushforward B S hS f').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryFactorsh
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategoryFactorsh
  let e := derivedModulePushforwardEtaleRestrictIso B S hS sq hg
    (etaleModuleLowerShriekAdjunction B S hS i hi) R Rf'
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory α αf'
    (etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategoryFactorsh.inv
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryFactorsh.inv
  have hT := qcohDerivedProp_derivedPushforward_of_affine_target B S hS hZ hTqc hTqs
    (isAffineSpace_yoneda B S hS _ hA) f' Rf' αf' _
    (derivedQuasicoherent_etaleModulePullback B S hS i hi L hL)
  exact (qcohDerivedProp B S hS (chartSpace B S hS X A)).prop_of_iso (e.app L).symm hT

end AlgebraicGeometry.Space

end
