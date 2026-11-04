module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartPerfectComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesHomEq
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# `𝒪_X ⊗ f^*(M~) ≅ 𝒪_X ⊗_A M` at a chart of `Spaces'_{fp, flat, proper}`

Let `x` be a flat, proper, finitely presented algebraic space `f : X → Spec A`, and let `M~` be
the module `𝒪_{Spec A} ⊗_A M` on the small étale site of `Spec A`
(`AlgebraicGeometry.Space.affineBaseTilde`). This file identifies `𝒪_X ⊗ f^*(M~)`, the coefficient
of [Stacks, Tag 08JR] at `𝒢^• = 𝒪_X[0]` (`AlgebraicGeometry.Space.tensorPullbackBifunctor`), with
the module `𝒪_X ⊗_A M` of [Stacks, Tag 0D3F] (`AlgebraicGeometry.Space.baseRingTensorModule`),
naturally in the `A`-module `M`: the unit law of `⊗`, the change of base ring along
`A ≅ Γ(Spec A)`, and `f^*(𝒪_{Spec A} ⊗ N) ≅ 𝒪_X ⊗ N`
(`AlgebraicGeometry.Space.baseRingTensorModulePullbackIso`).

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.chartTensorModule`: `M ↦ 𝒪_X ⊗_A M`, spelled on the
  small étale ringed topos of `X` as 08JR is.
* `AlgebraicGeometry.Space.ProperFlatLift.chartPullbackTildeIso`: `f^*(M~) ≅ 𝒪_X ⊗_A M`.
* `AlgebraicGeometry.Space.ProperFlatLift.chartTensorPullbackTildeIso`:
  `𝒪_X ⊗ f^*(M~) ≅ 𝒪_X ⊗_A M`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- One standard-model line, scoped to this file: the base declarations
-- `AlgebraicGeometry.Space.tensorPullbackExtGroup` and
-- `AlgebraicGeometry.Space.tensorPullbackComplexDerived` are stated in the model
-- `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology hasMapBifunctor_sheafTensor_smallEtaleRingedTopos
  smallEtaleRingedSite_hasSheafify smallEtaleRingedSite_wEqualsLocallyBijective
  smallEtaleRingedSite_hasSheafify_over smallEtaleRingedSite_wEqualsLocallyBijective_over

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

/-- Sheafification of abelian presheaves with sections in the universe of the schemes on the
small étale site, spelled through the small étale ringed topos; instance search does not settle
the universes of the general instance `AlgebraicGeometry.Space.SmallEtale.instHasSheafify` here. -/
local instance (priority := high) smallEtaleRingedTopos_hasSheafify_addCommGrpCat
    (Z : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleRingedTopos B S hS Z).J AddCommGrpCat.{u} :=
  SmallEtale.instHasSheafify B S hS Z.1 AddCommGrpCat.{u}

/-- Local equivalences of abelian presheaves on the small étale site, spelled through the small
étale ringed topos, at the universe of the schemes. -/
local instance (priority := high) smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat
    (Z : AlgebraicSpaces B S hS) :
    (smallEtaleRingedTopos B S hS Z).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  SmallEtale.instWEqualsLocallyBijective B S hS Z.1 AddCommGrpCat.{u}

/-! ### The coefficient `𝒪_X[0] ⊗ f^*(M~[0])` -/

/-- `f^*` of modules on the small étale sites, in the spelling of `tensorPullbackBifunctor`, is
`AlgebraicGeometry.Space.modulePullback`. -/
theorem modulePullback_chartStructureMap_eq :
    modulePullback B S hS (chartStructureMap x hx) =
      ((smallEtaleRingedToposHom B S hS (chartStructureMap x hx)).toModulesHom.pullbackModules :
        SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
            (schemeSpace (algebraOver A B S hS toS hA))) ⥤
          SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS x.obj.obj.left)) :=
  (modulePullback_eq B S hS _).trans (RingedToposHom.pullbackModules_toRingedToposModulesHom
    (smallEtaleRingedToposHom B S hS (chartStructureMap x hx)))

/-- **`M ↦ 𝒪_X ⊗_A M`** (Stacks 0D3F), `AlgebraicGeometry.Space.baseRingTensorModule` at the
base-ring datum of the chart, spelled as a functor into the modules on the small étale ringed
topos of `X`, the spelling of [Stacks, Tag 08JR]. -/
def chartTensorModule : ModuleCat.{u} A ⥤
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS x.obj.obj.left) :=
  baseRingTensorModule B S hS x.obj.obj.left (chartBaseRingHom x hx)

/-- **`f^*(M~) ≅ 𝒪_X ⊗_A M`**, naturally in the `A`-module `M`: the change of base ring along
`A ≅ Γ(Spec A)` on both sides, and `f^*(𝒪_{Spec A} ⊗ N) ≅ 𝒪_X ⊗ N` for `Γ(Spec A)`-modules `N`. -/
def chartPullbackTildeIso :
    affineBaseTilde A B S hS toS hA ⋙ modulePullback B S hS (chartStructureMap x hx) ≅
      chartTensorModule x hx :=
  Functor.isoWhiskerRight (baseRingTensorModuleCompIso B S hS
      (schemeSpace (algebraOver A B S hS toS hA)) (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (baseRingHomOfMap (𝟙 (schemeSpace (algebraOver A B S hS toS hA))))).symm _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars.{u, u, u}
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (baseRingTensorModulePullbackIso B S hS (chartStructureMap x hx)) ≪≫
    baseRingTensorModuleCompIso B S hS x.obj.obj.left (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (baseRingHomOfMap (chartStructureMap x hx))

/-- **`𝒪_X ⊗ f^*(M~) ≅ 𝒪_X ⊗_A M`**, naturally in `M`: the unit law of `⊗` followed by
`chartPullbackTildeIso`. -/
def chartTensorPullbackTildeIso :
    affineBaseTilde A B S hS toS hA ⋙
        (tensorPullbackBifunctor (chartStructureMap x hx)).obj (SheafOfModules.unit _) ≅
      chartTensorModule x hx :=
  Functor.isoWhiskerLeft (affineBaseTilde A B S hS toS hA)
      (Functor.isoWhiskerRight (eqToIso (modulePullback_chartStructureMap_eq x hx)).symm _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (affineBaseTilde A B S hS toS hA ⋙
      modulePullback B S hS (chartStructureMap x hx))
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding _).app (SheafOfModules.unit _) ≪≫
        Stacks.SheafOfModules.sheafTensorUnitNatIsoFreeSections _) ≪≫
    Functor.rightUnitor _ ≪≫ chartPullbackTildeIso x hx

end AlgebraicGeometry.Space.ProperFlatLift

end
