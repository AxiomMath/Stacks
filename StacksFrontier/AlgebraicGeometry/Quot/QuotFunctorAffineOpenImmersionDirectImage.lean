module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification

/-!
# Stacks 0DP2: the morphism of Quot functors along an affine open immersion is an open immersion

Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine open immersion of algebraic spaces
which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module.  Stacks 0DP2 asserts that the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of
Stacks 0DP1 is an open immersion.

The morphism of Stacks 0DP1 sends a quotient `F_T ⟶ Q` over a test scheme `T` to
`G_T ⟶ π_{T,*}F_T ⟶ π_{T,*}Q`, through the base change map `G_T ⟶ π_{T,*}F_T` of Stacks 07U8;
on the test schemes it is
`AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotFunctorMap`.  Being an open
immersion is a property of a morphism of presheaves on the schemes of the site with values in the
universe of the site, while quotients are recorded by subobjects, one universe up; so the
morphism is read on the Quot presheaves of the site and then in their canonical models
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheafModel` in the universe of the site.

By `QuotPushforwardSituation.isOpenImmersion_mapFrom_directImageQuotSitePresheafMap`, the
morphism is a monomorphism whose range is cut out by the condition `Supp(Q) ⊆ |X_T|`, which is
open on `T`.

## Main definitions

* `AlgebraicGeometry.Space.QuotPushforwardSituation.ofAffineOpenImmersion`: the standing data of
  Stacks 0DP1 for an affine open immersion, which is quasi-finite.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotSitePresheafMap`: the
  morphism of Stacks 0DP1 on the Quot presheaves of the site.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotModelMap`: the same morphism
  read in the canonical models of the two Quot presheaves.

## Main results

* `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotSitePresheafMap_app`: the
  morphism on the Quot presheaves is the morphism of Quot functors of Stacks 0DP1.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.isOpenImmersion_pushforwardQuotModelMap`: the
  morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` along an affine open immersion is an open immersion.

## References

* [Stacks Project, Tag 0DP2](https://stacks.math.columbia.edu/tag/0DP2)
* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The modules here have their sections in the universe of the schemes, which the ambient-universe
-- abelian structure of `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` cannot describe.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotPushforwardSituation

/-- An affine open immersion of algebraic spaces is quasi-finite: it is étale, hence locally
quasi-finite (Stacks 03XJ), and affine, hence quasi-compact. -/
theorem isQuasiFinite_of_isOpenImmersion_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (π : X ⟶ Y) (hπ : IsOpenImmersion B S hS π.hom) (haff : IsAffineHom B S hS π.hom) :
    IsQuasiFinite B S hS π.hom :=
  ⟨isLocallyQuasiFinite_of_presheafEtale B S hS (presheaf_etale_of_isOpenImmersion B S hS hπ),
    isQuasiCompact_of_isAffineHom' B S hS π.hom X.2 Y.2 haff⟩

/-- An affine open immersion `π : X ⟶ Y` of algebraic spaces which are separated and of finite
presentation over an algebraic space `B`, together with a quasi-coherent `𝒪_X`-module `F`, as the
standing data of Stacks 0DP1: an affine open immersion is quasi-finite. -/
def ofAffineOpenImmersion (base X Y : AlgebraicSpaces B S hS) (π : X ⟶ Y)
    (structureX : X ⟶ base) (structureY : Y ⟶ base) (comp : π ≫ structureY = structureX)
    (F : Modules.{u, u} B S hS X.1 X.2) (quasicoherent : F.IsQuasicoherentOnSite)
    (openImmersion : IsOpenImmersion B S hS π.hom) (affine : IsAffineHom B S hS π.hom)
    (separatedX : IsSeparated B S hS structureX.hom)
    (separatedY : IsSeparated B S hS structureY.hom)
    (finitePresentationX : IsFinitePresentation B S hS structureX.hom)
    (finitePresentationY : IsFinitePresentation B S hS structureY.hom) :
    QuotPushforwardSituation B S hS where
  base := base
  X := X
  Y := Y
  π := π
  structureX := structureX
  structureY := structureY
  comp := comp
  F := F
  quasicoherent := quasicoherent
  affine := affine
  quasiFinite := isQuasiFinite_of_isOpenImmersion_of_isAffineHom π openImmersion affine
  separatedX := separatedX
  separatedY := separatedY
  finitePresentationX := finitePresentationX
  finitePresentationY := finitePresentationY

variable (D : QuotPushforwardSituation B S hS)

/-- The direct image of every member of `Quot_{F/X/B}(T)` is a member of `Quot_{π_*F/Y/B}(T)`
(Stacks 0DP1 on objects, from claim (a) of the proof of Stacks 0DN9). -/
theorem directImageQuotientMem : D.DirectImageQuotientMem :=
  fun T K' hK' => D.directImageQuotient_mem D.pushforwardIsCoherent T K' hK'

/-- **The morphism of Stacks 0DP1 on the Quot presheaves of the site**: over a scheme of the site
it sends a quotient to its direct image. -/
def pushforwardQuotSitePresheafMap :
    D.sourceSituation.quotSitePresheaf ⟶ D.directImageSituation.quotSitePresheaf :=
  D.directImageQuotSitePresheafMap D.directImageQuotientMem

/-- **The morphism on the Quot presheaves of the site is the morphism of Stacks 0DP1**: over a
scheme of the site it sends a quotient over the test scheme `T ⟶ B` to a quotient over the same
test scheme, whose kernel is the value at that test scheme of
`AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotFunctorMap`. -/
theorem pushforwardQuotSitePresheafMap_app {T : BigFppfOver B S hS}
    (x : QuotFamilyOver D.sourceSituation T) :
    (D.pushforwardQuotSitePresheafMap.app (Opposite.op T) x).toBase = x.toBase ∧
      (D.pushforwardQuotSitePresheafMap.app (Opposite.op T) x).subobject =
        (D.pushforwardQuotFunctorMap.app (Opposite.op (CostructuredArrow.mk x.toBase))
          ⟨x.subobject, x.mem⟩).1 :=
  ⟨rfl, rfl⟩

/-- **The morphism of Stacks 0DP1 read in the canonical models** of the two Quot presheaves in the
universe of the site. -/
def pushforwardQuotModelMap :
    D.sourceSituation.quotSitePresheafModel.presheaf ⟶
      D.directImageSituation.quotSitePresheafModel.presheaf :=
  D.directImageSituation.quotSitePresheafModel.mapFrom
    (D.sourceSituation.quotSitePresheafModel.iso.hom ≫ D.pushforwardQuotSitePresheafMap)

/-- The morphism read in the canonical models is the morphism on the Quot presheaves of the site:
on a section of the model of `Quot_{F/X/B}` it takes the direct image of the corresponding
quotient. -/
theorem familyEquiv_pushforwardQuotModelMap (T : BigFppfOver B S hS)
    (z : D.sourceSituation.quotSitePresheafModel.presheaf.obj (Opposite.op T)) :
    D.directImageSituation.quotSitePresheafModel.familyEquiv T
        (D.pushforwardQuotModelMap.app (Opposite.op T) z) =
      D.pushforwardQuotSitePresheafMap.app (Opposite.op T)
        (D.sourceSituation.quotSitePresheafModel.familyEquiv T z) :=
  types_congr_hom (D.directImageSituation.quotSitePresheafModel.iso.inv_hom_id_app (Opposite.op T))
    ((D.sourceSituation.quotSitePresheafModel.iso.hom ≫ D.pushforwardQuotSitePresheafMap).app
      (Opposite.op T) (ULift.up z))

/-- **The morphism of Stacks 0DP1 along an affine open immersion is an open immersion**, read in
the canonical models of the two Quot presheaves. -/
theorem isOpenImmersion_pushforwardQuotModelMap_of_isOpenImmersion
    (hπ : IsOpenImmersion B S hS D.π.hom) :
    IsOpenImmersion B S hS D.pushforwardQuotModelMap :=
  D.isOpenImmersion_mapFrom_directImageQuotSitePresheafMap hπ _ _ _

/-- Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine open immersion of algebraic spaces
which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module.  Then the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of Stacks 0DP1 is an open
immersion.

The morphism is `AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotFunctorMap`,
read on the Quot presheaves of the site
(`AlgebraicGeometry.Space.QuotPushforwardSituation.pushforwardQuotSitePresheafMap_app`) and then in
their canonical models in the universe of the site, where being an open immersion of algebraic
spaces is defined (Stacks 02YU). -/
@[stacks 0DP2]
theorem isOpenImmersion_pushforwardQuotModelMap (base X Y : AlgebraicSpaces B S hS)
    (π : X ⟶ Y) (structureX : X ⟶ base) (structureY : Y ⟶ base)
    (comp : π ≫ structureY = structureX) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (hπ : IsOpenImmersion B S hS π.hom)
    (haff : IsAffineHom B S hS π.hom) (hsepX : IsSeparated B S hS structureX.hom)
    (hsepY : IsSeparated B S hS structureY.hom)
    (hfpX : IsFinitePresentation B S hS structureX.hom)
    (hfpY : IsFinitePresentation B S hS structureY.hom) :
    IsOpenImmersion B S hS (ofAffineOpenImmersion base X Y π structureX structureY comp F hF hπ
      haff hsepX hsepY hfpX hfpY).pushforwardQuotModelMap :=
  isOpenImmersion_pushforwardQuotModelMap_of_isOpenImmersion _ hπ

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
