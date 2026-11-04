/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistingModule
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.BaseReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.Hilbert
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist

/-!
# The reading of the pullback of `𝒪(1)` is `𝒪(1)`

Let `F/X/B` be a Quot situation over `Spec ℤ` with a projective frame `X = B × ℙⁿ_ℤ`, and let `𝓛`
be the pullback of `𝒪_{ℙⁿ}(1)` to `X` (`AlgebraicGeometry.ProjectiveQuotOverSpace.twistingModule`).
Over a test scheme `T` the base change `X_T` is the algebraic space of `ℙⁿ_T`, and the reading
of `𝓛_T` on the scheme `ℙⁿ_T` is the twisting sheaf `𝒪_{ℙⁿ_T}(1)`.  When `B` is the algebraic
space of a scheme `W`, the reading of `𝓛` itself on `ℙⁿ_W` is `𝒪_{ℙⁿ_W}(1)`.

Both follow from one computation: the module `𝓛₀ = 𝒪(1)` on `h_{ℙⁿ_ℤ}` is the associated module
of the twisting sheaf of `ℙⁿ_ℤ`, so its reading is that sheaf (Stacks 03DX), and the reading
commutes with inverse images along `ℙⁿ_V ⟶ ℙⁿ_ℤ`, which carry the twisting sheaf to the twisting
sheaf.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.readingTwistingModuleBaseIso`: the reading on `ℙⁿ_V`
  of the inverse image of `𝓛₀` along `h_{ℙⁿ_V} ⟶ h_{ℙⁿ_ℤ}` is `𝒪_{ℙⁿ_V}(1)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.readingTwistingModuleIso`: the reading of `𝓛_T` on
  `ℙⁿ_T` is `𝒪_{ℙⁿ_T}(1)`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.baseReadingTwistingModuleIso`: for `B ≅ h_W`, the
  reading of `𝓛` on `ℙⁿ_W` is `𝒪_{ℙⁿ_W}(1)`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The twisting sheaf `𝒪(d)` on `ℙⁿ_V` is quasi-coherent, being invertible. -/
theorem isQuasicoherent_twistingSheaf (V : Scheme.{u}) (d : ℤ) :
    SheafOfModules.IsQuasicoherent (twistingSheaf n V d) :=
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- `𝓛₀ = 𝒪(1)` on `h_{ℙⁿ_ℤ}` is quasi-coherent. -/
theorem isQuasicoherentOnSite_twistingModuleBase :
    (twistingModuleBase B n).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_associatedModule_schemeSpace (projectiveSiteBase B n) _
    (isQuasicoherent_twistingSheaf ((𝒯).obj (siteBase B)) 1)

/-- **The reading of `𝓛₀` on `ℙⁿ_ℤ` is the twisting sheaf** (Stacks 03DX): the inverse of the
unit of the associated-module adjunction at the quasi-coherent twisting sheaf. -/
def zariskiReadingTwistingModuleBaseIso :
    Space.representedZariskiModule B integerBase B.contains_integerBase (projectiveSiteBase B n)
        (twistingModuleBase B n) ≅
      twistingSheaf n ((𝒯).obj (siteBase B)) 1 :=
  haveI := isIso_zariskiAdjunction_unit_app (projectiveSiteBase B n)
    (twistingSheaf n ((𝒯).obj (siteBase B)) 1)
    (isQuasicoherent_twistingSheaf ((𝒯).obj (siteBase B)) 1)
  (asIso ((zariskiAdjunction B (projectiveSiteBase B n)).unit.app
    (twistingSheaf n ((𝒯).obj (siteBase B)) 1))).symm

/-- **The reading on `ℙⁿ_V` of the inverse image of `𝓛₀` along `h_{ℙⁿ_V} ⟶ h_{ℙⁿ_ℤ}` is
`𝒪_{ℙⁿ_V}(1)`**: the reading commutes with that inverse image, and `ℙⁿ_V ⟶ ℙⁿ_ℤ` carries the
twisting sheaf to the twisting sheaf. -/
def readingTwistingModuleBaseIso (V : BigFppfOver B integerBase B.contains_integerBase) :
    Space.representedZariskiModule B integerBase B.contains_integerBase (projectiveSite B n V)
        ((Space.modulePullback B integerBase B.contains_integerBase
          (Space.representedSpaceMap B integerBase B.contains_integerBase
            (projectiveSiteMap B n (toSiteBase B V)))).obj (twistingModuleBase B n)) ≅
      twistingSheaf n ((𝒯).obj V) 1 :=
  (Space.representedZariskiModulePullbackIso B integerBase B.contains_integerBase
      (projectiveSiteMap B n (toSiteBase B V))
      (Space.relativelyRepresentable_yoneda_map B integerBase B.contains_integerBase _)
      (twistingModuleBase B n) isQuasicoherentOnSite_twistingModuleBase).symm ≪≫
    (Scheme.Modules.pullback (projectiveSpaceOverMap n ((𝒯).map (toSiteBase B V)))).mapIso
      zariskiReadingTwistingModuleBaseIso ≪≫
    ProjectiveQuot.twistingSheafPullbackIso (n := n) ((𝒯).map (toSiteBase B V)) 1

variable {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)

/-- **The reading of `𝓛_T` on `ℙⁿ_T` is `𝒪_{ℙⁿ_T}(1)`**, for a test scheme `T` over `B`: the
composite `h_{ℙⁿ_T} ≅ X_T ⟶ X ⟶ ℙⁿ_ℤ` is the morphism represented by `ℙⁿ_T ⟶ ℙⁿ_ℤ`. -/
def readingTwistingModuleIso (T : Space.SchemesOver D.Y) :
    (reading E T).obj ((Space.modulePullback B integerBase B.contains_integerBase
        (D.sourceProjection T)).obj (twistingModule E)) ≅
      twistingSheaf n ((𝒯).obj T.left) 1 :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).mapIso
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n T.left)).inverse.mapIso
      ((Space.modulePullback B integerBase B.contains_integerBase (spaceIso E T).hom).mapIso
          ((Space.modulePullbackTriangle B integerBase B.contains_integerBase
            (rfl : D.sourceProjection T ≫ E.toProjective = _)).app (twistingModuleBase B n)).symm ≪≫
        ((Space.modulePullbackTriangle B integerBase B.contains_integerBase
          (spaceIso_hom_sourceProjection_toProjective E T)).app (twistingModuleBase B n)).symm)) ≪≫
    readingTwistingModuleBaseIso T.left

/-- **The reading of `𝓛` on `ℙⁿ_W` is `𝒪_{ℙⁿ_W}(1)`**, when `B ≅ h_W`: the composite
`h_{ℙⁿ_W} ≅ X ⟶ ℙⁿ_ℤ` is the morphism represented by `ℙⁿ_W ⟶ ℙⁿ_ℤ`. -/
def baseReadingTwistingModuleIso {W : BigFppfOver B integerBase B.contains_integerBase}
    (φ : schemeSpace W ≅ D.Y) :
    (baseReading E φ).obj (twistingModule E) ≅
      Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n ((𝒯).obj W) :=
  (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((𝒯).obj (projectiveSite B n W)) (projectiveSite B n W).left.property).mapIso
    ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
      (projectiveSite B n W)).inverse.mapIso
      ((Space.modulePullbackTriangle B integerBase B.contains_integerBase
          (baseSpaceIso_hom_toProjective E φ)).app (twistingModuleBase B n)).symm) ≪≫
    readingTwistingModuleBaseIso W

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
