module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposPullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.SmallModel
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` as a morphism of ringed sites

`AlgebraicGeometry.BigFppfOver.baseToZariskiRingedToposHom` packages the data of the comparison
of Stacks 070U as an `AlgebraicGeometry.RingedToposSiteHom`, which records only continuity of the
underlying functor.  This module supplies the *site* condition and repackages the comparison as
an `AlgebraicGeometry.RingedSite.HomGeneral`, a morphism of ringed sites in the sense of
Stacks 03AD, which is the form that carries a morphism of topoi and the one Stacks 070U is
registered on.

This is the big-site analogue of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral`, and the
argument is the same one.  Two universes are in play and they do not agree: the big `τ`-site of
`S` has objects in `Type (u + 1)` and morphisms in `Type u`, so it is a `RingedSite.{u + 1, u, u}`,
while the small Zariski site is a `RingedSite.{u, u, u}`.  `AlgebraicGeometry.RingedSite.Hom`
asks the objects and morphisms of both sites to share one universe and so cannot hold the
comparison; `AlgebraicGeometry.RingedSite.HomGeneral` asks only that the two sections universes
agree, and they do, both being `u`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseRingedSite`: `((Sch/S)_τ, 𝒪)` as a ringed site.
* `AlgebraicGeometry.BigFppfOver.baseToZariskiRingedSiteHom`: the comparison as a morphism of
  ringed sites at independent object universes.

## Main results

* `AlgebraicGeometry.BigFppfOver.opensToBig_isMorphismOfSites`: the inclusion of the small
  Zariski site of `S` into the big `τ`-site defines a morphism of sites, for sheaves of sets
  valued in the universe of the sections of the structure sheaves.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big `τ`-site of `S` together with its sheaf of global functions, as a ringed site in the
sense of Stacks 03AD.  A reducible abbreviation for the reason recorded on
`AlgebraicGeometry.Scheme.zariskiRingedSite`: the sheaf-of-modules and sheafification instances
are stated for the projections `.C`, `.J` and `.O`. -/
public abbrev baseRingedSite (τ : SiteKind) : RingedSite.{u + 1, u, u} where
  C := BigFppfOver B S hS
  J := baseOverTopology B S hS τ
  O := FibredSite.baseStructureSheaf B S hS τ

/-! ### The site condition at the universe of the structure rings -/

/-- The big `τ`-topology of `S`, transported to a small model of the big fppf category over `S`
at the universe of the structure rings. -/
private abbrev baseSmallModelTopology (τ : SiteKind) :
    GrothendieckTopology (SmallModel.{u} (BigFppfOver B S hS)) :=
  (equivSmallModel.{u} (BigFppfOver B S hS)).inverse.inducedTopology
    (baseOverTopology B S hS τ)

/-- The inclusion of the small Zariski site, followed by the comparison of the big fppf category
over `S` with its small model.  Both sides of this functor are genuinely small at `u`. -/
private abbrev opensToSmallModelBig :
    S.Opens ⥤ SmallModel.{u} (BigFppfOver B S hS) :=
  opensToBig B S hS ⋙ (equivSmallModel.{u} (BigFppfOver B S hS)).functor

private instance isContinuous_opensToSmallModelBig (τ : SiteKind) :
    (opensToSmallModelBig B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (baseSmallModelTopology B S hS τ) :=
  Functor.isContinuous_comp _ _ _ (baseOverTopology B S hS τ) _

/-- The comma categories indexing the right Kan extension along the comparison of the big fppf
category over `S` with its small model have limits of sets in universe `u`, being essentially
small at `u`. -/
private instance hasLimitsOfShape_structuredArrow_base_functor_op
    (W : (SmallModel.{u} (BigFppfOver B S hS))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (BigFppfOver B S hS)).functor.op) (Type u) :=
  have : EssentiallySmall.{u}
      (StructuredArrow W (equivSmallModel.{u} (BigFppfOver B S hS)).functor.op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Restriction of sheaves of sets along the comparison of the big fppf category over `S` with
its small model.  It is an equivalence, the comparison being a dense subsite inclusion. -/
private abbrev baseSmallModelRestrict (τ : SiteKind) :
    Sheaf (baseSmallModelTopology B S hS τ) (Type u) ⥤
      Sheaf (baseOverTopology B S hS τ) (Type u) :=
  (equivSmallModel.{u} (BigFppfOver B S hS)).functor.sheafPushforwardContinuous
    (Type u) (baseOverTopology B S hS τ) (baseSmallModelTopology B S hS τ)

/-- The direct image of the comparison on sheaves of sets valued in the universe of the
structure rings. -/
private abbrev baseDirectImage (τ : SiteKind) :
    Sheaf (baseOverTopology B S hS τ) (Type u) ⥤
      Sheaf (Opens.grothendieckTopology ↥S) (Type u) :=
  (opensToBig B S hS).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ)

/-- The inverse image of the transported inclusion, on the small model. -/
private abbrev baseSmallModelPullback (τ : SiteKind) :
    Sheaf (Opens.grothendieckTopology ↥S) (Type u) ⥤
      Sheaf (baseSmallModelTopology B S hS τ) (Type u) :=
  (opensToSmallModelBig B S hS).sheafPullback (Type u)
    (Opens.grothendieckTopology ↥S) (baseSmallModelTopology B S hS τ)

/-- The direct image of the transported inclusion is the direct image of the comparison,
precomposed with restriction along the comparison with the small model.  This holds by `rfl`,
both sides being the direct image of the same composite functor. -/
private theorem sheafPushforwardContinuous_opensToSmallModelBig (τ : SiteKind) :
    (baseSmallModelRestrict B S hS τ) ⋙ (baseDirectImage B S hS τ) =
      (opensToSmallModelBig B S hS).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ↥S) (baseSmallModelTopology B S hS τ) := rfl

/-- **The inclusion of the small Zariski site of `S` into the big `τ`-site defines a morphism of
sites**, for sheaves of sets valued in the universe `u` of the sections of the structure
sheaves.

This is the input the comparison of Stacks 070U needs to be a morphism of ringed sites.  The
instance `AlgebraicGeometry.BigFppfOver.isContinuous_baseOpensToBig` gives only
continuity, and `CategoryTheory.Functor.preservesFiniteLimits_sheafPullback` (Stacks 00X5) is
unavailable directly, being stated for two sites in a single universe while the big site has its
objects one universe above its morphisms.

The left exact left adjoint of the direct image is the pullback along the transported inclusion
into a small model of the big site at `Type u`, which is left exact by Stacks 00X5 at the
universe of a genuinely small site, conjugated by the restriction equivalence along the
comparison with that small model. -/
public instance opensToBig_isMorphismOfSites (τ : SiteKind) :
    IsMorphismOfSites.{u} (opensToBig B S hS)
      (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ) :=
  have _hP₀ : PreservesFiniteLimits (baseSmallModelPullback B S hS τ) :=
    Functor.preservesFiniteLimits_sheafPullback _ _ _
  have hL : PreservesFiniteLimits
      (baseSmallModelPullback B S hS τ ⋙ baseSmallModelRestrict B S hS τ) :=
    comp_preservesFiniteLimits _ _
  { __ := (inferInstance : (opensToBig B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ))
    hasExactLeftAdjoint :=
      ⟨baseSmallModelPullback B S hS τ ⋙ baseSmallModelRestrict B S hS τ,
        ⟨((((opensToSmallModelBig B S hS).sheafAdjunctionContinuous (Type u)
                (Opens.grothendieckTopology ↥S)
                (baseSmallModelTopology B S hS τ)).ofNatIsoRight
              (eqToIso
                (sheafPushforwardContinuous_opensToSmallModelBig B S hS τ).symm)).comp
            (baseSmallModelRestrict B S hS τ).asEquivalence.toAdjunction).ofNatIsoRight
          ((baseSmallModelRestrict B S hS τ).asEquivalence.invFunIdAssoc
            (baseDirectImage B S hS τ))⟩,
        hL⟩ }

/-! ### The comparison as a morphism of ringed sites -/

/-- **Stacks 070U**: the morphism of ringed sites `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` in the
sense of Stacks 03AD, for each `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, at independent
object universes: the continuous inclusion of the small Zariski site of `S` into the big
`τ`-site, which defines a morphism of sites at the universe of the structure rings, together
with the identification of the sections of `𝒪_S` over an open with the functions on it.

This is the same geometric datum and the same structure map as
`AlgebraicGeometry.BigFppfOver.baseToZariskiRingedToposHom`, which records only continuity;
what is added is the site condition, and with it the morphism of topoi. -/
@[stacks 070U "the morphism of ringed sites of 070R, for each of the five topologies, at \
  independent object universes"]
public def baseToZariskiRingedSiteHom (τ : SiteKind) :
    RingedSite.HomGeneral (baseRingedSite B S hS τ) S.zariskiRingedSite where
  u := opensToBig B S hS
  isMorphismOfSites := opensToBig_isMorphismOfSites B S hS τ
  fsharp := baseCommStructureMap B S hS τ

/-- The underlying functor of `baseToZariskiRingedSiteHom` is `opensToBig`. -/
@[simp]
public theorem baseToZariskiRingedSiteHom_u (τ : SiteKind) :
    (baseToZariskiRingedSiteHom B S hS τ).u = opensToBig B S hS := rfl

/-- The structure map of `baseToZariskiRingedSiteHom` is `baseCommStructureMap`. -/
@[simp]
public theorem baseToZariskiRingedSiteHom_fsharp (τ : SiteKind) :
    (baseToZariskiRingedSiteHom B S hS τ).fsharp = baseCommStructureMap B S hS τ := rfl

/-- **Stacks 00XC for the comparison.**  The morphism of topoi
`Sh((Sch/S)_τ) ⟶ Sh(S_Zar)` underlying it. -/
public abbrev baseToZariskiToposHom (τ : SiteKind) :
    MorphismOfTopoi (Sheaf (baseRingedSite B S hS τ).J (Type u))
      (Sheaf S.zariskiRingedSite.J (Type u)) :=
  (baseToZariskiRingedSiteHom B S hS τ).toposHom

end BigFppfOver

end AlgebraicGeometry

end
