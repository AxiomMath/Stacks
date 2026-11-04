module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksCore.Tactic.StacksAttribute

/-!
# Inverse images of a quasi-coherent module from the small étale site

Let `S` be a scheme contained in a chosen big fppf site `B` and let `𝓕` be a quasi-coherent
`𝒪_S`-module.  On the one category `(Sch/S) = BigFppfOver B S hS` carrying the five localized
topologies of `AlgebraicGeometry.SiteKind` the inclusion of the small étale site of `S` is
continuous for the étale topology and for every finer one, so it is the underlying functor of
both comparison morphisms of ringed sites

* `π_S : ((Sch/S)_étale, 𝒪) ⟶ (S_étale, 𝒪)` and
* `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)`,

whose structure-sheaf comparisons are the identity.  Their inverse images on sheaves of modules
are the left adjoints of the direct images of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPushforward`,
and clauses (2) and (3) of Stacks 0DEW identify `𝓕ᵃ` on the big site with the inverse image of
`𝓕ᵃ` on `S_étale` along them.

The source proves both by composing pullbacks: `𝓕ᵃ` on `(Sch/S)_τ` is the inverse image of `𝓕`
along `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, that morphism of ringed sites factors through
`(S_étale, 𝒪)`, and `𝓕ᵃ` on `S_étale` is the inverse image of `𝓕` along the second factor.  Both
factorizations are read here off uniqueness of left adjoints, the direct image along the
composite being the composite of the direct images; the identification of each inverse image with
the sections description `(f : T → S) ↦ Γ(T, f⁺𝓕)` is Stacks 070S, part (1) on the big site and
part (2) on `S_étale`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseStructureMap`: the structure-sheaf comparison of
  `π_S` resp. `a_S`, the identity.
* `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforward` and
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModulePullback`: the direct and inverse images
  of sheaves of modules along it, with
  `AlgebraicGeometry.BigFppfOver.smallEtaleToBaseModuleAdjunction`.
* `AlgebraicGeometry.BigFppfOver.smallEtaleToBasePushforwardCompIso`: the direct image along
  `(Sch/S)_τ ⟶ S_Zar` is the direct image to `S_étale` followed by restriction to the small
  Zariski site.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`: the resulting
  factorization of the associated-module functor of `(Sch/S)_τ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedModuleIsoSheaf` and
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoBaseAssociatedSheaf`: the
  associated-module functors of `S_étale` and of `(Sch/S)_τ` are the pullback-sections sheaf of
  Stacks 03DS, by Stacks 070S (2) resp. 070S (1).
* `AlgebraicGeometry.BigFppfOver.baseAssociatedSheafIsoSmallEtalePullback`: `𝓕ᵃ` on `(Sch/S)_τ`
  is the inverse image along `(Sch/S)_τ ⟶ S_étale` of `𝓕ᵃ` on `S_étale`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedSheafIsoPiPullback`: **Stacks 0DEW, clause (2)** —
  `𝓕ᵃ = π_S^*𝓕` on `(Sch/S)_étale`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedSheafIsoAPullback`: **Stacks 0DEW, clause (3)** —
  `𝓕ᵃ = a_S^*𝓕` on `(Sch/S)_fppf`.

## Implementation notes

**What `𝓕` on `S_étale` is.**  As in the pushforward file, the source's quasi-coherent module on
`S_étale` is replaced by the associated module of a quasi-coherent module on the scheme `S`,
which is legitimate by Descent, Proposition 03DX and is the first step of the source's own proof.
So the `𝓕` of clauses (2) and (3) is `AlgebraicGeometry.BigFppfOver.smallEtaleAssociatedSheaf`,
exactly as in clauses (6) and (7).

**Why the identification is not a reflexivity.**  The two sides are different constructions: the
left is the left adjoint of restriction of sections, obtained by pulling back presheaves of
modules and sheafifying, and the right is the sections presheaf itself.  The isomorphism between
them is the local bijectivity of the comparison of Stacks 070S on each of the two sites, and
neither half of it is definitional.

**The restated instances.**  `BigEtaleOver B.toBigEtaleSite S hS` and `BigFppfOver B S hS` are
the same category, but `AlgebraicGeometry.BigFppfSite.toBigEtaleSite` is a definition which
instance search does not unfold, so `essentiallySmall_smallEtaleOfBigFppf` and
`isContinuous_opensToSmallEtaleOfBigFppf` restate library instances in the fppf presentation, as
the three instances of the pushforward file do.  Essential smallness of the small étale site is
what makes the inverse image of sheaves of modules along `π_S` and `a_S` exist, by Stacks 03D6
part (2).

**The small Zariski site inside the big site.**  The inclusion of the small Zariski site of `S`
into the small étale site followed by the inclusion of the small étale site into the big site is
the inclusion of the small Zariski site into the big site, and the composite of the two
structure-sheaf comparisons is the structure-sheaf comparison of the big site: both hold by
`rfl`, which is what lets `CategoryTheory.SheafOfModules.pushforwardComp` and
`CategoryTheory.SheafOfModules.pushforwardCongr` be used directly.

## References

* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The small étale site in the fppf presentation -/

/-- The small étale site of `S` is essentially small, restated for the big étale site carried by
`B` so that instance search sees the size hypothesis in the form `B.Contains S`. -/
public instance essentiallySmall_smallEtaleOfBigFppf :
    EssentiallySmall.{u} (SmallEtale B.toBigEtaleSite S hS) :=
  SmallEtale.essentiallySmall B.toBigEtaleSite S hS

/-- The small Zariski site of `S` is continuous into the small étale site of `S`, restated for
the big étale site carried by `B`. -/
public instance isContinuous_opensToSmallEtaleOfBigFppf :
    (SmallEtale.opensToSmallEtale B.toBigEtaleSite S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (SmallEtale.topology B.toBigEtaleSite S hS) :=
  SmallEtale.isContinuous_opensToSmallEtale B.toBigEtaleSite S hS

/-- The inclusion of the small étale site of `S` into the big étale site of `S` is continuous for
the étale member of the five localized topologies: Stacks 021G makes it continuous into the
localized big étale topology, which that member refines. -/
public instance isContinuous_smallEtaleInclusion_etale :
    (smallEtaleToFppf B S hS).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS) (baseOverTopology B S hS .etale) :=
  have _h0 : (smallEtaleToFppf B S hS).IsContinuous
      (SmallEtale.topology B.toBigEtaleSite S hS)
      (BigEtaleOver.topology B.toBigEtaleSite S hS) :=
    (smallEtaleInclusion_isMorphismOfSites B.toBigEtaleSite S hS).toIsContinuous
  Functor.isContinuous_of_le_target _ _ (bigEtaleOver_topology_le_baseOverTopology B S hS)

/-! ### The comparison morphisms of ringed sites -/

variable (τ : SiteKind)
  [(smallEtaleToFppf B S hS).IsContinuous (SmallEtale.topology B.toBigEtaleSite S hS)
    (baseOverTopology B S hS τ)]

/-- The structure-sheaf comparison of the morphism of ringed sites
`((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)` given by the inclusion of the small étale site: the identity,
the structure sheaf of the small étale site being the restriction of that of the big site.  At
`τ = étale` this is `π_S` and at `τ = fppf` it is `a_S`. -/
public def smallEtaleToBaseStructureMap :
    SmallEtale.structureSheaf B.toBigEtaleSite S hS ⟶
      ((smallEtaleToFppf B S hS).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B.toBigEtaleSite S hS) (baseOverTopology B S hS τ)).obj
          (FibredSite.baseRingStructureSheaf B S hS τ) :=
  𝟙 _

/-- At `τ = fppf` the structure-sheaf comparison is the one of `a_S`. -/
public theorem smallEtaleToBaseStructureMap_fppf :
    smallEtaleToBaseStructureMap B S hS .fppf = aStructureMap B S hS :=
  rfl

/-- The direct image of sheaves of modules along `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)`: restriction of
sections along the inclusion of the small étale site. -/
public abbrev smallEtaleToBasePushforward :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS) :=
  SheafOfModules.pushforward.{u} (smallEtaleToBaseStructureMap B S hS τ)

/-- The inverse image of sheaves of modules along `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)`, the left
adjoint of the direct image.  At `τ = étale` this is `π_S^*` and at `τ = fppf` it is `a_S^*`. -/
public abbrev smallEtaleToBaseModulePullback :
    SheafOfModules.{u} (SmallEtale.structureSheaf B.toBigEtaleSite S hS) ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  SheafOfModules.pullback.{u} (smallEtaleToBaseStructureMap B S hS τ)

/-- The inverse image along `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)` is left adjoint to the direct
image. -/
public def smallEtaleToBaseModuleAdjunction :
    smallEtaleToBaseModulePullback B S hS τ ⊣ smallEtaleToBasePushforward B S hS τ :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleToBaseStructureMap B S hS τ)

/-! ### The factorization through the small étale site -/

/-- The inclusion of the small Zariski site of `S` into the small étale site of `S` followed by
the inclusion of the small étale site into the big site is continuous. -/
public instance isContinuous_opensToSmallEtale_comp_smallEtaleToFppf :
    (SmallEtale.opensToSmallEtale B.toBigEtaleSite S hS ⋙ smallEtaleToFppf B S hS).IsContinuous
      (Opens.grothendieckTopology ↥S) (baseOverTopology B S hS τ) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B.toBigEtaleSite S hS) _

/-- The structure-sheaf comparison of `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the one of
`(S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` followed by the direct image of the one of
`((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)`: all three are the identification of the sections of `𝒪_S` over
an open with the global functions of that open subscheme. -/
public theorem smallEtaleToBaseStructureMap_comp_eq :
    SmallEtale.structureMap B.toBigEtaleSite S hS ≫
        ((SmallEtale.opensToSmallEtale B.toBigEtaleSite S hS).sheafPushforwardContinuous
          RingCat.{u} (Opens.grothendieckTopology ↥S)
            (SmallEtale.topology B.toBigEtaleSite S hS)).map
              (smallEtaleToBaseStructureMap B S hS τ) =
      baseStructureMap B S hS τ :=
  rfl

/-- The direct image of sheaves of modules along `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the direct
image to `S_étale` followed by restriction along the inclusion of the small Zariski site. -/
public def smallEtaleToBasePushforwardCompIso :
    smallEtaleToBasePushforward B S hS τ ⋙ SmallEtale.restrictModule B.toBigEtaleSite S hS ≅
      baseRestrictModule B S hS τ :=
  SheafOfModules.pushforwardComp.{u} (SmallEtale.structureMap B.toBigEtaleSite S hS)
      (smallEtaleToBaseStructureMap B S hS τ) ≪≫
    SheafOfModules.pushforwardCongr.{u} (smallEtaleToBaseStructureMap_comp_eq B S hS τ)

/-- **The associated-module functor of `(Sch/S)_τ` factors through the small étale site**: the
inverse image along `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the associated-module functor of
`S_étale` followed by the inverse image along `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)`.  Both are left
adjoint to the direct image along the composite. -/
public def baseAssociatedModuleIsoSmallEtalePullback :
    SmallEtale.associatedModule B.toBigEtaleSite S hS ⋙ smallEtaleToBaseModulePullback B S hS τ ≅
      baseAssociatedModule B S hS τ :=
  Adjunction.leftAdjointUniq
    (((SmallEtale.associatedModuleAdjunction B.toBigEtaleSite S hS).comp
        (smallEtaleToBaseModuleAdjunction B S hS τ)).ofNatIsoRight
      (smallEtaleToBasePushforwardCompIso B S hS τ))
    (baseAssociatedModuleAdjunction B S hS τ)

/-! ### The two sections descriptions -/

variable (F : S.Modules) [F.IsQuasicoherent]

/-- **Stacks 070S (2) in the form clauses (2) and (3) consume.**  The associated module on
`S_étale` of a quasi-coherent module on the scheme `S` is the pullback-sections sheaf
`(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS there: the associated module is the sheafification of
the presheaf-level pullback, the comparison of Stacks 070S (2) sheafifies to an isomorphism, and
the sections presheaf is already a sheaf. -/
public def smallEtaleAssociatedModuleIsoSheaf :
    (SmallEtale.associatedModule B.toBigEtaleSite S hS).obj F ≅
      smallEtaleAssociatedSheaf B S hS F :=
  (SmallEtale.associatedModuleSheafificationIso B.toBigEtaleSite S hS).app F ≪≫
    @asIso _ _ _ _ _
        (SmallEtale.isIso_sheafification_map_sectionsComparison B.toBigEtaleSite S hS F) ≪≫
      (asIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf B.toBigEtaleSite S hS).obj)).counit)).app
          (smallEtaleAssociatedSheaf B S hS F)

/-- **Stacks 070S (1) in the form clauses (2) and (3) consume.**  The associated module on
`(Sch/S)_τ` of a quasi-coherent module on the scheme `S` is the pullback-sections sheaf
`(f : T → S) ↦ Γ(T, f⁺𝓕)` of Stacks 03DS, which is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf`. -/
public def baseAssociatedModuleIsoBaseAssociatedSheaf :
    (baseAssociatedModule B S hS τ).obj F ≅ baseAssociatedSheaf B S hS F τ :=
  baseAssociatedModuleIsoSectionsSheaf B S hS τ F

/-! ### Clauses (2) and (3) of Stacks 0DEW -/

/-- **`𝓕ᵃ` on `(Sch/S)_τ` is the inverse image of `𝓕ᵃ` on `S_étale`** along the morphism of
ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_étale, 𝒪)` given by the inclusion of the small étale site.

Both sides are read as the pullback-sections sheaf of Stacks 03DS by Stacks 070S, and the two
inverse images are identified by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSmallEtalePullback`. -/
public def baseAssociatedSheafIsoSmallEtalePullback :
    (smallEtaleToBaseModulePullback B S hS τ).obj (smallEtaleAssociatedSheaf B S hS F) ≅
      baseAssociatedSheaf B S hS F τ :=
  (smallEtaleToBaseModulePullback B S hS τ).mapIso
      (smallEtaleAssociatedModuleIsoSheaf B S hS F).symm ≪≫
    (baseAssociatedModuleIsoSmallEtalePullback B S hS τ).app F ≪≫
      baseAssociatedModuleIsoBaseAssociatedSheaf B S hS τ F

/-- **Stacks 0DEW, clause (2).**  On `(Sch/S)_étale` the associated module `𝓕ᵃ` of a
quasi-coherent module is the inverse image `π_S^*𝓕` of its associated module on `S_étale`, along
the morphism of ringed sites `π_S : ((Sch/S)_étale, 𝒪) ⟶ (S_étale, 𝒪)`. -/
@[stacks 0DEW "clause (2) only: 𝓕ᵃ = π_S^*𝓕 on (Sch/S)_étale, with 𝓕 on S_étale the associated \
module of a quasi-coherent module on the scheme S as in the source's first reduction"]
public def baseAssociatedSheafIsoPiPullback :
    (smallEtaleToBaseModulePullback B S hS .etale).obj (smallEtaleAssociatedSheaf B S hS F) ≅
      baseAssociatedSheaf B S hS F .etale :=
  baseAssociatedSheafIsoSmallEtalePullback B S hS .etale F

/-- **Stacks 0DEW, clause (3).**  On `(Sch/S)_fppf` the associated module `𝓕ᵃ` of a
quasi-coherent module is the inverse image `a_S^*𝓕` of its associated module on `S_étale`, along
the morphism of ringed sites `a_S : ((Sch/S)_fppf, 𝒪) ⟶ (S_étale, 𝒪)`. -/
@[stacks 0DEW "clause (3) only: 𝓕ᵃ = a_S^*𝓕 on (Sch/S)_fppf, with 𝓕 on S_étale the associated \
module of a quasi-coherent module on the scheme S as in the source's first reduction"]
public def baseAssociatedSheafIsoAPullback :
    (SheafOfModules.pullback.{u} (aStructureMap B S hS)).obj
        (smallEtaleAssociatedSheaf B S hS F) ≅
      baseAssociatedSheaf B S hS F .fppf :=
  baseAssociatedSheafIsoSmallEtalePullback B S hS .fppf F

end AlgebraicGeometry.BigFppfOver

end
