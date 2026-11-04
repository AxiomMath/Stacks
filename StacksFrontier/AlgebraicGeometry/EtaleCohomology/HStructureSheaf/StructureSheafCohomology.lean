module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.AffineHVanishing

/-!
# Cohomology of the structure sheaf in the h topology

Let `p` be a prime number and let `S` be a quasi-compact and quasi-separated scheme over `𝔽_p`.
Stacks 0EWU computes the cohomology of the big h site of `S` with coefficients in `𝒪^h`, the h
sheafification of the structure sheaf:

`H^i((Sch/S)_h, 𝒪^h) = colim_F H^i(S, 𝒪)`,

the colimit being taken over the system `H^i(S, 𝒪) →^F H^i(S, 𝒪) →^F ⋯` induced by the Frobenius
`F : 𝒪_S ⟶ 𝒪_S`, `f ↦ f^p`. This file proves it.

## Main definitions

* `AlgebraicGeometry.BigHOver.hStructureSheaf`: `𝒪^h`, the h sheafification of the abelian
  presheaf `X ↦ Γ(X, 𝒪_X)` on the big h category over `S`.
* `AlgebraicGeometry.BigHOver.hStructureSheafIsoAwnSheafAb`: `𝒪^h ≅ (X ↦ Γ(Xᵃʷⁿ, 𝒪))`
  (Stacks 0EVU).
* `AlgebraicGeometry.BigHOver.hCohomologyIsoColimitFrobenius`: the isomorphism
  `H^i((Sch/S)_h, 𝒪^h) ≅ colim_F H^i(S, 𝒪)` (Stacks 0EWU).

## Conventions

`H^i((Sch/S)_h, -)` is the `i`-th right derived functor of sections over the final object
`S / S` of the big h category over `S`, and `H^i(S, -)` that of sections over `⊤` on the opens of
`S`; both are taken at the universe `u` of the schemes and of the morphisms of the site.
"`S` is a scheme over `𝔽_p`" is `Stacks.Frobenius.IsInCharacteristic S p`.

## References

* [Stacks Project, Tag 0EWU](https://stacks.math.columbia.edu/tag/0EWU)
* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0EVU](https://stacks.math.columbia.edu/tag/0EVU)
* [Stacks Project, Tag 0EVW](https://stacks.math.columbia.edu/tag/0EVW)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.CoarserTopology

universe u

namespace AlgebraicGeometry.BigHOver

-- These global instances leave a stuck universe constraint against `SheafOfModules.{u + 1} _`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The h sheaf `𝒪^h`**: the h sheafification of the abelian presheaf `X ↦ Γ(X, 𝒪_X)` of
global functions on the big h category over `S`. -/
def hStructureSheaf : Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u} :=
  (presheafToSheaf (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj
    (sectionsRingPresheaf B S hS ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- Pullback of global functions to the absolute weak normalization, as a map of abelian
presheaves from `X ↦ Γ(X, 𝒪_X)` to the abelian h sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)`. -/
def toAwnSheafAb :
    sectionsRingPresheaf B S hS ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⟶
      (awnSheafAb B S hS).obj :=
  Functor.whiskerRight (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS))
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- The map `toAwnSheafAb` is locally injective for the h topology. -/
instance isLocallyInjective_toAwnSheafAb :
    Presheaf.IsLocallyInjective (BigHOver.topology B S hS) (toAwnSheafAb B S hS) :=
  (Presheaf.isLocallyInjective_forget_iff _ (toAwnSheafAb B S hS)).1
    ((Presheaf.isLocallyInjective_forget_iff _
      (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS))).2 inferInstance)

/-- The map `toAwnSheafAb` is locally surjective for the h topology. -/
instance isLocallySurjective_toAwnSheafAb :
    Presheaf.IsLocallySurjective (BigHOver.topology B S hS) (toAwnSheafAb B S hS) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget _ (toAwnSheafAb B S hS)).2
    ((Presheaf.isLocallySurjective_iff_whisker_forget _
      (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS))).1 inferInstance)

attribute [local instance] wEqualsLocallyBijective_topology

/-- **`𝒪^h` is `X ↦ Γ(Xᵃʷⁿ, 𝒪)`** (Stacks 0EVU): the isomorphism induced by pullback of functions
to absolute weak normalizations. -/
def hStructureSheafIsoAwnSheafAb : hStructureSheaf B S hS ≅ awnSheafAb B S hS :=
  @asIso _ _ _ _ ((presheafToSheaf (BigHOver.topology B S hS) AddCommGrpCat.{u}).map
      (toAwnSheafAb B S hS))
    (((BigHOver.topology B S hS).W_iff (toAwnSheafAb B S hS)).1
      ((BigHOver.topology B S hS).W_of_isLocallyBijective (toAwnSheafAb B S hS))) ≪≫
    asIso ((sheafificationAdjunction (BigHOver.topology B S hS) AddCommGrpCat.{u}).counit.app
      (awnSheafAb B S hS))

attribute [local instance] Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

/-- Let `p` be a prime number and let `S` be a quasi-compact and quasi-separated scheme over
`𝔽_p`. Then

`H^i((Sch/S)_h, 𝒪^h) ≅ colim_F H^i(S, 𝒪)`

for every `i`, where `𝒪^h` is the h sheafification of the structure sheaf of the big h site of
`S`, and the colimit is over the system `H^i(S, 𝒪) →^F H^i(S, 𝒪) →^F ⋯` induced by the
Frobenius `F : 𝒪_S ⟶ 𝒪_S`, `f ↦ f^p`.

The left-hand side is cohomology over the final object of the big h category over `S`, and the
right-hand side is the colimit of the right derived functors of sections over `S` applied to the
Frobenius system `AlgebraicGeometry.Scheme.abelianFrobeniusSystem`. -/
@[stacks 0EWU]
def hCohomologyIsoColimitFrobenius [CompactSpace S] [QuasiSeparatedSpace S]
    (i : ℕ) :
    (((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj
        (op (BigHOver.final B S hS))).rightDerived i).obj (hStructureSheaf B S hS) ≅
      colimit (S.abelianFrobeniusSystem p hSp ⋙
        ((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
          (op ⊤)).rightDerived i) :=
  have := S.isIso_colimit_post_abelianFrobeniusSystem p hSp i
  (((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj
      (op (BigHOver.final B S hS))).rightDerived i).mapIso (hStructureSheafIsoAwnSheafAb B S hS) ≪≫
    rightDerivedSectionsFinalIsoZariski B S hS (awnSheafAb B S hS)
      (fun V hV q hq ↦ isZero_rightDerived_sheafSections_awnSheafAb B S hS p hSp
        ((opensToBigH B S hS).obj V) hV q hq) i ≪≫
    (((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived
      i).mapIso (IsColimit.coconePointUniqueUpToIso (isColimitZariskiPerfectionCocone B S hS p hSp)
        (colimit.isColimit _)) ≪≫
    (asIso (colimit.post (S.abelianFrobeniusSystem p hSp)
      (((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived i))).symm

end AlgebraicGeometry.BigHOver
