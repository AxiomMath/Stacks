module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigFppf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigSmooth
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigSyntomic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.BigZariski
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamilyLocality

/-!
# Enough points for the site associated to a category fibred in groupoids (Stacks 06W4)

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids over the big fppf category of a
scheme `S` of a big fppf site `B`. Stacks 06W4 says that the associated site `𝒳_τ` has enough
points for each of the five standard topologies `τ ∈ {Zar, étale, smooth, syntomic, fppf}`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Stack.hasConservativeFamily_siteKind`: **Stacks 06W4**. For every
  `τ : AlgebraicGeometry.SiteKind` — Zariski, étale, smooth, syntomic or fppf — the site
  `𝒳_τ` has a conservative family of points.
* `AlgebraicGeometry.Stack.hasConservativeFamily_associatedTopology`: the argument of the
  source, for an arbitrary topology on the underlying category of schemes whose localizations
  have enough points.
* `AlgebraicGeometry.BigFppfSite.baseTopology_over_hasConservativeFamily`: Stacks 06VX for the
  five big sites carried by `B`, at every object of the common category of schemes.
* `AlgebraicGeometry.BigFppfSite.toBigZariskiSite_grothendieckTopology`,
  `.toBigEtaleSite_topology`, `.toBigSmoothSite_grothendieckTopology` and
  `.toBigSyntomicSite_topology`: the topologies of the big Zariski, étale, smooth and syntomic
  sites carried by a big fppf site are the four coarser topologies of Stacks 03FF, and
  `AlgebraicGeometry.BigFppfSite.bigZariskiOver_topology_toBigZariskiSite` and its three
  companions say the same of their slices over a scheme.

## Implementation notes

**The proof.** By Stacks 06UL having a conservative family of points is local, and every object
of `𝒳` is a member of a family covering the final object, so it is enough to produce a
conservative family on each localization `𝒳_τ/x`. Stacks 06W0 identifies that localization with
the localization of the base at the scheme `x` lies over — and identifies it through the
canonical functor, which is what lets the conservative family be transported along the
equivalence by `CategoryTheory.GrothendieckTopology.HasConservativeFamily.of_inducedTopology`.
The localizations of the base have enough points by Stacks 06VX, which is
`AlgebraicGeometry.bigZariski_hasConservativeFamily`,
`AlgebraicGeometry.bigEtale_hasConservativeFamily`,
`AlgebraicGeometry.bigSmooth_hasConservativeFamily`,
`AlgebraicGeometry.bigSyntomic_hasConservativeFamily` and
`AlgebraicGeometry.bigFppf_hasConservativeFamily` for the five big sites.

**Universes.** Points take values in `Type (u+1)`, as they do in every instance of Stacks 06VX
in this library. `𝒳` is an arbitrary category whose morphisms form `(u+1)`-small types, which
is how the convention of the source that the morphisms of a category form a set (Stacks 0014)
is rendered relative to the universe of the site of schemes; it holds in particular whenever
`𝒳` is a category in `Type u` or in `Type (u+1)`.

**The coarser sites.** The big Zariski, étale, smooth and syntomic sites carried by a big fppf
site (Stacks 03FF) have, by construction, the same underlying category as the fppf one, so the
topology identifications below are equalities of Grothendieck topologies on one and the same
category and need no transport: only the chosen covering families have to be compared, which is
`AlgebraicGeometry.BigFppfSite.toBigEtaleSite_isCovering_iff` and its three companions.

## References

* [Stacks Project, Tag 06W4](https://stacks.math.columbia.edu/tag/06W4)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06UL](https://stacks.math.columbia.edu/tag/06UL)
* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

namespace BigFppfSite

variable (B : BigFppfSite.{u})

/-- The topology of the big étale site carried by a big fppf site is the big étale topology of
Stacks 03FF: the two have the same underlying category and the same chosen covering
families. -/
theorem toBigEtaleSite_topology : B.toBigEtaleSite.topology = B.etaleTopology := by
  have hpre : B.toBigEtaleSite.precoverage = B.etalePrecoverage := by
    ext X R
    constructor
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, rfl, (B.toBigEtaleSite_isCovering_iff ⟨X, E⟩).mp hE⟩
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, rfl, (B.toBigEtaleSite_isCovering_iff ⟨X, E⟩).mpr hE⟩
  rw [BigEtaleSite.topology, hpre]
  rfl

/-- The topology of the big smooth site carried by a big fppf site is the big smooth topology of
Stacks 03FF: the two have the same underlying category and the same chosen covering
families. -/
theorem toBigSmoothSite_grothendieckTopology :
    B.toBigSmoothSite.grothendieckTopology = B.smoothTopology := by
  have hpre : B.toBigSmoothSite.precoverage = B.smoothPrecoverage := by
    ext X R
    constructor
    · rintro ⟨E, hE, rfl⟩
      exact ⟨E, rfl, (B.toBigSmoothSite_isCovering_iff ⟨X, E⟩).mp hE⟩
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, (B.toBigSmoothSite_isCovering_iff ⟨X, E⟩).mpr hE, rfl⟩
  rw [BigSmoothSite.grothendieckTopology, hpre]
  rfl

/-- The topology of the big Zariski site carried by a big fppf site is the big Zariski topology
of Stacks 03FF: the two have the same underlying category and the same chosen covering
families. -/
theorem toBigZariskiSite_grothendieckTopology :
    B.toBigZariskiSite.grothendieckTopology = B.zariskiTopology := by
  have hpre : B.toBigZariskiSite.precoverage = B.zariskiPrecoverage := by
    ext X R
    constructor
    · rintro ⟨E, hE, rfl⟩
      exact ⟨E, rfl, (B.toBigZariskiSite_isCovering_iff ⟨X, E⟩).mp hE⟩
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, (B.toBigZariskiSite_isCovering_iff ⟨X, E⟩).mpr hE, rfl⟩
  rw [BigZariskiSite.grothendieckTopology, hpre]
  rfl

/-- The topology of the big syntomic site carried by a big fppf site is the big syntomic
topology of Stacks 03FF: the two have the same underlying category and the same chosen covering
families. -/
theorem toBigSyntomicSite_topology : B.toBigSyntomicSite.topology = B.syntomicTopology := by
  have hpre : B.toBigSyntomicSite.precoverage = B.syntomicPrecoverage := by
    ext X R
    constructor
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, rfl, (B.toBigSyntomicSite_isCovering_iff ⟨X, E⟩).mp hE⟩
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, rfl, (B.toBigSyntomicSite_isCovering_iff ⟨X, E⟩).mpr hE⟩
  rw [BigSyntomicSite.topology, hpre]
  rfl

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The topology of the big Zariski category over `S` carried by a big fppf site is the
localization at `S` of the big Zariski topology of Stacks 03FF. -/
theorem bigZariskiOver_topology_toBigZariskiSite :
    BigZariskiOver.topology B.toBigZariskiSite S hS = B.zariskiTopology.over (B.obj hS) := by
  rw [← B.toBigZariskiSite_grothendieckTopology]
  exact bigZariskiOver_topology_eq B.toBigZariskiSite ⟨S, hS⟩

/-- The topology of the big étale category over `S` carried by a big fppf site is the
localization at `S` of the big étale topology of Stacks 03FF. -/
theorem bigEtaleOver_topology_toBigEtaleSite :
    BigEtaleOver.topology B.toBigEtaleSite S hS = B.etaleTopology.over (B.obj hS) := by
  rw [← B.toBigEtaleSite_topology]
  exact bigEtaleOver_topology_eq B.toBigEtaleSite S hS

/-- The topology of the big smooth category over `S` carried by a big fppf site is the
localization at `S` of the big smooth topology of Stacks 03FF. -/
theorem bigSmoothOver_topology_toBigSmoothSite :
    BigSmoothOver.topology B.toBigSmoothSite S hS = B.smoothTopology.over (B.obj hS) := by
  rw [← B.toBigSmoothSite_grothendieckTopology]
  rfl

/-- The topology of the big syntomic category over `S` carried by a big fppf site is the
localization at `S` of the big syntomic topology of Stacks 03FF. -/
theorem bigSyntomicOver_topology_toBigSyntomicSite :
    BigSyntomicOver.topology B.toBigSyntomicSite S hS =
      B.syntomicTopology.over (B.obj hS) := by
  rw [← B.toBigSyntomicSite_topology]
  rfl

/-- **Stacks 06VX for the five big sites, on the common category of schemes.** For each of the
five topologies `τ`, the localization of the big site `(Sch)_τ` carried by `B` at any of its
objects has a conservative family of points. -/
theorem baseTopology_over_hasConservativeFamily (τ : SiteKind) (T : B.Schemes) :
    ((B.baseTopology τ).over T).HasConservativeFamily.{u + 1} := by
  cases τ with
  | zariski =>
      exact (B.bigZariskiOver_topology_toBigZariskiSite T.1 T.2) ▸
        bigZariski_hasConservativeFamily B.toBigZariskiSite T.1 T.2
  | etale =>
      exact (B.bigEtaleOver_topology_toBigEtaleSite T.1 T.2) ▸
        bigEtale_hasConservativeFamily B.toBigEtaleSite T.1 T.2
  | smooth =>
      exact (B.bigSmoothOver_topology_toBigSmoothSite T.1 T.2) ▸
        bigSmooth_hasConservativeFamily B.toBigSmoothSite T.1 T.2
  | syntomic =>
      exact (B.bigSyntomicOver_topology_toBigSyntomicSite T.1 T.2) ▸
        bigSyntomic_hasConservativeFamily B.toBigSyntomicSite T.1 T.2
  | fppf => exact bigFppf_hasConservativeFamily B T.1 T.2

end BigFppfSite

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] [LocallySmall.{u + 1} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The argument of Stacks 06W4, for an arbitrary topology on the underlying category of
schemes. If every localization of `τ` has a conservative family of points, then so does the site
that a category fibred in groupoids over the big fppf category of `S` inherits from the
localization of `τ` at `S`.

Having a conservative family of points is local on the site (Stacks 06UL) and the objects of
`𝒳` cover its final object, so it suffices to produce one on each localization `𝒳_τ/x`; Stacks
06W0 identifies that site with the localization of `τ` at the scheme `x` lies over, through the
canonical localization functor, along which the family transports. -/
theorem hasConservativeFamily_associatedTopology (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes)
    (hτ : ∀ T : B.Schemes, (τ.over T).HasConservativeFamily.{u + 1}) :
    (associatedTopology B S hS p τ).HasConservativeFamily.{u + 1} := by
  have hlocal : ∀ x : 𝒳,
      ((associatedTopology B S hS p τ).over x).HasConservativeFamily.{u + 1} := by
    intro x
    have : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp x
    rw [← inducedTopology_overPost B S hS p hp τ x]
    exact GrothendieckTopology.HasConservativeFamily.of_inducedTopology
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))) _ (hτ _)
  refine GrothendieckTopology.HasConservativeFamily.of_coversTop (fun x : 𝒳 ↦ x)
    (fun x ↦ ?_) hlocal
  exact (associatedTopology B S hS p τ).superset_covering (S := ⊤)
    (fun y _ _ ↦ ⟨y, ⟨𝟙 y⟩⟩) ((associatedTopology B S hS p τ).top_mem x)

/-- **Stacks 06W4.** Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and let
`τ ∈ {Zar, étale, smooth, syntomic, fppf}`. Then the site `𝒳_τ` has enough points: it has a
conservative family of points.

The site `𝒳_τ` is `AlgebraicGeometry.BigFppfOver.associatedTopology`, the topology `𝒳`
inherits along `p` from the localization at `S` of the big `τ` topology (Stacks 06TP). The
proof is the one of the source: `hasConservativeFamily_associatedTopology` reduces to the
localizations of the big site, which have enough points by Stacks 06VX. -/
@[stacks 06W4]
theorem hasConservativeFamily_siteKind (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).HasConservativeFamily.{u + 1} :=
  hasConservativeFamily_associatedTopology B S hS p hp (B.baseTopology τ)
    (B.baseTopology_over_hasConservativeFamily τ)

end Stack

end AlgebraicGeometry

end
