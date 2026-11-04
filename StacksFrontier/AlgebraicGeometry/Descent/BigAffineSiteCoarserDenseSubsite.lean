module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence

/-!
# The affine objects are a dense subsite for all five topologies of a big fppf site

Let `S` be a scheme inside a chosen big fppf site `B`.  The affine objects of `(Sch/S)` form a
dense subsite of `(Sch/S)_fppf`, which is Stacks 021V and is
`AlgebraicGeometry.bigAffineFppfInclusion_isDenseSubsite`.  This file records the same statement
for the four coarser topologies that `B` carries — Zariski, étale, smooth and syntomic — on the
*same* category `AlgebraicGeometry.BigAffineFppf B S hS`, uniformly in the `SiteKind` index.

## Main definitions

* `AlgebraicGeometry.BigAffineFppf.topologyOf`: the topology of `(Aff/S)_τ` as a topology on
  `AlgebraicGeometry.BigAffineFppf B S hS`, for each of the five `τ`.  Its coverings are the
  standard `τ`-coverings of Stacks 020T (3), 021B (3), 021S (2) and their smooth and syntomic
  companions.

## Main results

* `AlgebraicGeometry.BigAffineFppf.inclusion_isDenseSubsite`: **the inclusion of the affine
  objects is a dense subsite inclusion for the `τ`-topology of the affine objects and the
  localized `τ`-topology of `(Sch/S)`, at each of the five `τ`.**
* `AlgebraicGeometry.BigAffineFppf.inclusion_isCocontinuous`: the inclusion is cocontinuous for
  the same pair.
* `AlgebraicGeometry.BigAffineFppf.topologyOf_le_topology`: the `τ`-topology of the affine
  objects is coarser than their fppf topology.

## Implementation notes

There is nothing to construct.  The four coarser big sites that `B` carries, Stacks 03FF, are
`AlgebraicGeometry.BigFppfSite.toBigZariskiSite` and its three companions, and they are built
from `B`'s own cutoff and covering bound *syntactically*: their category of schemes, the slice
of it over `S`, the full subcategory of affine objects in that slice and the inclusion of the
one in the other are therefore the fppf ones on the nose, with no transport.  So the four
dense-subsite statements of
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence` —
`AlgebraicGeometry.BigAffineZariski.inclusion_isSpecialCocontinuous` and its three companions,
which are Stacks 020W, 021E and their smooth and syntomic counterparts — instantiate at
`B.toBigZariskiSite` and so on to give statements about
`AlgebraicGeometry.BigAffineFppf.inclusion B S hS` itself.  The only step is to rewrite the
topology downstairs, from the one the coarser slice carries to the localization at `S` of the
`τ`-topology of Stacks 03FF, and that is
`AlgebraicGeometry.BigFppfSite.bigZariskiOver_topology_toBigZariskiSite` and its three
companions.

This reading is already in use: `AlgebraicGeometry.generate_affineOverPresieve_mem` takes
`(BigAffineEtale.inclusion_isSpecialCocontinuous B.toBigEtaleSite S hS).2` and applies its
cover-density to an object of `AlgebraicGeometry.BigFppfOver B S hS`.

No `@[stacks]` attribute is attached below.  Each statement is an instantiation of a tagged
result at an argument, and the tags 020W, 021E and 021V are registered where those results are
proved; the clause-level registrations that use this file are on Stacks 0GZV, in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteCoarserAssociatedModule`.

## References

* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
* [Stacks Project, Tag 020W](https://stacks.math.columbia.edu/tag/020W)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigAffineFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The topology of the big affine `τ`-site of `S`, carried by the affine objects of the big
fppf category over `S`.

For each of the five `τ` the category is the same — the affine objects over `S` inside the
size-bounded category of schemes `B` chose — and only the covering families differ: they are
the standard `τ`-coverings, the finite families of affines over an affine whose members are
`τ`-morphisms.  The four coarser ones are read off the big `τ`-sites that `B` carries,
Stacks 03FF, whose affine subcategories are this one on the nose. -/
public def topologyOf : SiteKind → GrothendieckTopology (BigAffineFppf B S hS)
  | .zariski => BigAffineZariski.topology B.toBigZariskiSite S hS
  | .etale => BigAffineEtale.topology B.toBigEtaleSite S hS
  | .smooth => BigAffineSmooth.topology B.toBigSmoothSite S hS
  | .syntomic => BigAffineSyntomic.topology B.toBigSyntomicSite S hS
  | .fppf => topology B S hS

/-- At `τ = fppf` the topology of the big affine `τ`-site is the fppf one of Stacks 021S (2). -/
public theorem topologyOf_fppf : topologyOf B S hS .fppf = topology B S hS := rfl

/-- **The inclusion of the affine objects is cocontinuous for the `τ`-topologies**, at each of
the five `τ`: a covering sieve of an affine object is refined by a standard `τ`-covering with
affine sources. -/
public instance inclusion_isCocontinuous (τ : SiteKind) :
    (inclusion B S hS).IsCocontinuous (topologyOf B S hS τ)
      (BigFppfOver.baseOverTopology B S hS τ) := by
  cases τ with
  | zariski =>
      have h := (BigAffineZariski.inclusion_isSpecialCocontinuous B.toBigZariskiSite S hS).1
      rwa [B.bigZariskiOver_topology_toBigZariskiSite S hS] at h
  | etale =>
      have h := (BigAffineEtale.inclusion_isSpecialCocontinuous B.toBigEtaleSite S hS).1
      rwa [B.bigEtaleOver_topology_toBigEtaleSite S hS] at h
  | smooth =>
      have h := (BigAffineSmooth.inclusion_isSpecialCocontinuous B.toBigSmoothSite S hS).1
      rwa [B.bigSmoothOver_topology_toBigSmoothSite S hS] at h
  | syntomic =>
      have h := (BigAffineSyntomic.inclusion_isSpecialCocontinuous B.toBigSyntomicSite S hS).1
      rwa [B.bigSyntomicOver_topology_toBigSyntomicSite S hS] at h
  | fppf => exact bigAffineFppfInclusion_isCocontinuous B S hS

/-- **Stacks 021V and its three companions, for the five topologies a big fppf site carries.**
The inclusion of the affine objects of `(Sch/S)` into `(Sch/S)` exhibits `(Aff/S)_τ` as a dense
subsite of `(Sch/S)_τ`, for each `τ ∈ {Zariski, étale, smooth, syntomic, fppf}` — all five on
one and the same pair of categories. -/
public instance inclusion_isDenseSubsite (τ : SiteKind) :
    (inclusion B S hS).IsDenseSubsite (topologyOf B S hS τ)
      (BigFppfOver.baseOverTopology B S hS τ) := by
  cases τ with
  | zariski =>
      have h := (BigAffineZariski.inclusion_isSpecialCocontinuous B.toBigZariskiSite S hS).2
      rwa [B.bigZariskiOver_topology_toBigZariskiSite S hS] at h
  | etale =>
      have h := (BigAffineEtale.inclusion_isSpecialCocontinuous B.toBigEtaleSite S hS).2
      rwa [B.bigEtaleOver_topology_toBigEtaleSite S hS] at h
  | smooth =>
      have h := (BigAffineSmooth.inclusion_isSpecialCocontinuous B.toBigSmoothSite S hS).2
      rwa [B.bigSmoothOver_topology_toBigSmoothSite S hS] at h
  | syntomic =>
      have h := (BigAffineSyntomic.inclusion_isSpecialCocontinuous B.toBigSyntomicSite S hS).2
      rwa [B.bigSyntomicOver_topology_toBigSyntomicSite S hS] at h
  | fppf => exact bigAffineFppfInclusion_isDenseSubsite B S hS

/-- The `τ`-topology of the affine objects is coarser than their fppf topology.  Both are read
off the topology downstairs by the dense-subsite biconditional, and downstairs the localized
`τ`-topology is coarser than the localized fppf topology. -/
public theorem topologyOf_le_topology (τ : SiteKind) :
    topologyOf B S hS τ ≤ topology B S hS := by
  intro X R hR
  rw [← Functor.IsDenseSubsite.functorPushforward_mem_iff (J := topology B S hS)
    (K := BigFppfOver.topology B S hS) (G := inclusion B S hS)]
  exact BigFppfOver.baseOverTopology_le_fppf B S hS τ _
    (Functor.IsDenseSubsite.functorPushforward_mem_iff.2 hR)

end BigAffineFppf

end AlgebraicGeometry

end
