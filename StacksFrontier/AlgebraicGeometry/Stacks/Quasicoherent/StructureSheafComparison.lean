module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf

/-!
# The structure sheaf of a fibred category at a named topology and at an arbitrary one

The structure sheaf of Stacks 06TV on an associated site of a category fibred in groupoids is
built twice: once for an arbitrary topology `τ` on the underlying category of schemes which is
coarser than the fppf one, and once for the five topologies the source names — Zariski, étale,
smooth, syntomic and fppf. The second is the first evaluated at `AlgebraicGeometry.SiteKind`,
and this file records that, for the associated topology, for the structure sheaf of the base,
and for the structure sheaf of the fibred category, with its underlying sheaf of rings.

Each identification is an equality on the nose: the two associated topologies are both the
topology inherited along the structure functor from the localization at `S`, and the two
structure presheaves are both the restriction along the structure functor of the presheaf of
global functions, so only the asserted sheaf condition differs and that is a proposition.

## Main results

* `AlgebraicGeometry.FibredSite.associatedTopology_eq_stack`: the associated site of a named
  topology is the associated site of the topology it names.
* `AlgebraicGeometry.FibredSite.structureSheaf_eq_stack` and
  `AlgebraicGeometry.FibredSite.ringStructureSheafCore_eq_stack`: the structure sheaf of the
  fibred category, and its underlying sheaf of rings, agree with the ones for the named
  topology.
* `AlgebraicGeometry.FibredSite.ringStructureSheafCore_etale_eq_stack` and
  `AlgebraicGeometry.FibredSite.ringStructureSheafCore_fppf_eq_stack`: the two instances of the
  previous result at the étale and fppf topologies.

## References

* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The site associated with a fibred category for one of the five named topologies is the site
associated with the topology it names: both are the topology inherited along the structure
functor from the localization at `S`. -/
public theorem associatedTopology_eq_stack (τ : SiteKind) :
    BigFppfOver.associatedTopology B S hS p τ =
      Stack.associatedTopology B S hS p (B.baseTopology τ) :=
  rfl

/-- The structure sheaf of the big site of schemes over `S` for one of the five named
topologies is the one for the topology it names. -/
public theorem baseStructureSheaf_eq_stack (τ : SiteKind) :
    baseStructureSheaf B S hS τ =
      Stack.baseStructureSheaf B S hS (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  rfl

/-- The sheaf of rings of the big site of schemes over `S` for one of the five named
topologies is the one for the topology it names. -/
public theorem baseRingStructureSheaf_eq_stack (τ : SiteKind) :
    baseRingStructureSheaf B S hS τ =
      Stack.baseRingStructureSheaf B S hS (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  rfl

variable (hp : p.IsFiberedInGroupoids)

/-- **Stacks 06TV at a named topology.** The structure sheaf of a category fibred in groupoids
on the site associated with one of the five named topologies is its structure sheaf for the
topology that name denotes. -/
public theorem structureSheaf_eq_stack (τ : SiteKind) :
    structureSheaf B S hS p hp τ =
      Stack.structureSheaf B S hS p hp (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  rfl

/-- **The coefficient sheaf for modules, at a named topology.** The sheaf of rings underlying
the structure sheaf of a category fibred in groupoids on the site associated with one of the
five named topologies is the one for the topology that name denotes. -/
public theorem ringStructureSheafCore_eq_stack (τ : SiteKind) :
    ringStructureSheafCore B S hS p hp τ =
      Stack.ringStructureSheafCore B S hS p hp (B.baseTopology τ)
        (B.baseTopology_le_topology τ) :=
  rfl

/-- The coefficient sheaf for modules on the associated étale site, read for the big étale
topology of the base. -/
public theorem ringStructureSheafCore_etale_eq_stack :
    ringStructureSheafCore B S hS p hp .etale =
      Stack.ringStructureSheafCore B S hS p hp (etaleTopology B)
        (Stack.etaleTopology_le_topology B) :=
  rfl

/-- The coefficient sheaf for modules on the associated fppf site, read for the fppf topology
of the base. -/
public theorem ringStructureSheafCore_fppf_eq_stack :
    ringStructureSheafCore B S hS p hp .fppf =
      Stack.ringStructureSheafCore B S hS p hp B.topology le_rfl :=
  rfl

end AlgebraicGeometry.FibredSite

end
