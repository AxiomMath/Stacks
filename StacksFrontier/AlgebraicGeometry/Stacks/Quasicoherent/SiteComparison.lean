module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe

/-!
# Comparing quasi-coherence on the five sites of a category fibred in groupoids

Stacks 0EM8 asserts, for a presheaf of modules `𝓕` on a category `𝒳` fibred in groupoids over
the big fppf category of schemes over `S`, that the three conditions

1. `𝓕 ∈ Mod(𝒳_Zar, 𝒪_𝒳)` and `𝓕` is quasi-coherent on `(𝒳_Zar, 𝒪_𝒳)` in the sense of
   Stacks 03DL,
2. `𝓕 ∈ Mod(𝒳_ét, 𝒪_𝒳)` and `𝓕` is quasi-coherent on `(𝒳_ét, 𝒪_𝒳)` in the sense of
   Stacks 03DL,
3. `𝓕` is a quasi-coherent module on `𝒳` in the sense of Stacks 06WG, that is, for the
   inherited fppf topology,

are equivalent.  For a module sheaf that is already a sheaf for the inherited fppf topology,
quasi-coherence for any of the four topologies coarser than the fppf one implies quasi-coherence
for the fppf one; in particular `(1) ⟹ (3)` and `(2) ⟹ (3)` hold for such a module.

## Main definitions

* `AlgebraicGeometry.FibredSite.quasicoherentOfSiteRestriction`: such a module, as an object of
  the category `AlgebraicGeometry.FibredSite.quasicoherentModules` of Stacks 06WG.

## Main results

* `AlgebraicGeometry.FibredSite.ringOfLe_ringStructureSheafCore`: the coefficient sheaf of
  rings of a coarser associated site is the one of the inherited fppf site, read for the
  coarser topology.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_of_siteRestriction`: a sheaf of modules
  on the inherited fppf site whose reading for a coarser associated topology is quasi-coherent
  in the sense of Stacks 03DL(6) is quasi-coherent on the inherited fppf site.
* `AlgebraicGeometry.FibredSite.siteRestriction_eq_comparisonPushforward`:
  `AlgebraicGeometry.FibredSite.siteRestriction` is the functor
  `Stacks.SheafOfModules.comparisonPushforward` for the inclusion of a coarser associated
  topology.

## References

* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : SiteKind)

/-- The coefficient sheaf of rings of a coarser associated site is the coefficient sheaf of
rings of the inherited fppf site, read for the coarser topology. -/
public theorem ringOfLe_ringStructureSheafCore :
    Stacks.SheafOfModules.ringOfLe
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf) =
      ringStructureSheafCore B S hS p hp τ := rfl

/-- A sheaf of modules on the inherited fppf site of a
category fibred in groupoids whose reading for one of the four coarser associated topologies
is quasi-coherent in the sense of Stacks 03DL(6) is quasi-coherent on the inherited fppf site.

At `τ = .zariski` and `τ = .etale` this is `(1) ⟹ (3)` and `(2) ⟹ (3)` of Stacks 0EM8, for a
module that is already a sheaf for the inherited fppf topology. -/
public theorem isQuasicoherentOnSite_of_siteRestriction
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
      (ringStructureSheafCore B S hS p hp .fppf)).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_le
    (BigFppfOver.associatedTopology_le_fppf B S hS p τ) _ M hM

/-- A sheaf of modules on the inherited fppf site whose reading for a coarser associated topology
is quasi-coherent, as an object of the category of quasi-coherent modules of Stacks 06WG. -/
public def quasicoherentOfSiteRestriction
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
      (ringStructureSheafCore B S hS p hp .fppf)).obj M).IsQuasicoherentOnSite) :
    quasicoherentModules.{u, v, w, u} B S hS p hp :=
  ⟨M, isQuasicoherentOnSite_of_siteRestriction B S hS p hp τ M hM⟩

section

variable {𝒴 : Type (u + 1)} [Category.{u} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids)

/-- Reading a module sheaf for a coarser associated topology,
`AlgebraicGeometry.FibredSite.siteRestriction`, is the functor
`Stacks.SheafOfModules.comparisonPushforward` for the inclusion of that topology. -/
public theorem siteRestriction_eq_comparisonPushforward :
    siteRestriction B S hS q hq τ =
      Stacks.SheafOfModules.comparisonPushforward
        (BigFppfOver.associatedTopology_le_fppf B S hS q τ)
        (ringStructureSheafCore B S hS q hq .fppf) := rfl

end

end AlgebraicGeometry.FibredSite

end
