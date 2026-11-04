module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules on a category fibred in groupoids

A module on the fppf site of a category fibred in groupoids over schemes is quasi-coherent
when it is quasi-coherent as a module on the associated ringed site, that is, when every
object of the site has a covering on whose members the restricted module has a global
presentation. The category of such modules is the full subcategory of sheaves of modules
cut out by that condition, denoted `QCoh(𝒪_𝒳)`.

## Main definitions

* `AlgebraicGeometry.FibredSite.quasicoherentModules` is the category of quasi-coherent
  modules on the fppf site of the fibred category.
* `AlgebraicGeometry.FibredSite.toSiteModules` restricts a quasi-coherent fppf module to the
  sheaves of modules for one of the associated topologies.

## Implementation notes

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the predicate of Stacks 03DL(6)
for a general ringed site, which needs no sheafification instance on the site or its slices.

`toSiteModules` changes neither the underlying presheaf of modules nor the maps between them:
the coefficient sheaf of rings has the same presheaf for every one of the five topologies, and
a sheaf for the inherited fppf topology is a sheaf for each coarser inherited topology.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u v w m

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The category of quasi-coherent modules on the fppf ringed site of a category fibred in
groupoids over the schemes over `S`. -/
@[stacks 06WG]
public abbrev quasicoherentModules :=
  (SheafOfModules.isQuasicoherentOnSite.{v, w, u, m}
    (ringStructureSheafCore B S hS p hp .fppf)).FullSubcategory

/-- Restrict a quasi-coherent fppf module to the sheaves of modules for one of the five
associated topologies, leaving the underlying presheaf of modules unchanged. -/
public def toSiteModules (τ : SiteKind) :
    quasicoherentModules.{u, v, w, m} B S hS p hp ⥤
      SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ) where
  obj M := ⟨M.obj.val,
    M.obj.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS p τ)⟩
  map f := ⟨f.hom.val⟩

end AlgebraicGeometry.FibredSite

end
