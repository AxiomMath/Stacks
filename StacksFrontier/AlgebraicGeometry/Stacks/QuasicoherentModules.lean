module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Quasi-coherent modules on a category fibred in groupoids (Stacks 06WG)

A module on the fppf site of a category fibred in groupoids over schemes is quasi-coherent when
it is quasi-coherent as a module on the associated ringed site. The category of such modules is
the full subcategory of sheaves of modules satisfying that condition.

Quasi-coherence is the predicate `SheafOfModules.IsQuasicoherentOnSite` of Tag 03DL(6) for a
general ringed site. Taking its full subcategory over
`AlgebraicGeometry.Stack.ringStructureSheafCore` at the fppf topology gives the category written
`QCoh(𝒪_𝒳)` in the source. The abbreviation
exposes the underlying full subcategory, so its objects carry the quasi-coherence instance
directly and the usual full-subcategory inclusion is available.

The fppf topology is the value `B.topology` of the structure sheaf's topology parameter, whose
comparison hypothesis is then `le_rfl`; see the "Generality of `τ`" section of
`StacksFrontier/AlgebraicGeometry/Stacks/StructureSheaf.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.quasicoherentModules`: **Stacks 06WG**, the category of
  quasi-coherent modules on the fppf ringed site of a category fibred in groupoids.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Stack

/-- **Stacks 06WG.** The category of quasi-coherent modules on the fppf ringed site of a
category fibred in groupoids over the schemes over `S`.

Tag 06WG is registered, under no part key, on
`AlgebraicGeometry.FibredSite.quasicoherentModules` in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Modules.lean`, which is this category
again at `τ = .fppf` and is equal to it by `rfl`; this declaration is deliberately left
untagged, so do not add a tag registration here. -/
abbrev quasicoherentModules (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) :=
  (SheafOfModules.isQuasicoherentOnSite
    (ringStructureSheafCore B S hS p hp B.topology le_rfl)).FullSubcategory

end AlgebraicGeometry.Stack

end
