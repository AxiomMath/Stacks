module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# A map of quasi-coherent modules with flat target over an affine base

Let `S = Spec R` be an affine scheme, let `X` be an algebraic space over `S`, and let
`u : F ⟶ G` be a map of quasi-coherent `𝒪_X`-modules whose target `G` is flat over `S`.
Stacks 0CWA fixes this data; it is the standing situation in which one asks for the largest
closed subscheme of `S` over which `u` becomes zero.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation`: **Stacks 0CWA**, the data of an
  affine base, an algebraic space over it, and a map of quasi-coherent modules with flat
  target.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.toModuleMapSituation`: the situation
  read as an instance of Stacks 083F, for the structure morphism of `X` to the base.

## Main results

There are no results beyond the definitions; the situation only fixes notation.

## Implementation notes

The base `S` of the big fppf site plays the role of `Spec R`, and affineness of `S` is the
source's `S = Spec(R)`; the ring `R` is then the ring of global functions on `S`. The base
read as an algebraic space over itself is `AlgebraicGeometry.Space.terminalSpace`, the final
object of the category of algebraic spaces over `S`, so the structure morphism of `X` over
the base is the unique morphism to it and needs no separate datum.

Flatness of `G` over `S` is `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV, taken along
that structure morphism. It is stated at the module universe of the structure rings, which is
the only universe at which that predicate is available, so the modules here live in
`AlgebraicGeometry.Space.Modules` at that universe rather than at an independent one.

Quasi-coherence of the two modules is carried as a pair of hypotheses on
`AlgebraicGeometry.Space.Modules`, rather than by taking the modules in the full subcategory
`AlgebraicGeometry.Space.QuasicoherentSheaves` of Stacks 03G9; the two are equivalent data,
and this is the form used by `AlgebraicGeometry.Space.ModuleMapSituation`, the situation of
Stacks 083F of which this one is a special case.

## References

* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CWA.** The standing data of Stacks 0CWA: an affine base `S = Spec R`, an
algebraic space `X` over `S`, and a map `u : F ⟶ G` of quasi-coherent `𝒪_X`-modules whose
target is flat over `S`. -/
@[stacks 0CWA]
structure ModuleMapFlatTargetSituation [IsAffine S] where
  /-- The algebraic space over the affine base, carrying the two modules. -/
  X : AlgebraicSpaces B S hS
  /-- The source module of the map. -/
  F : Modules.{u, u} B S hS X.1 X.2
  /-- The target module of the map. -/
  G : Modules.{u, u} B S hS X.1 X.2
  /-- The source module is quasi-coherent. -/
  quasicoherent_F : F.IsQuasicoherentOnSite
  /-- The target module is quasi-coherent. -/
  quasicoherent_G : G.IsQuasicoherentOnSite
  /-- The map of quasi-coherent modules whose vanishing after base change is studied. -/
  u : F ⟶ G
  /-- The target module is flat over the base, along the structure morphism of `X`. -/
  flat_G : IsFlatOver B S hS X.2 ((terminalSpace_isTerminal B S hS).from X).hom G

namespace ModuleMapFlatTargetSituation

/-- The structure morphism to the base of the algebraic space of the situation: the unique
morphism to the final algebraic space over `S`. -/
def structureMorphism [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS) :
    D.X ⟶ terminalSpace B S hS :=
  (terminalSpace_isTerminal B S hS).from D.X

/-- The structure morphism to the base is the only morphism of algebraic spaces from `X` to
the base. -/
theorem structureMorphism_eq [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)
    (f : D.X ⟶ terminalSpace B S hS) : f = D.structureMorphism B S hS :=
  (terminalSpace_isTerminal B S hS).hom_ext _ _

/-- The target module is flat over the base along the structure morphism. -/
theorem isFlatOver_G [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS) :
    IsFlatOver B S hS D.X.2 (D.structureMorphism B S hS).hom D.G :=
  D.flat_G

/-- The situation of Stacks 0CWA, read as an instance of the situation of Stacks 083F for the
structure morphism of `X` to the base. -/
def toModuleMapSituation [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS) :
    ModuleMapSituation.{u, u} B S hS where
  X := D.X
  Y := terminalSpace B S hS
  f := D.structureMorphism B S hS
  F := D.F
  G := D.G
  quasicoherent_F := D.quasicoherent_F
  quasicoherent_G := D.quasicoherent_G
  u := D.u

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end

