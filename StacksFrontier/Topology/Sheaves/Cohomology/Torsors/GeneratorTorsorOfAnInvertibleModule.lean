module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneIff.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.ModuleAssociatedToAUnitTorsor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The torsor of generators of an invertible module

Let `X` be a ringed space all of whose stalks `𝒪_{X, x}` are local rings and let `L` be an
invertible sheaf of `𝒪_X`-modules.  Then `L` is finite locally free of rank one, so the
sections trivializing it form a torsor under the sheaf of units `𝒪_X^*`.  Isomorphic modules
have the same torsor class, and every class of a torsor under `𝒪_X^*` arises this way.

## Main definitions

* `Stacks.Cohomology.Generators.generatorTorsorOfInvertible`: the torsor of generators of an
  invertible module.
* `Stacks.Cohomology.Generators.generatorTorsorClassOfInvertible`: its isomorphism class.

## Main results

* `Stacks.Cohomology.Generators.isFiniteLocallyFreeOfRank_one_of_isInvertible`: an invertible
  module on a ringed space with local stalks is finite locally free of rank one.
* `Stacks.Cohomology.Generators.generatorTorsorClassOfInvertible_eq_of_iso`: isomorphic
  invertible modules have the same generator-torsor class.
* `Stacks.Cohomology.Generators.exists_generatorTorsorClassOfInvertible_eq`: every class of a
  torsor under the sheaf of units is the generator-torsor class of an invertible module.

## Implementation notes

`Stacks.Cohomology.Generators.generatorTorsor` takes finite local freeness of rank one as an
instance hypothesis, while the declarations here take invertibility together with local stalks;
the two are interchangeable by
`Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one`.  Both predicates
are `Prop`-valued classes, so the instance derived from invertibility is the unique one.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Generators

/-- An invertible sheaf of modules on a ringed space all of whose stalks are local rings is
finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible (X : RingedSpace.{u, u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1 :=
  (Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L).mp
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL)

/-- The sections of an invertible module `L` that trivialize it form a sheaf of sets on which
the sheaf of units acts simply transitively: the *generator torsor* of `L`.  The identification
of its sections with the trivializing sections of `L`, and the compatibility of that
identification with restriction and with the action of units, are part of the data. -/
@[stacks 09NU "the generator torsor", ega "IV 21.13.13" "special case"]
def generatorTorsorOfInvertible (X : RingedSpace.{u, u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L) :
    GeneratorTorsor X L :=
  haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible X L hL
  generatorTorsor X L

/-- The generator torsor of an invertible module, read at the rank-one spelling. -/
theorem generatorTorsorOfInvertible_eq (X : RingedSpace.{u, u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1] :
    generatorTorsorOfInvertible X L hL = generatorTorsor X L := rfl

/-- The isomorphism class, in the group of torsor classes under the sheaf of units, of the
generator torsor of an invertible module. -/
def generatorTorsorClassOfInvertible (X : RingedSpace.{u, u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L) :
    Stacks.Cohomology.SheafTorsor.TorsorClass X (unitsSheaf X) :=
  Quotient.mk _ (generatorTorsorOfInvertible X L hL).toTorsor

/-- Isomorphic invertible modules have isomorphic generator torsors, hence the same class. -/
theorem generatorTorsorClassOfInvertible_eq_of_iso (X : RingedSpace.{u, u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    {L N : SheafOfModules.{u} (structureSheaf X.sheaf)}
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L)
    (hN : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property N)
    (e : L ≅ N) :
    generatorTorsorClassOfInvertible X L hL = generatorTorsorClassOfInvertible X N hN := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible X L hL
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible X N hN
  exact Quotient.sound (Relation.EqvGen.rel _ _ (generatorTorsor_iso_of_iso X e))

/-- The module glued from a torsor under the sheaf of units is invertible. -/
theorem torsorAssociatedSheafOfModules_isInvertible {X : RingedSpace.{u, u}}
    {F : Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X)} (D : TorsorCoverData X F) :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      (torsorAssociatedSheafOfModules D) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one X
      (torsorAssociatedSheafOfModules D))

/-- Every class of a torsor under the sheaf of units is the generator-torsor class of an
invertible module. -/
theorem exists_generatorTorsorClassOfInvertible_eq (X : RingedSpace.{u, u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)]
    (c : Stacks.Cohomology.SheafTorsor.TorsorClass X (unitsSheaf X)) :
    ∃ (L : SheafOfModules.{u} (structureSheaf X.sheaf))
      (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
        (structureSheaf X.sheaf).property L),
      generatorTorsorClassOfInvertible X L hL = c := by
  refine Quotient.inductionOn c fun F => ?_
  refine ⟨torsorAssociatedSheafOfModules (torsorCoverData X F),
    torsorAssociatedSheafOfModules_isInvertible (torsorCoverData X F), ?_⟩
  exact Quotient.sound (Relation.EqvGen.rel _ _
    ⟨torsorAssociatedGeneratorTorsorHom (torsorCoverData X F),
      torsorAssociatedGeneratorTorsorHom_isIso (torsorCoverData X F)⟩)

end Stacks.Cohomology.Generators

end
