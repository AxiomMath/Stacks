module

public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyTrivialInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse

/-!
# An invertible sheaf of modules is finite locally free of rank one

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X,x}` are local rings. An invertible
`𝒪_X`-module `L` is finite locally free of rank one, and conversely a finite locally free
`𝒪_X`-module of rank one is invertible: on such a ringed space, invertibility is characterized by
finite local freeness of rank one. A section `a : L(W)` whose multiples exhaust `L(V)` bijectively
for every open `V ≤ W` gives an isomorphism of sheaves of modules `L|_W ≅ 𝒪_W`.

## Main definitions

* `Stacks.SheafOfModules.isoUnitOver`: a section `a` of `L` over `W` whose multiples exhaust
  `L(V)` bijectively for every `V ≤ W` is an isomorphism `L|_W ≅ 𝒪_W` of sheaves of modules
  over the localized site.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`: an invertible sheaf of
  modules on a ringed space with local stalks is finite locally free of rank one, for the rank
  predicate `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of
  [Stacks, Tag 01CS].
* `Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: on a ringed space whose
  structure sheaf has local stalks, a sheaf of modules is invertible if and only if it is finite
  locally free of rank one.
* `Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: the same for a
  scheme, where the stalks are local rings automatically.

## Implementation notes

Over an object `A` of the localized site `Over W` the map of `isoUnitOver` is
`c ↦ c • a|_{A.left}`, that is `LinearMap.toSpanSingleton` at the restricted section, promoted to a
linear equivalence by the bijectivity hypothesis and then to a `ModuleCat` isomorphism.
`PresheafOfModules.isoMk` assembles these into an isomorphism of presheaves of modules and
`SheafOfModules.fullyFaithfulForget` lifts it back to sheaves, as in
`SheafOfModules.overFunctorMap` of Mathlib.

The hypothesis and conclusion use `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`. The repository also carries
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`, with the same body; nothing here
identifies the two. The rank predicate is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, reached from
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank` through
`Stacks.InvertibleLocallyFree.isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/


@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))

/-- **A trivializing section is a trivialization.** If `a : L(W)` is such that `c ↦ c • a|_V` is a
bijection `𝒪_X(V) → L(V)` for every open `V ≤ W`, then `L` restricted to the localized site over
`W` is isomorphic to the structure sheaf there. -/
noncomputable def isoUnitOver (W : Opens X.carrier) (a : L.val.obj (op W))
    (ha : ∀ (V : Opens X.carrier) (hVW : V ≤ W),
      Function.Bijective fun c : X.presheaf.obj (op V) => c • (L.val.map (homOfLE hVW).op a)) :
    L.over W ≅ SheafOfModules.unit ((structureSheafRing X).over W) :=
  ((SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun A =>
      (LinearEquiv.ofBijective
        (LinearMap.toSpanSingleton _ _ (L.val.map (homOfLE (leOfHom A.unop.hom)).op a))
        (ha A.unop.left (leOfHom A.unop.hom))).toModuleIso)
      (fun A B f => by
        ext
        simp only [ModuleCat.hom_comp]
        change (((O X).map (f.unop.left).op).hom (1 : X.presheaf.obj (op A.unop.left)))
              • (L.val.map (homOfLE (leOfHom B.unop.hom)).op).hom a
            = (L.val.map (f.unop.left).op).hom
                ((1 : X.presheaf.obj (op A.unop.left))
                  • (L.val.map (homOfLE (leOfHom A.unop.hom)).op).hom a)
        rw [map_one, one_smul, one_smul, ← PresheafOfModules.map_comp_apply]
        exact L.val.congr_map_apply (Subsingleton.elim _ _) a)).symm

variable [∀ x : X.carrier, IsLocalRing (ringStalk X x)]

/-- An invertible sheaf of modules on a ringed space with local stalks is finite locally free of
rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens X.carrier) (J := Opens.grothendieckTopology X.carrier) L 1 :=
  have := Invertible.isLocallyTrivial_of_isInvertible L
  (Stacks.InvertibleLocallyFree.isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank
      X.presheaf (structureSheafRing X).property L 1).2
    (Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial L)

end Stacks.SheafOfModules

namespace Stacks.RingedSpace

/-- On a ringed space all of whose structure-sheaf stalks are local rings, a sheaf of modules is
invertible if and only if it is finite locally free of rank one. -/
@[stacks 0B8M "characterization for local stalks"]
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
        (C := Opens X) (J := Opens.grothendieckTopology X) L 1 := by
  constructor
  · intro h
    have hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X).property L := h
    have hx : ∀ x : X.carrier, IsLocalRing (ringStalk X x) := fun x => inferInstance
    exact Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (X := X) L
  · intro _
    exact isInvertible_of_isFiniteLocallyFreeOfRank_one X L

end Stacks.RingedSpace

namespace Stacks.SheafOfModules

/-- On a scheme, a sheaf of modules is invertible if and only if it is finite locally free of rank
one. -/
theorem Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one (Y : Scheme.{u}) (L : Y.Modules) :
    IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
        (C := Opens Y) (J := Opens.grothendieckTopology Y) L 1 :=
  have : ∀ x : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace x) :=
    fun x => Y.isLocalRing x
  ⟨fun h =>
      have := h
      isFiniteLocallyFreeOfRank_one_of_isInvertible (X := Y.toRingedSpace) L,
    fun h => Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one
      (h := h) Y.toRingedSpace L⟩

end Stacks.SheafOfModules

end
