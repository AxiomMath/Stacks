module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite locally free morphisms

A morphism of schemes is *finite locally free* when it is affine and the direct image of its
structure sheaf is a finite locally free module on the target. Its *rank* (or *degree*) is the
rank of that module.

## Main definitions

* `Stacks.Morphisms.IsFiniteLocallyFree` is the predicate that a morphism is finite locally
  free.
* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank` says that a finite locally free morphism has a
  given rank.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFree_iff` and
  `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff` unfold the two classes into conjunctions.
* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree` forgets the specified rank.

## Implementation notes

The direct image of the structure sheaf is `Stacks.Morphisms.pushforwardStructureSheaf`, formed
by applying Mathlib's module pushforward to the unit module; it is declared in
`StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf`, which is why this file imports
that one.

The two classes extend their constituent classes, so typeclass search can use affineness and
the module-theoretic condition directly. The module-theoretic conditions are the sheaf-level
predicates `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of Stacks Tag 01C6, instantiated
at the Zariski site of the target, which forces the three universe parameters of those
predicates to coincide.

Forgetting the rank is a named theorem rather than an instance, because the rank cannot be
recovered from `IsFiniteLocallyFree f`.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- **Stacks Project, Tag 02KA.** A morphism of schemes is finite locally free if it is affine
and the direct image of its structure sheaf is a finite locally free module. -/
@[stacks 02KA "finite locally free", sga "1 I 4.10" "more general"]
class IsFiniteLocallyFree {X S : Scheme.{u}} (f : X ⟶ S) : Prop
    extends IsAffineHom f,
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (pushforwardStructureSheaf.{u} f)

/-- **Stacks Project, Tag 02KA.** A finite locally free morphism has rank (or degree) `r` if
the direct image of its structure sheaf is finite locally free of rank `r`. -/
@[stacks 02KA "rank or degree"]
class IsFiniteLocallyFreeOfRank {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) : Prop
    extends IsAffineHom f,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pushforwardStructureSheaf.{u} f) r

/-- The definition of a finite locally free morphism, expressed as a conjunction. -/
theorem isFiniteLocallyFree_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    IsFiniteLocallyFree f ↔
      IsAffineHom f ∧
        SheafOfModules.IsFiniteLocallyFree.{u, u, u} (pushforwardStructureSheaf.{u} f) :=
  ⟨fun h ↦ ⟨h.toIsAffineHom, h.toIsFiniteLocallyFree⟩, fun ⟨h₁, h₂⟩ ↦
    .mk (toIsAffineHom := h₁) (toIsFiniteLocallyFree := h₂)⟩

/-- The definition of the rank of a finite locally free morphism, expressed as a
conjunction. -/
theorem isFiniteLocallyFreeOfRank_iff {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) :
    IsFiniteLocallyFreeOfRank f r ↔
      IsAffineHom f ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pushforwardStructureSheaf.{u} f) r :=
  ⟨fun h ↦ ⟨h.toIsAffineHom, h.toIsFiniteLocallyFreeOfRank⟩, fun ⟨h₁, h₂⟩ ↦
    .mk (toIsAffineHom := h₁) (toIsFiniteLocallyFreeOfRank := h₂)⟩

/-- A finite locally free morphism of fixed rank is finite locally free. This is not an
instance because the rank cannot in general be inferred from `IsFiniteLocallyFree f`. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFree {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    [h : IsFiniteLocallyFreeOfRank f r] : IsFiniteLocallyFree f :=
  .mk (toIsAffineHom := h.toIsAffineHom)
    (toIsFiniteLocallyFree :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} _ r)

end Stacks.Morphisms

end
