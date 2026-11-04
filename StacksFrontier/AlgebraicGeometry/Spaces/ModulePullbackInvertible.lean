module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The inverse image of an invertible module on an algebraic space is invertible

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `L` be an invertible `𝒪_Y`-module on the small étale site.  Then the inverse image `f^*L` of
Stacks 03LU is an invertible `𝒪_X`-module.

This is Stacks 0B8P, which is proved for an arbitrary morphism of ringed topoi as
`Stacks.SheafOfModules.isInvertible_pullbackModules_obj`, read at the morphism of small étale
ringed topoi of Stacks 03G8: `AlgebraicGeometry.Space.modulePullback` *is* the pullback of
modules of that morphism, by `AlgebraicGeometry.Space.modulePullback_eq`.

## Main results

* `AlgebraicGeometry.Space.isInvertible_modulePullback_obj`: **Stacks 0B8P on the small étale
  sites of algebraic spaces.**  The inverse image of an invertible module is invertible.

## Implementation notes

The invertibility predicate is converted twice, because Stacks 0B8P is stated with the class of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Invertible.lean` while the divisor files use
`AlgebraicGeometry.SheafOfModules.IsInvertible`: in through
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry` and out through
`Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry`, exactly as
`StacksFrontier/AlgebraicGeometry/Spaces/InvertibleQuasicoherent.lean` converts in.

The sheafification hypotheses of Stacks 0B8P are at `AddCommGrpCat.{u}`, the universe of the
sections of the structure sheaves, and are supplied as local instances rather than left to
instance search: they are registered for `AlgebraicGeometry.Space.SmallEtale.topology` and
instance search does not unfold `AlgebraicGeometry.Space.smallEtaleRingedTopos` to see that the
topology of the ringed topos is that one.

## References

* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0B8P on the small étale sites of algebraic spaces.**  The inverse image of an
invertible `𝒪_Y`-module along a morphism `f : X ⟶ Y` of algebraic spaces is an invertible
`𝒪_X`-module.

This is `Stacks.SheafOfModules.isInvertible_pullbackModules_obj` at the morphism of small étale
ringed topoi of Stacks 03G8, whose pullback of modules is
`AlgebraicGeometry.Space.modulePullback`. -/
theorem isInvertible_modulePullback_obj (f : X ⟶ Y) (L : Modules.{u, u} B S hS Y.1 Y.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property ((modulePullback B S hS f).obj L) := by
  have key (Z : AlgebraicSpaces B S hS) :
      HasWeakSheafify (smallEtaleRingedTopos B S hS Z).J AddCommGrpCat.{u} ∧
        (smallEtaleRingedTopos B S hS Z).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    ⟨inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u}),
      inferInstanceAs ((SmallEtale.topology B S hS Z.1).WEqualsLocallyBijective AddCommGrpCat.{u})⟩
  obtain ⟨hX₁, hX₂⟩ := key X
  obtain ⟨hY₁, hY₂⟩ := key Y
  have h : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedTopos B S hS Y).O.obj
      (structureRingSheaf B S hS Y).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (smallEtaleRingedToposModulesHom B S hS f) L)

end AlgebraicGeometry.Space

end
