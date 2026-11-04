module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.Topology.OpensMapFinal

/-!
# The descent condition on a base change, and triviality of the pulled-back module

Let `f : X ⟶ S` be a morphism of schemes and `E` a sheaf of modules on `X`. A morphism
`g : T ⟶ S` *satisfies the descent condition* for `E` when the pullback of `E` to the base
change `X_T = X ×_S T` comes from a finite locally free module on `T`; this is
`AlgebraicGeometry.DescendsFromBase`. It is the condition whose representability by an
immersion of finite presentation is [Stacks, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP),
and whose lifting along valuation rings is the content of
[Stacks, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0) once that representability is
known.

The result proved here is the implication that converts a *triviality* statement about the
pulled-back module into the descent condition: if the pullback of `E` to `X_T` is isomorphic
to the structure sheaf of `X_T`, then `g` satisfies the descent condition, witnessed by the
structure sheaf of `T`. This is the step by which the conclusion of
[Stacks, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8) — "the invertible module is
trivial" — becomes an instance of the descent condition, which is how Tag 0BF0's proof uses
it.

Its proof needs that pullback of sheaves of modules along a morphism of ringed spaces carries
the structure sheaf to the structure sheaf, `f^* 𝒪_Y ≅ 𝒪_X`. Mathlib supplies the canonical
map `SheafOfModules.pullbackObjUnitToUnit` and proves it invertible when the functor between
the two sites is final; the finality needed here holds for the inverse-image functor on opens
of *any* continuous map, which is `Stacks.Topology.final_opensMap`.

## Main definitions

* `AlgebraicGeometry.DescendsFromBase` is the descent condition on a base change.

## Main results

* `AlgebraicGeometry.descendsFromBase_of_nonempty_iso_unit`: a base change whose pulled-back
  module is trivial satisfies the descent condition.

## Implementation notes

The descent condition is stated with `Nonempty` of an isomorphism rather than with a chosen
isomorphism, so that no descent datum is part of the condition, and with the two pullback
projections of `CategoryTheory.Limits.pullback` read as morphisms of ringed spaces through
`Scheme.Hom.toLRSHom` and `LocallyRingedSpace.Hom.toShHom`, which is the form
`RingedSpaceModuleAdjunction.modulePullback` consumes.

Both `SheafOfModules.pullback` and `SheafOfModules.pullbackObjUnitToUnit` take the adjointness
of the pushforward as an instance argument, and `modulePullback` supplies it internally, so the
two readings of the pullback functor only agree once the same fact is available to instance
search; that is
`RingedSpaceModuleAdjunction.pushforward_structureSheafHom_isRightAdjoint`.

What is *not* proved here is what Tag 0BF0 needs beyond this: the construction of the descent
locus (Tag 0BDP, which rests on cohomology and base change for perfect complexes, Tag 0B91)
and the triviality theorem over a valuation ring (Tag 0EX8). Neither the converse of
`descendsFromBase_of_nonempty_iso_unit` nor any statement about the locus itself is proved
here; the converse would require that a finite locally free module of rank one on a local base
is trivial, which is not available.

## References

* [Stacks Project, Tag 0BF0](https://stacks.math.columbia.edu/tag/0BF0)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
* [Stacks Project, Tag 0EX8](https://stacks.math.columbia.edu/tag/0EX8)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Finality of the inverse-image functor on opens of a morphism of ringed spaces, in the
spelling `RingedSpaceModuleAdjunction.structureSheafHom` uses, so that instance search finds
it. -/
instance opensMapFinal : (opensMap f).Final := Stacks.Topology.final_opensMap _

end

/-- A morphism `g : T ⟶ S` satisfies the *descent condition* for a sheaf of modules `E` on `X`
over `f : X ⟶ S` when the pullback of `E` to the base change `X ×_S T` is isomorphic to the
pullback of some finite locally free module on `T`.

This is the condition whose representability by an immersion of finite presentation is
Stacks Tag 0BDP. -/
def DescendsFromBase {X S : Scheme.{u}} (f : X ⟶ S)
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {T : Scheme.{u}} (g : T ⟶ S) : Prop :=
  ∃ N : SheafOfModules.{u} (structureSheafRing T.toRingedSpace),
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
      Nonempty ((modulePullback (pullback.snd f g).toLRSHom.toShHom).obj N ≅
        (modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E)

/-- If the pullback of `E` to the base change `X ×_S T` is trivial, that is isomorphic to the
structure sheaf of `X ×_S T`, then `g` satisfies the descent condition for `E`: the structure
sheaf of `T` is finite locally free, and its pullback to `X ×_S T` is the structure sheaf
there.

This is the implication by which the conclusion of Stacks Tag 0EX8 becomes an instance of the
descent condition. The converse is not proved: it would need that a finite locally free module
of rank one on the base is trivial. -/
theorem descendsFromBase_of_nonempty_iso_unit {X S : Scheme.{u}} (f : X ⟶ S)
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {T : Scheme.{u}} (g : T ⟶ S)
    (h : Nonempty ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E ≅
      SheafOfModules.unit (structureSheafRing (pullback f g).toRingedSpace))) :
    DescendsFromBase f E g :=
  ⟨SheafOfModules.unit (structureSheafRing T.toRingedSpace),
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (SheafOfModules.unit (structureSheafRing T.toRingedSpace)) 1
      (hM := SheafOfModules.isFiniteLocallyFreeOfRank_unit T),
    ⟨modulePullbackObjUnitIso _ ≪≫ h.some.symm⟩⟩

end AlgebraicGeometry

end
