module

public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeCategory
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the objects of `FTS S` over a Noetherian base

In the setting of [Stacks, Tag 0F42] the base `S` is Noetherian, and
`AlgebraicGeometry.FTS S` is the category of schemes separated and of finite type over it.
Over such a base the objects of `FTS S` inherit the finiteness hypotheses under which the
right adjoint of derived pushforward is studied in Chapter 48, Section 9: each is locally
Noetherian, quasi-compact and quasi-separated, and every closed immersion into one is
pseudo-coherent.

The module exists because `AlgebraicGeometry.Duality.SeparatedFiniteTypeCategory`
deliberately keeps a minimal import surface and does not impose the Noetherian hypothesis on
`S`; the consequences of imposing it are collected here instead, so that a consumer of
`FTS S` that does not need pseudo-coherence does not pay for it.

## Main results

* `AlgebraicGeometry.FTS.isLocallyNoetherian`: an object of `FTS S` is locally Noetherian
  when `S` is.
* `AlgebraicGeometry.FTS.compactSpace`: an object of `FTS S` is quasi-compact when `S` is.
* `AlgebraicGeometry.FTS.quasiSeparatedSpace`: an object of `FTS S` is quasi-separated when `S`
  is.
* `AlgebraicGeometry.FTS.pseudoCoherent_of_isClosedImmersion`: a closed immersion into an
  object of `FTS S` is pseudo-coherent when `S` is locally Noetherian.

## Implementation notes

`FTS.isLocallyNoetherian` and `FTS.compactSpace` are stated for the underlying scheme
`X.left` of an object `X : FTS S`, which is the form in which typeclass synthesis meets
them. Over a Noetherian base quasi-separatedness also follows from local Noetherianness by
`AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`; `FTS.quasiSeparatedSpace` serves a
quasi-separated base.

`pseudoCoherent_of_isClosedImmersion` is the hypothesis that [Stacks, Tag 0A9X] asks of a
closed immersion, discharged in the setting of [Stacks, Tag 0F42]. Its two inputs are
`AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType` ([Stacks, Tag 0684]) and
Mathlib's instance making a closed immersion locally of finite type.

## References

* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FTS

variable {S : Scheme.{u}}

/-- An object of `FTS S` is locally Noetherian as soon as the base `S` is, being of finite
type over it. -/
instance isLocallyNoetherian [IsLocallyNoetherian S] (X : FTS S) :
    IsLocallyNoetherian X.left := by
  have : IsLocallyNoetherian ((Functor.fromPUnit S).obj X.right) :=
    (inferInstance : IsLocallyNoetherian S)
  exact LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- An object of `FTS S` has compact underlying space as soon as `S` does, its structure
morphism being quasi-compact. -/
instance compactSpace [CompactSpace S] (X : FTS S) : CompactSpace X.left := by
  have : CompactSpace ((Functor.fromPUnit S).obj X.right) :=
    (inferInstance : CompactSpace S)
  exact QuasiCompact.compactSpace_of_compactSpace X.hom

/-- An object of `FTS S` is quasi-separated as soon as `S` is, its structure morphism being
separated. -/
instance quasiSeparatedSpace [QuasiSeparatedSpace S] (X : FTS S) :
    QuasiSeparatedSpace X.left := by
  have : QuasiSeparatedSpace ((Functor.fromPUnit S).obj X.right) :=
    (inferInstance : QuasiSeparatedSpace S)
  exact quasiSeparatedSpace_of_quasiSeparated X.hom

/-- A closed immersion into an object of `FTS S` is pseudo-coherent when the base `S` is
locally Noetherian. This is the hypothesis on a closed immersion in [Stacks, Tag 0A9X],
discharged in the setting of [Stacks, Tag 0F42]. -/
theorem pseudoCoherent_of_isClosedImmersion [IsLocallyNoetherian S] {Y : FTS S}
    {X : Scheme.{u}} (i : X ⟶ Y.left) [IsClosedImmersion i] : PseudoCoherent i :=
  (pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance

/-- A morphism of `FTS S` whose underlying morphism of schemes is a closed immersion is
pseudo-coherent, when the base `S` is locally Noetherian. -/
@[sga "6 III 1.3" "special case"]
theorem pseudoCoherent_left_of_isClosedImmersion [IsLocallyNoetherian S] {X Y : FTS S}
    (i : X ⟶ Y) [IsClosedImmersion i.left] : PseudoCoherent i.left :=
  pseudoCoherent_of_isClosedImmersion i.left

end FTS

end AlgebraicGeometry

end
