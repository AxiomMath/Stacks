module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# The whole of the characterisation of an unramified monomorphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. [Stacks Project, Tag 05W6]
lists four equivalent conditions on `f`:

1. `f` is unramified and a monomorphism,
2. `f` is unramified and universally injective,
3. `f` is locally of finite type and a monomorphism,
4. `f` is universally injective, locally of finite type and formally unramified,

and asserts that such an `f` is moreover representable, separated and locally quasi-finite.

`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism` and
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria` prove the three equivalences with
condition (1) and the separatedness and local quasi-finiteness clauses of the "moreover" part.
This file proves the remaining clause, representability, and assembles the tag into a single
statement.

## Main definitions

There are no new definitions.

## Main results

* `Space.isUnramified_mono_tfae_and_relativelyRepresentable_isSeparated_isLocallyQuasiFinite`
  is the whole of [Stacks Project, Tag 05W6]: the equivalence of the four conditions together
  with the three assertions of the "moreover" clause.

## Implementation notes

The three equivalences with condition (1) are
`AlgebraicGeometry.Space.isUnramified_mono_iff_isUnramified_universallyInjective`,
`AlgebraicGeometry.Space.isUnramified_mono_iff_isLocallyOfFiniteType_mono` and
`Space.isUnramified_mono_iff_universallyInjective_locallyOfFiniteType_formallyUnramified`,
so the four conditions are equivalent by `List.TFAE` from condition (1) as the hub.

The "moreover" clause is read off condition (3), to which condition (1) is equivalent. A
monomorphism which is locally of finite type is separated and locally quasi-finite by
[Stacks Project, Tag 0463], which is
`AlgebraicGeometry.Space.isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono`; and a
separated locally quasi-finite morphism of algebraic spaces is representable by
[Stacks Project, Tag 0418], which is
`AlgebraicGeometry.Space.relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable`. Representability is
relative representability along the Yoneda embedding of the big fppf site over `S`, which for a
morphism of algebraic spaces is exactly the source's notion: every base change along a morphism
from a scheme is a scheme.

## References

* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 05W6.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The
following are equivalent:

1. `f` is unramified and a monomorphism,
2. `f` is unramified and universally injective,
3. `f` is locally of finite type and a monomorphism,
4. `f` is universally injective, locally of finite type and formally unramified.

Moreover, in that case `f` is representable, separated and locally quasi-finite.

The equivalences run through condition (1). The "moreover" clause is taken at condition (3):
separatedness and local quasi-finiteness are [Stacks Project, Tag 0463], and representability
follows from them by [Stacks Project, Tag 0418]. -/
@[stacks 05W6]
theorem isUnramified_mono_tfae_and_relativelyRepresentable_isSeparated_isLocallyQuasiFinite
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE
      [IsUnramified B S hS f ∧ Mono f,
        IsUnramified B S hS f ∧ UniversallyInjective B S hS f,
        IsLocallyOfFiniteType B S hS f ∧ Mono f,
        UniversallyInjective B S hS f ∧ IsLocallyOfFiniteType B S hS f ∧
          FormallyUnramified (B := B) (S := S) (hS := hS) f] ∧
      ((IsUnramified B S hS f ∧ Mono f) →
        yoneda.relativelyRepresentable f ∧ IsSeparated B S hS f ∧
          IsLocallyQuasiFinite B S hS f) := by
  refine ⟨?_, fun h => ?_⟩
  · tfae_have 1 ↔ 2 := isUnramified_mono_iff_isUnramified_universallyInjective B S hS hX hY f
    tfae_have 1 ↔ 3 := isUnramified_mono_iff_isLocallyOfFiniteType_mono B S hS hX hY f
    tfae_have 1 ↔ 4 :=
      isUnramified_mono_iff_universallyInjective_locallyOfFiniteType_formallyUnramified
        B S hS hX hY f
    tfae_finish
  · have h₃ : IsLocallyOfFiniteType B S hS f ∧ Mono f :=
      (isUnramified_mono_iff_isLocallyOfFiniteType_mono B S hS hX hY f).mp h
    have hsep := isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS f h₃
    exact ⟨relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS f hX hY
      hsep.2 hsep.1, hsep.1, hsep.2⟩

end AlgebraicGeometry.Space

end
