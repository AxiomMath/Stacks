module

public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic

/-!
# Quasi-projective morphisms

`AlgebraicGeometry.IsQuasiProjective` — finite type together with a relatively ample invertible
sheaf — is the first of the three notions of [Stacks, Tag 01VW] and is defined in
`StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic`. This file adds the other two: the
*H-quasi-projective* condition, a quasi-compact immersion into relative projective space over
the base, and *local* quasi-projectivity, tested after restricting over an open cover of the
base.

## Main definitions

* `AlgebraicGeometry.IsHQuasiProjective`: a quasi-compact immersion into projective space over
  the base, compatible with the structure morphisms.
* `AlgebraicGeometry.IsLocallyQuasiProjective`: quasi-projectivity on an open cover of the base.

## Implementation notes

An open-cover restriction is the pullback along the corresponding open immersion. Both
predicates are transparent abbreviations, so clients can use their defining existential and
conjunction data directly without an unfolding lemma.

Projective space over a base is `AlgebraicGeometry.projectiveSpaceOver` (Tag 01NF).

## References

* [EGA II, Definition 5.3.1]
* [H, page 103]
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01VW.** A quasi-compact immersion into relative
finite-dimensional projective space.  This is `Stacks.HProjective.IsHQuasiProjective`, which
states the same thing with the structure morphism of `ℙⁿ_S` spelled `↘`. -/
@[stacks 01VW "H-quasi-projective"]
abbrev IsHQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Stacks.HProjective.IsHQuasiProjective f

/-- **Stacks Project, Tag 01VW.** A morphism quasi-projective after restriction over an open
cover of the base. -/
@[stacks 01VW "locally quasi-projective"]
abbrev IsLocallyQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ 𝒰 : Scheme.OpenCover.{u} S,
    ∀ i : 𝒰.I₀, IsQuasiProjective (pullback.snd f (𝒰.f i))

end AlgebraicGeometry

end
