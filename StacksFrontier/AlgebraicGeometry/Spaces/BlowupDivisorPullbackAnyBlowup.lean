module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAnyCentre

/-!
# Stacks 085X: every effective Cartier divisor pulls back along every blowup

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `b : X' ⟶ X` be a blowup of `X`
in a closed subspace. Stacks 085X says that for every effective Cartier divisor `D` on `X` the
pullback `b⁻¹(D)` is defined in the sense of Stacks 083Y.

The hypothesis on `b` is that it is a blowup of `X` in some closed subspace: the universal property
of Stacks 085U, `AlgebraicGeometry.Space.IsBlowupAlong`, existentially quantified over the centre.

## Main results

* `AlgebraicGeometry.Space.isPullbackDefined_of_exists_isBlowupAlong`: **Stacks 085X**.

## References

* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 085X.**  Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`b : X' ⟶ X` be a blowup of `X` in a closed subspace.  Then for every effective Cartier divisor
`D` on `X` the pullback `b⁻¹(D)` is defined in the sense of Stacks 083Y: the inverse image of
`D` along `b` is an effective Cartier divisor on `X'`.

"A blowup of `X` in a closed subspace" is `∃ Z, IsBlowupAlong B S hS Z b`: `b` is a final object
of the category of algebraic spaces over `X` on which the inverse image of the closed subspace
`Z` is an effective Cartier divisor (Stacks 085U), so `b` is isomorphic over `X` to the blowing
up of `X` along `Z` of Stacks 085Q. -/
@[stacks 085X "the full statement, for every morphism b which is a blowup of X in some closed \
subspace (Stacks 085U universal property) and every effective Cartier divisor D on X; no \
construction data and no size condition on the site among the hypotheses"]
theorem isPullbackDefined_of_exists_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    (b : X' ⟶ X) (hb : ∃ Z : ClosedSubspaces B S hS X.1, IsBlowupAlong B S hS Z b) :
    ∀ D : ClosedSubspaces B S hS X.1, IsEffectiveCartierDivisor B S hS X D →
      IsPullbackDefined B S hS b D := by
  obtain ⟨Z, hZ⟩ := hb
  exact fun D hD => hZ.isPullbackDefined_of_isEffectiveCartierDivisor D hD

end AlgebraicGeometry.Space

end
