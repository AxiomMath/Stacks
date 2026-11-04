module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre

/-!
# The composition of admissible blowups of an algebraic space

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `U ⊆ X` be a quasi-compact open subspace.  Tag 086C asserts that if `b : X' ⟶ X` is a
`U`-admissible blowup and `X'' ⟶ X'` is a `U`-admissible blowup, then the composition
`X'' ⟶ X` is a `U`-admissible blowup.

## Main results

* `AlgebraicGeometry.Space.isAdmissibleBlowup_comp_of_isQuasiCompactSpace`: over a quasi-compact
  quasi-separated algebraic space, the composition of two `U`-admissible blowups is a
  `U`-admissible blowup.

## References

* [Stacks Project, Tag 086C](https://stacks.math.columbia.edu/tag/086C)
* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X X' X'' : AlgebraicSpaces B S hS}

/-- Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S`
and let `U ⊆ X` be an open subspace.  Let `b : X' ⟶ X` be a `U`-admissible blowup and let
`c : X'' ⟶ X'` be a `U`-admissible blowup.  Then the composition `c ≫ b : X'' ⟶ X` is a
`U`-admissible blowup.

Since `b` is an isomorphism over `U`, the source regards `U` as an open subspace of `X'` as well;
as a subspace of `X'` it is the inverse image `b⁻¹(U)`, which is how the admissibility of `c`
is stated.  Quasi-separatedness of `X` is absolute quasi-separatedness, which needs the terminal
scheme in the site (`hZ`).  The source also takes `U` quasi-compact; that hypothesis is not
needed and is omitted. -/
@[stacks 086C]
theorem isAdmissibleBlowup_comp_of_isQuasiCompactSpace
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U : OpenSubspaces B S hS X.1) {b : X' ⟶ X} {c : X'' ⟶ X'}
    (hb : IsAdmissibleBlowup B S hS U b)
    (hc : IsAdmissibleBlowup B S hS
      ⟨U.1.preimage b.hom, isOpenSubspace_preimage B S hS b.hom U.1 X.2 X'.2 U.2⟩ c) :
    IsAdmissibleBlowup B S hS U (c ≫ b) :=
  isAdmissibleBlowup_comp U hb hc fun _ hZfp hbZ => hasSecondCentre hZ hXqc hXqs hZfp hbZ

end AlgebraicGeometry.Space

end
