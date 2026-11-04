module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Chart
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# The "equality_flat" clause of Stacks tag 063W

Stacks tag 063W is a four-part lemma about a closed subscheme `T` of a scheme `X` which is flat
and locally of finite presentation over a base `S`, at a point `x` of `T` whose fibre
`T_s ⊆ X_s` is a quasi-regular immersion near `x`.  Its second item adds to those hypotheses
that `T → X` be of finite presentation and that `T → S` be flat at `x`, and concludes that the
relative quasi-regular immersion produced by the first item can be taken to be `T` itself:
there is an open `U ∋ x` with `T ∩ U = Z`.

This file records that one item.  Taking `Z = T ∩ U` as the witness, the first item's remaining
assertions — `Z_s = T_s ∩ U_s` and `T ∩ U ⊆ Z` — hold by construction, so the content of the
item is that `T ∩ U ⊆ U` is a relative quasi-regular immersion over `S`;  the closing sentence
of the lemma, that `Z → U` is in each case a regular immersion, is carried along as the second
conjunct.  That is exactly `Stacks.AlgebraicGeometry.Statement063W`, which
`Stacks.AlgebraicGeometry.statement063W` proves unconditionally, and the theorem below is that
proposition with ordinary binders.

The other three items of the tag are recorded elsewhere:  the existence of a containing relative
quasi-regular `Z` (item (1)) in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/RelativeRegularImmersion/Containing.lean`, the
equality obtained from the expected number of equations (item (3)) in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/RelativeRegularImmersion/EqualityEquationCount.lean`
and the fibrewise criterion (the closing "in particular") in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/RelativeRegularImmersion/Fibrewise.lean`.  That is
why the tag is recorded here with the `"equality_flat"` comment rather than bare.

## Main results

* `Stacks.AlgebraicGeometry.exists_mem_isRelativeQuasiRegularImmersion_of_flatAt`: item (2) of
  Stacks tag 063W.

## Implementation notes

`T` is a `Scheme.IdealSheafData` on `X` and `T ∩ U` is `T.comap U.ι`, the inverse-image ideal on
the open subscheme `U`.  Finite presentation of `T → X` is asked for as
`LocallyOfFinitePresentation T.subschemeι`:  a closed immersion is affine, hence quasi-compact
and quasi-separated, so the two notions agree for it, and the weaker spelling is the weaker
hypothesis.  Flatness of `T → S` at `x` is flatness of the stalk map of `T.subschemeι ≫ f` at
the point of `T.subscheme` over `x`.  Quasi-regularity of the fibre near `x` is quasi-regularity
of the closed immersion cut out by `T` on some open neighbourhood of the image of `x` in
`f.fiber (f x)`.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- **Stacks tag 063W, item (2).**  Let `f : X ⟶ S` be flat and locally of finite presentation,
let `T` be a closed subscheme of `X` whose closed immersion into `X` is locally of finite
presentation, and let `x` be a point of `T` such that the fibre of `T` over `f x` is a
quasi-regular immersion on a neighbourhood of `x` and `T` is flat over `S` at `x`.  Then there
is an open `U ∋ x` on which `T` itself is a relative quasi-regular immersion over `S`, and a
regular immersion. -/
@[stacks 063W "equality_flat", ega "IV 19.2.4" "b) => c)"]
theorem exists_mem_isRelativeQuasiRegularImmersion_of_flatAt {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (T : X.IdealSheafData)
    [LocallyOfFinitePresentation T.subschemeι] (x : X) (hx : x ∈ T.support)
    (hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧
      IsQuasiRegularImmersion (((T.comap (f.fiberι (f x))).comap V.ι).subschemeι))
    (hflat : ((T.subschemeι ≫ f).stalkMap (⟨x, hx⟩ : T.subscheme)).hom.Flat) :
    ∃ U : X.Opens, x ∈ U ∧
      IsRelativeQuasiRegularImmersion (U.ι ≫ f) (T.comap U.ι).subschemeι ∧
        IsRegularImmersion (T.comap U.ι).subschemeι :=
  statement063W f inferInstance inferInstance T inferInstance x hx hfib hflat

end Stacks.AlgebraicGeometry

end
