module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionAdjunction

/-!
# The equalizer of an étale surjection, with restriction along the counit as its arrow

Let `h : U ⟶ V` be a surjective étale morphism of algebraic spaces over a scheme `S` contained
in a big fppf site `B`, and let `W` be an object of the spaces-étale site of `V`.  The base
change `W ×_V U`, read back in the spaces-étale site of `V` by postcomposition with `h`, comes
with a cartesian projection to `W`, and that projection is the component at `W` of the counit
of the adjunction of sites
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`
(`AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`).  Since
`h` is surjective the projection is surjective on points, so it is a one-element covering of the
spaces-étale site, and the sheaf condition of Stacks 03H7 for that covering presents the
sections over `W` of a sheaf as an equalizer.

This file states that equalizer with its first arrow written as restriction along the counit.
That spelling is the point of the file.  The equalizer of the same covering is already available
from `AlgebraicGeometry.Space.isLimitForkProdOfEtalePresentation`, whose first arrow is
restriction along `CategoryTheory.Limits.prod.snd` for the *chosen* binary product of the
spaces-étale site — but that statement asks for `U` to be an étale *scheme chart* of `V`,
surjective on points, together with a second chart `R` and two morphisms exhibiting `R` as
`U ×_V U`, whereas what is asked here is a surjective étale morphism of algebraic spaces and
nothing else.  The statements below are therefore strictly more general in `U`, and so is the
covering condition: `AlgebraicGeometry.Space.isSurjective_of_isPullback_isTerminal` cannot even
be *stated* for an algebraic space `U`, since its statement names the comparison image of a
scheme chart.  No comparison between the chosen product and the base change is proved here, and
none is needed: the covering is taken to be the counit from the start.

At the universe `u` of the structure rings, restriction along the counit *is* the component of
the unit of the adjunction on sheaves
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction`, by `rfl`
(`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_app`, stated there on each
section), and it is a unit of that shape that the module-level reading of Stacks 03M8 needs.

The structure map of Stacks 03G8 of an étale morphism is also a unit, but of a *different*
adjunction: `AlgebraicGeometry.Space.structureSharpSet_eq_unit` identifies it with the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`, which lives on the small étale
sites.  That adjunction is `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction`
conjugated by the two comparison equivalences of Stacks 03G1 — one
`CategoryTheory.Adjunction.comp` against `CategoryTheory.Equivalence.toAdjunction` on each
side, transported along an isomorphism of left adjoints by
`CategoryTheory.Adjunction.ofNatIsoLeft` — and that conjugation is *not* proved here.  The two
units are not even type-comparable: the sheaves they act on live over the two different sites
`SmallEtale.topology B S hS V` and `SpacesEtale.topology B S hS V`, whose objects sit in
different universes.

## Main definitions

* `AlgebraicGeometry.Space.isLimitForkCounit` is the equalizer: for a sheaf `P` on the
  spaces-étale site of `V`, with values in an arbitrary category, and a presentation of the
  fibre product of the counit with itself, the fork
  `P(W) → P(W ×_V U) ⇉ P((W ×_V U) ×_W (W ×_V U))` whose first arrow is restriction along the
  counit is a limit.

## Main results

* `CategoryTheory.Presheaf.fork_condition_of_isPullback` is the commutation that the fork takes
  as an argument, for a presheaf on an arbitrary category; it is proved, so the fork is
  well-formed.
* `Space.isSurjective_toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit` (in
  `AlgebraicGeometry`) is Stacks 03MH for this projection: the counit is surjective on points
  when `h` is.

## Implementation notes

The fibre product of the counit with itself is left as a hypothesis rather than taken to be the
chosen pullback, because a consumer has its own presentation of it: in the proof of
Stacks 03M8, with `U → X` a surjective étale chart and `R = U ×_X U`, the object to be supplied
is `W ×_X R`, and the two parallel arrows are then restriction along the base changes of the
two projections `t, s : R ⟶ U`.  Identifying `W ×_X R` with the fibre product of the projection
with itself is `CategoryTheory.Limits.isPullback_lift_of_isTerminal` in the product spelling;
the same identification in the base-change spelling is not proved here.  The hypothesis is
never vacuous: the spaces-étale site has fibre products
(`AlgebraicGeometry.Space.SpacesEtale.instHasPullbacks`), so a consumer with no presentation of
its own supplies `CategoryTheory.IsPullback.of_hasPullback _ _` and needs no lemma of this file.

Surjectivity of the counit is deduced from the base-change datum directly rather than from
`AlgebraicGeometry.Space.isSurjective_of_isPullback_isTerminal`: the datum
`AlgebraicGeometry.Space.SpacesBaseChange.isPullback` already asserts that the projection
exhibits the base change as a fibre product of the structure morphism of `W` with `h`, so
Stacks 03MH applies to it with no passage through the terminal object of the site.

`CategoryTheory.Presheaf.fork_condition_of_isPullback` is stated for a presheaf on an arbitrary
category rather than for the counit, because the two-line proof is otherwise written out once
per fork.  Its natural home is beside
`CategoryTheory.Presheaf.isLimitForkOfSingletonCovering`; moving it there, and redirecting the
places that inline the same two lines, touches files this one only imports.

At a general coefficient category restriction along the counit is still the component of the
unit, but no longer by `rfl`: unfolding the adjunction and Mathlib's
`CategoryTheory.Adjunction.sheafPushforwardContinuous` with `simp`, then `rfl`, proves it.  Only
the `Type u` form is used here, and that is the universe
`AlgebraicGeometry.Space.smallEtaleDirectImage` and the module development are stated at.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v' w w' u

namespace CategoryTheory.Presheaf

/-- The commutation that a fork built from a cartesian square of a morphism with itself asks
for: if `p, q : Z ⟶ Y` exhibit `Z` as the fibre product of `g : Y ⟶ X` with itself, then for
every presheaf `P` restriction along `g` followed by restriction along `p` agrees with
restriction along `g` followed by restriction along `q`.

It holds because `p ≫ g = q ≫ g`.  It is recorded as a declaration of its own because the
forks of `CategoryTheory.Presheaf.isLimitForkOfSingletonCovering` and its specialisations take
the commutation as an argument, and a fork whose commutation could not be proved would not be
well-formed. -/
theorem fork_condition_of_isPullback {C : Type v} [Category.{v'} C] {A : Type w}
    [Category.{w'} A] (P : Cᵒᵖ ⥤ A) {X Y Z : C} {g : Y ⟶ X} {p q : Z ⟶ Y}
    (hpb : IsPullback p q g g) :
    P.map g.op ≫ P.map p.op = P.map g.op ≫ P.map q.op := by
  rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, hpb.w]

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS} {A : Type w} [Category.{w'} A]

/-! ### The counit is a one-element covering -/

/-- **Stacks 03MH for the cartesian projection of a spaces-étale base change.**  If `h : U ⟶ V`
is étale and surjective on points, then for every object `W` of the spaces-étale site of `V` the
component at `W` of the counit of
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` is surjective on points.

The counit is the cartesian projection `W ×_V U ⟶ W` by
`AlgebraicGeometry.Space.toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`, and the
base-change datum of Stacks 03G2, part (1) asserts that the projection exhibits `W ×_V U` as
the fibre product of the structure morphism of `W` with `h`; so this is stability of
surjectivity on points under base change. -/
theorem isSurjective_toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit
    (h : U ⟶ V) (hh : IsEtale B S hS h.hom) (hsurj : IsSurjective B S hS h.hom)
    (W : SpacesEtale B S hS V) :
    IsSurjective B S hS ((SpacesEtale.toSpaces B S hS V).map
      ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app W)).hom := by
  rw [toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit B S hS h hh W]
  exact surjective_pointsMap_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS
      (((spacesBaseChange B S hS h).isPullback W).flip)) hsurj

/-! ### The equalizer -/

/-- **The sheaf condition of Stacks 03H7 for a surjective étale base change, with restriction
along the counit as its first arrow.**  Let `h : U ⟶ V` be étale and surjective on points, let
`W` be an object of the spaces-étale site of `V`, and let `p, q` exhibit `Z₂` as the fibre
product with itself of the counit `W ×_V U ⟶ W`.  Then for every sheaf `P` on the spaces-étale
site of `V`, with values in an arbitrary category,

`P(W) → P(W ×_V U) ⇉ P(Z₂)`

is an equalizer diagram, the first arrow being restriction along the counit.

This is `AlgebraicGeometry.Space.isLimitForkOfSurjectiveSingleton` for the one-element covering
given by the counit, whose covering condition is
`AlgebraicGeometry.Space.isSurjective_toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit`.
At the universe of the structure rings the first arrow is the component of the unit of
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction`, by
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction_unit_app` on each section. -/
noncomputable def isLimitForkCounit (P : (SpacesEtale B S hS V)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (SpacesEtale.topology B S hS V) P) (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) (hsurj : IsSurjective B S hS h.hom)
    (W : SpacesEtale B S hS V) {Z₂ : SpacesEtale B S hS V}
    {p q : Z₂ ⟶ (spacesEtalePostcomp B S hS h hh).obj
      ((spacesBaseChange B S hS h).functor.obj W)}
    (hpb : IsPullback p q ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app W)
      ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app W)) :
    IsLimit (Fork.ofι
      (P.map ((spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app W).op)
      (Presheaf.fork_condition_of_isPullback P hpb)) :=
  isLimitForkOfSurjectiveSingleton B S hS P hP
    (isSurjective_toSpaces_map_spacesEtalePostcompBaseChangeAdjunction_counit B S hS h hh
      hsurj W) hpb _

end AlgebraicGeometry.Space

end
