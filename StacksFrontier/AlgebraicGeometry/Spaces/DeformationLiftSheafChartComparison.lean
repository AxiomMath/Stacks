module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafDescent

/-!
# The two spellings of the sheaf of lifts agree

The lifts of a morphism of algebraic spaces along a thickening form a sheaf on two sites. On the
spaces-étale site of `X'` they are `AlgebraicGeometry.Space.liftSubfunctor`, cut out by
`AlgebraicGeometry.Space.IsLiftOver`. On the small étale site of `X'` — the site of étale
*scheme* charts — they are `AlgebraicGeometry.Space.liftsSubfunctor`, cut out by
`AlgebraicGeometry.Space.IsChartLift`.

This file identifies the two along the comparison `AlgebraicGeometry.Space.comparisonFunctor` of
Stacks 03G1: the two lifting conditions agree on a scheme chart.

## Main results

* `AlgebraicGeometry.Space.isLiftOver_comparisonFunctor_iff_isChartLift`: on a scheme chart of
  `X'`, read as an algebraic space étale over `X'` by Stacks 03G1, the lifting condition of
  `IsLiftOver` and the lifting condition of `IsChartLift` are the same condition.
* `AlgebraicGeometry.Space.existsUnique_hom_of_isLiftOver_family`: a family of lifts indexed by
  the spaces-étale site of `X'` and compatible with restriction — that is, a global section of
  `AlgebraicGeometry.Space.liftSubfunctor` — is the family of restrictions of exactly one
  morphism `X' ⟶ Y'` lying over `T` and restricting to `a` on `X`.

## Implementation notes

The two conditions differ in exactly one place. Being a morphism over the base is literally the
same equation on both sides: the structure morphism of `comparisonFunctor.obj U'` is the chart
itself, and a morphism of algebraic spaces is an equation of its underlying transformations.

In the restriction clause `IsLiftOver` reads `U = X ×_{X'} U'` as the base change
`AlgebraicGeometry.Space.spacesBaseChange` along the inclusion of the thickening, whereas
`IsChartLift` reads it — through `AlgebraicGeometry.Space.isChartLift_iff_restrict` — as the
preimage subfunctor `CategoryTheory.Subfunctor.preimage`. Both are fibre products of the same
cospan, the second by Stacks 083Q.

The target is not restricted. `IsLiftOver` lifts into `Y'` the restriction of
`a : X ⟶ Y` along a thickening `Y ⊆ Y'`, while `IsChartLift` lifts a morphism into a single
algebraic space; the two agree with the morphism into `Y'` taken to be
`a ≫ IsThickening.inclusion hH`, which is the shape in which `IsLiftOver` uses `a` as well.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- An equation between the two legs of one cartesian square holds on the corner of any other
cartesian square over the same cospan. -/
private theorem comp_eq_comp_of_isPullback {𝒞 : Type*} [Category 𝒞] {P P' A A' Z W : 𝒞}
    {u : P ⟶ A} {v : P ⟶ A'} {u' : P' ⟶ A} {v' : P' ⟶ A'} {f : A ⟶ Z} {g : A' ⟶ Z}
    (h : IsPullback u v f g) (h' : IsPullback u' v' f g)
    {r : A ⟶ W} {s : A' ⟶ W} (hrs : u ≫ r = v ≫ s) :
    u' ≫ r = v' ≫ s := by
  rw [← h.lift_fst u' v' h'.w, Category.assoc, hrs, ← Category.assoc, h.lift_snd]

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}
  (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)

/-- **The two spellings of the lifting condition agree.** Let `X ⊆ X'` and `Y ⊆ Y'` be
thickenings of algebraic spaces over `T` and let `a : X ⟶ Y` be a morphism. An étale scheme
chart `U'` of `X'` is an algebraic space étale over `X'` by Stacks 03G1, and a morphism from it
into `Y'` is a lift of `a` in the sense of `AlgebraicGeometry.Space.IsLiftOver` exactly when its
underlying transformation is a lift of `a ≫ (Y ⟶ Y')` in the sense of
`AlgebraicGeometry.Space.IsChartLift`. -/
theorem isLiftOver_comparisonFunctor_iff_isChartLift (U' : SmallEtale C S hS X'.obj)
    (a' : (SpacesEtale.toSpaces C S hS X').obj ((comparisonFunctor C S hS X').obj U') ⟶ Y') :
    IsLiftOver C S hS hG hH pX' pY' a ((comparisonFunctor C S hS X').obj U') a' ↔
      IsChartLift C S hS pX' pY' (a ≫ IsThickening.inclusion C S hS hH).hom U' a'.hom := by
  have hsq1 := AlgebraicSpaces.isPullback_hom C S hS
    ((spacesBaseChange C S hS (IsThickening.inclusion C S hS hG)).isPullback
      ((comparisonFunctor C S hS X').obj U'))
  have hsq2 := (Subfunctor.isPullback_preimage U'.obj.hom G).flip
  refine Iff.trans ?_ (isChartLift_iff_restrict C S hS pX' pY' (X := G)
    (a ≫ IsThickening.inclusion C S hS hH).hom U' a'.hom).symm
  constructor
  · intro h
    exact ⟨congrArg (fun k => k.hom) h.1,
      comp_eq_comp_of_isPullback hsq1 hsq2 (congrArg (fun k => k.hom) h.2)⟩
  · intro h
    exact ⟨ObjectProperty.hom_ext _ h.1,
      ObjectProperty.hom_ext _ (comp_eq_comp_of_isPullback hsq2 hsq1 h.2)⟩

/-- **A family of lifts indexed by the spaces-étale site descends to a global lift.** A rule
assigning to every algebraic space `U'` étale over `X'` a lift `α U' : U' ⟶ Y'` of `a`,
compatibly with the morphisms of that site — that is, a global section of
`AlgebraicGeometry.Space.liftSubfunctor` — is the family of restrictions of exactly one morphism
`X'.1 ⟶ Y'.1`, and that morphism lies over `T` and restricts to `a` on `X`. -/
theorem existsUnique_hom_of_isLiftOver_family
    (α : ∀ U' : SpacesEtale C S hS X', (SpacesEtale.toSpaces C S hS X').obj U' ⟶ Y')
    (hα : ∀ U', IsLiftOver C S hS hG hH pX' pY' a U' (α U'))
    (hcompat : ∀ {U' V' : SpacesEtale C S hS X'} (k : V' ⟶ U'),
      (SpacesEtale.toSpaces C S hS X').map k ≫ α U' = α V') :
    ∃! b : X'.obj ⟶ Y'.obj,
      (∀ W : SmallEtale C S hS X'.obj,
          W.obj.hom ≫ b = (α ((comparisonFunctor C S hS X').obj W)).hom) ∧
        b ≫ pY'.hom = pX'.hom ∧
          G.ι ≫ b = (a ≫ IsThickening.inclusion C S hS hH).hom :=
  existsUnique_hom_of_isChartLift_family C S hS pX' pY'
    (a ≫ IsThickening.inclusion C S hS hH).hom
    (fun W => (α ((comparisonFunctor C S hS X').obj W)).hom)
    (fun W => (isLiftOver_comparisonFunctor_iff_isChartLift C S hS hG hH pX' pY' a W
      (α ((comparisonFunctor C S hS X').obj W))).1 (hα _))
    (fun {_ _} m => congrArg (fun k => k.hom)
      (hcompat ((comparisonFunctor C S hS X').map m)))

end AlgebraicGeometry.Space

end
