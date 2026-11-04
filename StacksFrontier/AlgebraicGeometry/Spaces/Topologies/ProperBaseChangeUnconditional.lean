module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleFinitePushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper base change for algebraic spaces and the big and small étale topoi, unconditionally

From the proper base change theorem for sheaves of sets on schemes (Stacks 0A3U,
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`) we obtain:

* effective descent of small étale sheaves along a proper surjection of schemes (Stacks 0GF0);
* that the pseudofunctor of spaces-étale inverse images is a prestack along proper surjections of
  representable algebraic spaces;
* proper base change for sheaves of sets on algebraic spaces (Stacks 0DG0);
* the comparison `π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` for `f` proper (Stacks 0DGD, part (1)),
  and its abelian form.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleSetBaseChange_of_isProper_forall`: Stacks 0A3U in the form
  the conditional statements take it.
* `AlgebraicGeometry.smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper`:
  effective descent along a proper surjection (Stacks 0GF0).
* `AlgebraicGeometry.Space.properSurjectivePrestackOverSchemes`: the prestack property along proper
  surjections of representable algebraic spaces.
* `AlgebraicGeometry.Space.spacesToposBaseChangeSquare_isIso_of_isProper`: Stacks 0DG0.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtalePushforwardIsoOfIsProper`: Stacks 0DGD,
  part (1).
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleAbelianPushforwardIsoOfIsProper`: its
  abelian form.

## Implementation notes

The derived form of Stacks 0DGD, part (3), is
`AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedPushforwardIsoOfIsFinite` applied to
`AlgebraicGeometry.isIso_smallEtaleSetBaseChange_of_isProper_forall`.

## References

* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0A3U**, in the form taken by the statements conditional on it: for every cartesian
square of schemes whose right-hand side is proper, the base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹`
of sheaves of sets on the small étale sites is an isomorphism. -/
theorem isIso_smallEtaleSetBaseChange_of_isProper_forall
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (hf : IsProper f) :
    IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w) :=
  Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq

/-- **Effective descent of small étale sheaves along a proper surjection** (Stacks 0GF0). For a
surjective proper morphism `f : X ⟶ Y` of a big étale site, the functor sending a sheaf of sets
on the small étale site of `Y` to its canonical descent datum along `f` is an equivalence. -/
@[sga "4 VIII 9.4"]
theorem smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper
    (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [Surjective (B.inclusion.map f)] [IsProper (B.inclusion.map f)] :
    (smallEtaleSheafInverseImageDescentFunctor B f).IsEquivalence :=
  smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange
    B f isIso_smallEtaleSetBaseChange_of_isProper_forall

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The spaces-étale inverse images form a prestack along proper surjections of representable
algebraic spaces**: for every proper surjection of schemes of the big fppf site of `S`, the
pseudofunctor of spaces-étale inverse images is a prestack for the sieve it generates among
representable algebraic spaces. -/
theorem properSurjectivePrestackOverSchemes : ProperSurjectivePrestackOverSchemes B S hS :=
  properSurjectivePrestackOverSchemes_of_properBaseChange B S hS
    isIso_smallEtaleSetBaseChange_of_isProper_forall

/-- **Proper base change for sheaves of sets on algebraic spaces** (Stacks 0DG0). Let
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
be a cartesian square of algebraic spaces over `S` with `f` proper. Then the base change map
`g⁻¹ f_* ⟶ f'_* (g')⁻¹` of spaces-étale sheaves of sets is invertible. -/
theorem spacesToposBaseChangeSquare_isIso_of_isProper
    ⦃X Y X' Y' : AlgebraicSpaces B S hS⦄ (f : Y ⟶ X) (hf : IsProper B S hS f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g) :
    IsIso (spacesToposBaseChangeSquare B S hS g' f' f g sq) :=
  isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange B S hS
    isIso_smallEtaleSetBaseChange_of_isProper_forall f hf g g' f' sq

end Space

namespace BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- **Stacks 0DGD, part (1), as invertibility of the base change map.** For a proper morphism
`f : Y ⟶ X` of algebraic spaces of the big étale site, the canonical map
`π_X⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_Y⁻¹` is an isomorphism. -/
theorem isIso_bigToSmallEtaleBaseChange_of_isProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom) :
    IsIso (bigToSmallEtaleBaseChange T f) :=
  isIso_bigToSmallEtaleBaseChange T f hf isIso_smallEtaleSetBaseChange_of_isProper_forall

/-- **Stacks 0DGD, part (1).** For a proper morphism `f : Y ⟶ X` of algebraic spaces of the big
étale site, the canonical base change map is an isomorphism of functors
`π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` from sheaves of sets on the spaces-étale site of `Y` to
sheaves on the big étale site of `X`. -/
def bigToSmallEtalePushforwardIsoOfIsProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom) :
    (smallEtaleMorphism T f).pushforward ⋙ (bigToSmallEtaleMorphism T X).inverseImage ≅
      (bigToSmallEtaleMorphism T Y).inverseImage ⋙ (bigEtaleMorphism T f).pushforward :=
  bigToSmallEtalePushforwardIso T f hf isIso_smallEtaleSetBaseChange_of_isProper_forall

/-- **Stacks 0DGD, part (1), for abelian sheaves.** For a proper morphism `f : Y ⟶ X` of
algebraic spaces of the big étale site, `π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` on abelian
sheaves. -/
def bigToSmallEtaleAbelianPushforwardIsoOfIsProper {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom) :
    smallEtalePushforward T f ⋙
        CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X) ≅
      CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T Y) ⋙
        bigEtalePushforward T f :=
  bigToSmallEtaleAbelianPushforwardIso T f hf isIso_smallEtaleSetBaseChange_of_isProper_forall


end BigEtaleSpaceSite

end AlgebraicGeometry

end
