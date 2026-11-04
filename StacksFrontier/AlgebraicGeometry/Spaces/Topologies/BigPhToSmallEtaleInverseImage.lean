module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtale

/-!
# The ph–étale comparison squares on inverse images (Stacks 0DGW)

Let `S` be a scheme and `f : Y ⟶ X` a morphism of algebraic spaces over `S`. Stacks 0DGW asserts
that the two squares of topoi
```
Sh((Spaces/Y)_ph) --f_{big,ph}--> Sh((Spaces/X)_ph)
      | ε_Y                              | ε_X
Sh((Spaces/Y)_ét) --f_{big,ét}--> Sh((Spaces/X)_ét)

Sh((Spaces/Y)_ph) --f_{big,ph}--> Sh((Spaces/X)_ph)
      | a_Y                              | a_X
Sh(Y_ét)          --f_{small}-->  Sh(X_ét)
```
commute, where `a = π ∘ ε`. A commutative square of topoi is a pair of compatible
identifications, one of the direct images of the two composites and one of their inverse
images. The direct-image halves are
`AlgebraicGeometry.BigPHSpaceSite.bigPHBigEtale_pushforwardCommIso` and
`AlgebraicGeometry.BigPHSpaceSite.bigPHSmallEtale_pushforwardCommIso`; this file supplies the
inverse-image halves. Since the inverse image of a morphism of topoi is left adjoint to its direct
image, each is the conjugate of the corresponding direct-image isomorphism, and that is what makes
the two halves compatible.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.bigPHBigEtale_inverseImageCommIso`: **Stacks 0DGW**, the
  big ph–big étale square on inverse images, `f_{big,ph}⁻¹ ∘ ε_X⁻¹ ≅ ε_Y⁻¹ ∘ f_{big,ét}⁻¹`.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHSmallEtale_inverseImageCommIso`: **Stacks 0DGW**, the
  big ph–small étale square on inverse images, `f_{big,ph}⁻¹ ∘ a_X⁻¹ ≅ a_Y⁻¹ ∘ f_{small}⁻¹`.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHBigEtale_inverseImageCommIso_conjugate` and
  `.bigPHSmallEtale_inverseImageCommIso_conjugate`: the inverse-image isomorphisms are the
  conjugates of the direct-image ones, so each square commutes as a square of topoi.
* `AlgebraicGeometry.BigPHSpaceSite.bigPHSmallEtaleCharts_inverseImageCommIso`: **Stacks 0DGW**,
  the second square on inverse images for the presentation of the small étale topos by the site
  of scheme charts, where `a⁻¹` is the left adjoint of restriction along the chart functor.

## Implementation notes

The setting is a big ph site of algebraic spaces `P` and a big étale site of algebraic spaces `E`
over the same big fppf site of schemes, so that they topologize the same category of algebraic
spaces.

## References

* [Stacks Project, Tag 0DGW](https://stacks.math.columbia.edu/tag/0DGW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite)

/-- The first diagram, on inverse images. For a morphism `f : Y ⟶ X` of algebraic spaces the
inverse images of `ε_X ∘ f_{big, ph}` and of `f_{big, étale} ∘ ε_Y` are canonically isomorphic:
`f_{big, ph}⁻¹ ∘ ε_X⁻¹ ≅ ε_Y⁻¹ ∘ f_{big, étale}⁻¹`. It is the conjugate of the direct-image
isomorphism `bigPHBigEtale_pushforwardCommIso`. -/
@[stacks 0DGW "the big ph–big étale square, on inverse images"]
def bigPHBigEtale_inverseImageCommIso {X Y : P.Spaces} (f : Y ⟶ X) :
    ((phToBigEtaleMorphism P E h X).comp (bigPHMorphism P f)).inverseImage ≅
      ((E.bigEtaleMorphism (etaleMap P E h f)).comp (phToBigEtaleMorphism P E h Y)).inverseImage :=
  (conjugateIsoEquiv
    ((E.bigEtaleMorphism (etaleMap P E h f)).comp (phToBigEtaleMorphism P E h Y)).adj
    ((phToBigEtaleMorphism P E h X).comp (bigPHMorphism P f)).adj).symm
      (bigPHBigEtale_pushforwardCommIso P E h f)

/-- The inverse-image isomorphism of the first diagram is the conjugate of its direct-image
isomorphism: the two halves form one commutative square of topoi. -/
theorem bigPHBigEtale_inverseImageCommIso_conjugate {X Y : P.Spaces} (f : Y ⟶ X) :
    conjugateIsoEquiv
        ((E.bigEtaleMorphism (etaleMap P E h f)).comp (phToBigEtaleMorphism P E h Y)).adj
        ((phToBigEtaleMorphism P E h X).comp (bigPHMorphism P f)).adj
        (bigPHBigEtale_inverseImageCommIso P E h f) =
      bigPHBigEtale_pushforwardCommIso P E h f :=
  Equiv.apply_symm_apply _ _

/-- The second diagram, on inverse images. For a morphism `f : Y ⟶ X` of algebraic spaces the
inverse images of `a_X ∘ f_{big, ph}` and of `f_{small} ∘ a_Y` are canonically isomorphic:
`f_{big, ph}⁻¹ ∘ a_X⁻¹ ≅ a_Y⁻¹ ∘ f_{small}⁻¹`, where `a = π ∘ ε`. It is the conjugate of the
direct-image isomorphism `bigPHSmallEtale_pushforwardCommIso`. -/
@[stacks 0DGW "the big ph–small étale square, on inverse images"]
def bigPHSmallEtale_inverseImageCommIso {X Y : P.Spaces} (f : Y ⟶ X) :
    ((phToSmallEtaleMorphism P E h X).comp (bigPHMorphism P f)).inverseImage ≅
      ((E.smallEtaleMorphism (etaleMap P E h f)).comp
        (phToSmallEtaleMorphism P E h Y)).inverseImage :=
  (conjugateIsoEquiv
    ((E.smallEtaleMorphism (etaleMap P E h f)).comp (phToSmallEtaleMorphism P E h Y)).adj
    ((phToSmallEtaleMorphism P E h X).comp (bigPHMorphism P f)).adj).symm
      (bigPHSmallEtale_pushforwardCommIso P E h f)

/-- The inverse-image isomorphism of the second diagram is the conjugate of its direct-image
isomorphism: the two halves form one commutative square of topoi. -/
theorem bigPHSmallEtale_inverseImageCommIso_conjugate {X Y : P.Spaces} (f : Y ⟶ X) :
    conjugateIsoEquiv
        ((E.smallEtaleMorphism (etaleMap P E h f)).comp (phToSmallEtaleMorphism P E h Y)).adj
        ((phToSmallEtaleMorphism P E h X).comp (bigPHMorphism P f)).adj
        (bigPHSmallEtale_inverseImageCommIso P E h f) =
      bigPHSmallEtale_pushforwardCommIso P E h f :=
  Equiv.apply_symm_apply _ _

/-! ### The small étale site of scheme charts -/

/-- The second diagram on inverse images, for the presentation of the small étale topos by the
site of scheme charts. For a morphism `f : X ⟶ Y` of algebraic spaces of the ph site, with `a` the
restriction along the chart functor `smallEtaleToPH` and `a⁻¹` its left adjoint,
`f_{big, ph}⁻¹ ∘ a_Y⁻¹ ≅ a_X⁻¹ ∘ f_{small}⁻¹`. It is the conjugate of the direct-image isomorphism
`bigPHSmallEtaleCharts_pushforwardCommIso`. -/
@[stacks 0DGW "the big ph–small étale square, for the small étale site of scheme charts, \
  on inverse images"]
def bigPHSmallEtaleCharts_inverseImageCommIso {X Y : P.Spaces} (f : X ⟶ Y) :
    (smallEtaleToPH P Y).sheafPullback (Type (u + 1))
        (Space.SmallEtale.topology P.fppfSite S P.fppf_mem Y.1)
        (BigPHSpaceOver.topology P Y) ⋙ (bigPHMorphism P f).inverseImage ≅
      (Space.smallToposMorphism P.fppfSite S P.fppf_mem f).inverseImage ⋙
        (smallEtaleToPH P X).sheafPullback (Type (u + 1))
          (Space.SmallEtale.topology P.fppfSite S P.fppf_mem X.1)
          (BigPHSpaceOver.topology P X) :=
  (conjugateIsoEquiv
    ((Space.smallToposMorphism P.fppfSite S P.fppf_mem f).adj.comp
      ((smallEtaleToPH P X).sheafAdjunctionContinuous (Type (u + 1))
        (Space.SmallEtale.topology P.fppfSite S P.fppf_mem X.1)
        (BigPHSpaceOver.topology P X)))
    (((smallEtaleToPH P Y).sheafAdjunctionContinuous (Type (u + 1))
        (Space.SmallEtale.topology P.fppfSite S P.fppf_mem Y.1)
        (BigPHSpaceOver.topology P Y)).comp (bigPHMorphism P f).adj)).symm
      (bigPHSmallEtaleCharts_pushforwardCommIso P f)

/-- The inverse-image isomorphism of the chart square is the conjugate of its direct-image
isomorphism. -/
theorem bigPHSmallEtaleCharts_inverseImageCommIso_conjugate {X Y : P.Spaces} (f : X ⟶ Y) :
    conjugateIsoEquiv
        ((Space.smallToposMorphism P.fppfSite S P.fppf_mem f).adj.comp
          ((smallEtaleToPH P X).sheafAdjunctionContinuous (Type (u + 1))
            (Space.SmallEtale.topology P.fppfSite S P.fppf_mem X.1)
            (BigPHSpaceOver.topology P X)))
        (((smallEtaleToPH P Y).sheafAdjunctionContinuous (Type (u + 1))
            (Space.SmallEtale.topology P.fppfSite S P.fppf_mem Y.1)
            (BigPHSpaceOver.topology P Y)).comp (bigPHMorphism P f).adj)
        (bigPHSmallEtaleCharts_inverseImageCommIso P f) =
      bigPHSmallEtaleCharts_pushforwardCommIso P f :=
  Equiv.apply_symm_apply _ _

end AlgebraicGeometry.BigPHSpaceSite

end
