module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# Stalks of the inverse image of abelian sheaves on the small étale site of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose underlying morphism of
presheaves is representable, and let `x` be a geometric point of `X`. The stalk at `x` of the
inverse image along `f` of an abelian sheaf on the small étale site of `Y` is the stalk of that
sheaf at the image geometric point `f ∘ x`, naturally in the sheaf. This is part (4) of Stacks
04K2 with coefficients in abelian groups rather than in sets.

## Main results

* `AlgebraicGeometry.Space.etaleSitePointStalkFunctorIso`: the stalk at the point of the small
  étale site of Stacks 04K0 is the geometric stalk of Stacks 04JY, for coefficients in any
  category with colimits of the size of the site. This generalizes
  `AlgebraicGeometry.Space.etaleSitePointStalkIso`, which is stated at `Type (u + 1)`.
* `AlgebraicGeometry.Space.spacesComparisonSheafFiberIso`: the fibre at a geometric point of a
  sheaf on the spaces-étale site is the fibre of its restriction along the comparison functor
  of Stacks 03G1, at the same generality. This generalizes
  `AlgebraicGeometry.Space.spacesEtaleSitePointSheafFiberIso`.
* `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageStalkIso`: Stacks 04K2, part (4), for
  abelian sheaves and the inverse image of a representable morphism.
* `AlgebraicGeometry.Space.preservesFiniteLimits_smallEtaleAbelianInverseImage`: that inverse
  image is left exact.

## Implementation notes

Both stalk comparisons are instances of one fact: the fibre functor of a point of a site and
the geometric stalk are colimits of the same sections along two indexing categories, and the
comparison between the two indexings is initial. So each is
`CategoryTheory.Functor.Final.colimIso` whiskered into the common diagram, with no computation
on germs and hence no restriction on the coefficients; the `Type (u + 1)` versions they
generalize instead compare quotient colimits of sets by hand.

The inverse image itself is not treated on the small étale sites, where base change along `f`
is not representably flat for want of a terminal object — an algebraic space is not one of its
own scheme charts. It is treated on the spaces-étale sites, where the identity chart is
terminal (`AlgebraicGeometry.Space.SpacesEtale.isTerminal_idObj`) and base change therefore
preserves finite limits, so that Stacks 05V1 in the form of
`CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` applies. The descent to the
small étale sites is by uniqueness of adjoints: restriction along the comparison functor of
Stacks 03G1 is an equivalence on sheaves with any coefficients, the comparison square of
Stacks 03G2, part (4), identifies the two direct images, and conjugating that identification
gives the corresponding identification of inverse images.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04JZ](https://stacks.math.columbia.edu/tag/04JZ)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace CategoryTheory.Limits

/-- Restricting a diagram along a final functor does not change its colimit, as an isomorphism
of functors on the diagrams themselves: the two indexings of the same sections compute the same
colimit. -/
@[sga "4 I 8.2.3" "more general"]
def colimIsoOfFinalPrecomp {I : Type*} [Category* I] {J : Type*} [Category* J]
    {C : Type*} [Category* C] {A : Type*} [Category* A] (Φ : J ⥤ C) (H : I ⥤ J) [H.Final]
    [HasColimitsOfShape I A] [HasColimitsOfShape J A] :
    (Functor.whiskeringLeft I C A).obj (H ⋙ Φ) ⋙ colim ≅
      (Functor.whiskeringLeft J C A).obj Φ ⋙ colim :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft J C A).obj Φ) (Functor.Final.colimIso H)

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The stalk at the point of the small étale site -/

section SmallSite

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {A : Type v} [Category.{w} A]
  [HasColimitsOfSize.{u, u} A]

/-- **Stacks 04K0.** The stalk at the point of the small étale site determined by a geometric
point is the geometric stalk of Stacks 04JY, naturally in the presheaf, for coefficients in any
category with colimits of the size of the site.

A lift of the geometric point into an étale chart is the same data as a small étale
neighbourhood of the point, so the two diagrams of sections are the same functor read along an
equivalence of indexing categories. -/
def etaleSitePointStalkFunctorIso (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A] :
    (etaleSitePoint B S hS F x hF).presheafFiber (A := A) ≅ stalkFunctor A x :=
  haveI : HasColimitsOfShape (geometricFiber B S hS F x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (etaleSitePoint B S hS F x hF).fiber.Elementsᵒᵖ A)
  haveI : (neighborhoodFiberElementsEquiv B S hS F x).functor.Initial := inferInstance
  (colimIsoOfFinalPrecomp (Functor.Elements.π (geometricFiber B S hS F x)).op
    (neighborhoodFiberElementsEquiv B S hS F x).functor.op).symm

end SmallSite

/-! ### The fibre of the point of the spaces-étale site -/

section Comparison

variable {X : AlgebraicSpaces B S hS} (x : GeometricPoint B S hS X.1) {A : Type v}
  [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- A lift of a geometric point into an étale scheme chart, read as a lift into an algebraic
space étale over `X`: a small étale neighbourhood is an étale neighbourhood, and an étale
neighbourhood is an object of the spaces-étale site with a lift of the point. -/
def smallToSpacesFiberElements :
    (geometricFiber B S hS X.1 x).Elements ⥤ (spacesGeometricFiber x).Elements :=
  fiberElementsToNeighborhood B S hS X.1 x ⋙
    EtaleNeighborhood.ofSmallEtale X.2 x ⋙ (spacesFiberElementsEquiv x).inverse

/-- The object of the spaces-étale site underlying the lift of the geometric point attached to
a lift into an étale scheme chart is the comparison functor of Stacks 03G1 applied to that
chart, so the two diagrams of sections are the same functor. -/
theorem smallToSpacesFiberElements_comp_π :
    smallToSpacesFiberElements B S hS x ⋙ Functor.Elements.π (spacesGeometricFiber x) =
      Functor.Elements.π (geometricFiber B S hS X.1 x) ⋙ comparisonFunctor B S hS X := rfl

/-- The lifts of a geometric point into the étale scheme charts are initial among its lifts
into the algebraic spaces étale over `X`, because the small étale neighbourhoods are initial
among all étale neighbourhoods. -/
instance : (smallToSpacesFiberElements B S hS x).Initial := by
  have : (fiberElementsToNeighborhood B S hS X.1 x).Initial :=
    inferInstanceAs (neighborhoodFiberElementsEquiv B S hS X.1 x).inverse.Initial
  have : ((EtaleNeighborhood.ofSmallEtale X.2 x) ⋙
      (spacesFiberElementsEquiv x).inverse).Initial := inferInstance
  exact inferInstanceAs (Functor.Initial (fiberElementsToNeighborhood B S hS X.1 x ⋙
    EtaleNeighborhood.ofSmallEtale X.2 x ⋙ (spacesFiberElementsEquiv x).inverse))

/-- **Stacks 04JZ.** The fibre at a geometric point of a presheaf on the spaces-étale site of
`X` is the fibre at the corresponding point of the small étale site of its restriction along
the comparison functor of Stacks 03G1, naturally in the presheaf. -/
def spacesComparisonPresheafFiberIso (hX : IsAlgebraicSpace B S hS X.1) :
    (spacesEtaleSitePoint x).presheafFiber (A := A) ≅
      (Functor.whiskeringLeft (SmallEtale B S hS X.1)ᵒᵖ (SpacesEtale B S hS X)ᵒᵖ A).obj
          (comparisonFunctor B S hS X).op ⋙
        (etaleSitePoint B S hS X.1 x hX).presheafFiber :=
  haveI : HasColimitsOfShape (spacesGeometricFiber x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (spacesEtaleSitePoint x).fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape (geometricFiber B S hS X.1 x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (etaleSitePoint B S hS X.1 x hX).fiber.Elementsᵒᵖ A)
  (colimIsoOfFinalPrecomp (Functor.Elements.π (spacesGeometricFiber x)).op
    (smallToSpacesFiberElements B S hS x).op).symm

/-- **Stacks 04JZ.** The fibre at a geometric point of a sheaf on the spaces-étale site of `X`
is the fibre of its restriction along the comparison functor of Stacks 03G1, naturally in the
sheaf, for coefficients in any category with colimits of the size of the site.

This generalizes `AlgebraicGeometry.Space.spacesEtaleSitePointSheafFiberIso`, which is stated
at `Type (u + 1)`. -/
def spacesComparisonSheafFiberIso (hX : IsAlgebraicSpace B S hS X.1) :
    (spacesEtaleSitePoint x).sheafFiber (A := A) ≅
      (comparisonFunctor B S hS X).sheafPushforwardContinuous A
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
        (etaleSitePoint B S hS X.1 x hX).sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf (SpacesEtale.topology B S hS X) A)
      (spacesComparisonPresheafFiberIso B S hS x hX) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      ((comparisonFunctor B S hS X).sheafPushforwardContinuousCompSheafToPresheafIso A
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).symm _ ≪≫
    Functor.associator ..

end Comparison

/-! ### The inverse image of abelian sheaves and its stalks -/

section InverseImage

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hf : yoneda.relativelyRepresentable f.hom)

/-- Left Kan extensions of abelian presheaves along the opposite of spaces-étale base change
exist. Instance search finds each one but not the universally quantified family that
`CategoryTheory.Functor.lan` asks for, which this instance supplies. -/
instance hasLeftKanExtension_spacesBaseChange_op
    (F : (SpacesEtale B S hS Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (spacesBaseChange B S hS f).functor.op.HasLeftKanExtension F :=
  inferInstance

/-- Restriction of abelian sheaves along spaces-étale base change has a left adjoint, built from
left Kan extension and sheafification. -/
instance isRightAdjoint_sheafPushforwardContinuous_spacesBaseChange_addCommGrpCat :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).IsRightAdjoint :=
  letI : ∀ F : (SpacesEtale B S hS Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (spacesBaseChange B S hS f).functor.op.HasLeftKanExtension F := fun _ => inferInstance
  inferInstance

/-- Restriction of abelian sheaves along base change of scheme charts has a left adjoint, built
from left Kan extension and sheafification. -/
instance isRightAdjoint_sheafPushforwardContinuous_smallBaseChange_addCommGrpCat :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((smallBaseChange B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).IsRightAdjoint :=
  letI := isContinuous_smallBaseChange B S hS f hf
  letI : ∀ F : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallBaseChange B S hS f hf).op.HasLeftKanExtension F := fun _ => inferInstance
  inferInstance

/-- Direct-image comparison of the small and spaces-étale cartesian squares of Stacks 03G2,
part (4), for sheaves with coefficients in an arbitrary category: restriction along base change
of scheme charts, read through the comparison equivalences of Stacks 03G1, is restriction along
base change of étale algebraic spaces. -/
def smallBaseChangePushforwardComparison (A : Type v) [Category.{w} A] :
    letI := isContinuous_smallBaseChange B S hS f hf
    (comparisonFunctor B S hS X).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) ≅
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
      (comparisonFunctor B S hS Y).sheafPushforwardContinuous A
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  letI := Functor.isContinuous_comp (smallBaseChange B S hS f hf) (comparisonFunctor B S hS X)
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X)
  letI := Functor.isContinuous_comp (comparisonFunctor B S hS Y)
    (spacesBaseChange B S hS f).functor (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  Functor.sheafPushforwardContinuousComp (smallBaseChange B S hS f hf)
      (comparisonFunctor B S hS X) A (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ≪≫
    Functor.sheafPushforwardContinuousIso (smallBaseChange_comparison B S hS f hf) A
      (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) ≪≫
    (Functor.sheafPushforwardContinuousComp (comparisonFunctor B S hS Y)
      (spacesBaseChange B S hS f).functor A (SmallEtale.topology B S hS Y.1)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).symm

/-- **Stacks 04K2, part (4), for abelian sheaves.** For a morphism `f : X ⟶ Y` of algebraic
spaces over `S` with representable underlying morphism and a geometric point `x` of `X`, the
stalk at `x` of the inverse image of an abelian sheaf on the small étale site of `Y` is the
stalk of that sheaf at the image geometric point `f ∘ x`, naturally in the sheaf. -/
@[stacks 04K2 "stalk_pullback, abelian sheaves"]
def smallEtaleAbelianInverseImageStalkIso (x : GeometricPoint B S hS X.1) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (smallBaseChange B S hS f hf).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) ⋙
        sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⋙
          stalkFunctor AddCommGrpCat.{u + 1} x ≅
      sheafToPresheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} ⋙
        stalkFunctor AddCommGrpCat.{u + 1} (geometricPointMap f.hom x) := by
  letI := isContinuous_smallBaseChange B S hS f hf
  let A := AddCommGrpCat.{u + 1}
  let JX := SmallEtale.topology B S hS X.1
  let JY := SmallEtale.topology B S hS Y.1
  let KX := SpacesEtale.topology B S hS X
  let KY := SpacesEtale.topology B S hS Y
  let v := smallBaseChange B S hS f hf
  let g := (spacesBaseChange B S hS f).functor
  let y := geometricPointMap f.hom x
  let q := etaleSitePoint B S hS X.1 x X.2
  let p := etaleSitePoint B S hS Y.1 y Y.2
  let Px := spacesEtaleSitePoint x
  let Py := spacesEtaleSitePoint y
  haveI : HasColimitsOfShape (geometricFiber B S hS X.1 x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape q.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A :=
    hasColimitsOfShape_of_equivalence (neighborhoodFiberElementsEquiv B S hS X.1 x).op.symm
  haveI : HasColimitsOfShape (geometricFiber B S hS Y.1 y).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape p.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape (SmallEtaleNeighborhood y)ᵒᵖ A :=
    hasColimitsOfShape_of_equivalence (neighborhoodFiberElementsEquiv B S hS Y.1 y).op.symm
  letI : RepresentablyFlat g := representablyFlat_spacesBaseChange B S hS f
  let hcover : CoverPreserving KY KX g := CoverPreserving.of_isContinuous g KY KX
  let efib : g ⋙ Px.fiber ≅ Py.fiber := spacesBaseChangeFiberIso B S hS f x
  haveI : InitiallySmall.{u} (g ⋙ Px.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  let Pxg := Px.comap g hcover
  haveI : HasColimitsOfShape (g ⋙ Px.fiber).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape Pxg.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape Py.fiber.Elementsᵒᵖ A := inferInstance
  let cXstar := (comparisonFunctor B S hS X).sheafPushforwardContinuous A JX KX
  let cYstar := (comparisonFunctor B S hS Y).sheafPushforwardContinuous A JY KY
  haveI : cXstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X A
  haveI : cYstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS Y A
  let eX := cXstar.asEquivalence
  let eY := cYstar.asEquivalence
  -- The fibre of the base-changed point is the fibre at the image point.
  let eComap : Pxg.sheafFiber (A := A) ≅ g.sheafPullback A KY KX ⋙ Px.sheafFiber :=
    Px.sheafFiberComapIso g hcover A
  let eBase : Pxg.sheafFiber (A := A) ≅ Py.sheafFiber :=
    Functor.isoWhiskerLeft (sheafToPresheaf KY A)
      (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients efib)
  -- The small-site fibres are the spaces-site fibres, read through Stacks 03G1.
  let eQ : q.sheafFiber (A := A) ≅ eX.inverse ⋙ Px.sheafFiber :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight eX.counitIso.symm _ ≪≫ Functor.associator .. ≪≫
      Functor.isoWhiskerLeft eX.inverse (spacesComparisonSheafFiberIso B S hS x X.2).symm
  let eP : eY.inverse ⋙ Py.sheafFiber ≅ p.sheafFiber :=
    Functor.isoWhiskerLeft eY.inverse (spacesComparisonSheafFiberIso B S hS y Y.2) ≪≫
      (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso _ ≪≫ Functor.leftUnitor _
  -- Conjugating the comparison of direct images gives the comparison of inverse images.
  let ePull : v.sheafPullback A JY JX ⋙ eX.inverse ≅ eY.inverse ⋙ g.sheafPullback A KY KX :=
    (conjugateIsoEquiv (eY.symm.toAdjunction.comp (g.sheafAdjunctionContinuous A KY KX))
      ((v.sheafAdjunctionContinuous A JY JX).comp eX.symm.toAdjunction)).symm
      (smallBaseChangePushforwardComparison B S hS f hf A).symm
  let eFiber : v.sheafPullback A JY JX ⋙ q.sheafFiber ≅ p.sheafFiber :=
    Functor.isoWhiskerLeft _ eQ ≪≫ (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight ePull _ ≪≫ Functor.associator .. ≪≫
      Functor.isoWhiskerLeft eY.inverse (eComap.symm ≪≫ eBase) ≪≫ eP
  exact Functor.isoWhiskerLeft (v.sheafPullback A JY JX)
      (Functor.isoWhiskerLeft (sheafToPresheaf JX A)
        (etaleSitePointStalkFunctorIso B S hS X.1 x X.2).symm) ≪≫
    eFiber ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf JY A)
      (etaleSitePointStalkFunctorIso B S hS Y.1 y Y.2)

/-- The left Kan extension along base change of étale algebraic spaces is left exact on
presheaves of abelian groups: base change is representably flat, so the costructured-arrow
categories computing the extension pointwise are filtered, and filtered colimits of abelian
groups are exact. -/
theorem preservesFiniteLimits_spacesBaseChange_op_lan :
    PreservesFiniteLimits
      ((spacesBaseChange B S hS f).functor.op.lan (H := AddCommGrpCat.{u + 1}) :
        ((SpacesEtale B S hS Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})) := by
  let : RepresentablyFlat (spacesBaseChange B S hS f).functor :=
    representablyFlat_spacesBaseChange B S hS f
  have : PreservesFilteredColimitsOfSize.{u + 1, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u + 1, u + 1} _
  refine Stacks.Topology.lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u + 1})
    (spacesBaseChange B S hS f).functor (fun Z => ?_)
  have : IsFiltered (CostructuredArrow (spacesBaseChange B S hS f).functor.op Z) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (spacesBaseChange B S hS f).functor (Opposite.unop Z))
  infer_instance

/-- **Stacks 04K2, part (1).** The inverse image of abelian sheaves along a morphism of
algebraic spaces with representable underlying morphism is left exact.

Base change of scheme charts is not representably flat, for want of a terminal object on the
small étale site; left exactness is instead inherited from base change of étale algebraic
spaces through the equivalences of Stacks 03G1. -/
@[stacks 04K2 "part (1): finite limits"]
theorem preservesFiniteLimits_smallEtaleAbelianInverseImage :
    letI := isContinuous_smallBaseChange B S hS f hf
    PreservesFiniteLimits ((smallBaseChange B S hS f hf).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)) := by
  let := isContinuous_smallBaseChange B S hS f hf
  let A := AddCommGrpCat.{u + 1}
  let JX := SmallEtale.topology B S hS X.1
  let JY := SmallEtale.topology B S hS Y.1
  let KX := SpacesEtale.topology B S hS X
  let KY := SpacesEtale.topology B S hS Y
  let v := smallBaseChange B S hS f hf
  let g := (spacesBaseChange B S hS f).functor
  let : RepresentablyFlat g := representablyFlat_spacesBaseChange B S hS f
  have : PreservesFiniteLimits (g.op.lan (H := A) : ((SpacesEtale B S hS Y)ᵒᵖ ⥤ A) ⥤
      ((SpacesEtale B S hS X)ᵒᵖ ⥤ A)) :=
    preservesFiniteLimits_spacesBaseChange_op_lan B S hS f
  have : PreservesFiniteLimits (g.sheafPullback A KY KX) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits g A KY KX
  let cXstar := (comparisonFunctor B S hS X).sheafPushforwardContinuous A JX KX
  let cYstar := (comparisonFunctor B S hS Y).sheafPushforwardContinuous A JY KY
  have : cXstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X A
  have : cYstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS Y A
  let eX := cXstar.asEquivalence
  let eY := cYstar.asEquivalence
  let ePull : v.sheafPullback A JY JX ⋙ eX.inverse ≅ eY.inverse ⋙ g.sheafPullback A KY KX :=
    (conjugateIsoEquiv (eY.symm.toAdjunction.comp (g.sheafAdjunctionContinuous A KY KX))
      ((v.sheafAdjunctionContinuous A JY JX).comp eX.symm.toAdjunction)).symm
      (smallBaseChangePushforwardComparison B S hS f hf A).symm
  have : PreservesFiniteLimits (eY.inverse ⋙ g.sheafPullback A KY KX) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (v.sheafPullback A JY JX ⋙ eX.inverse) :=
    preservesFiniteLimits_of_natIso ePull.symm
  have : PreservesFiniteLimits ((v.sheafPullback A JY JX ⋙ eX.inverse) ⋙ eX.functor) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.associator .. ≪≫ Functor.isoWhiskerLeft _ eX.counitIso ≪≫ Functor.rightUnitor _)

end InverseImage

end AlgebraicGeometry.Space

end
