module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianPushforwardComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian

/-!
# Direct and inverse image of abelian sheaves along an arbitrary morphism of algebraic spaces

The direct image `AlgebraicGeometry.Space.smallEtaleAbelianPushforward` of abelian sheaves on
the small étale sites is restriction along the base change of étale *scheme* charts, and so is
available only for a morphism whose underlying morphism of presheaves is relatively
representable: without that hypothesis the base change of an étale scheme chart of the target
is an étale algebraic space over the source, not an étale scheme chart of it.

On the *spaces*-étale sites base change is unconditional
(`AlgebraicGeometry.Space.spacesBaseChange`, Stacks 03G2 part (1)), and the two sites have the same
topos by the comparison equivalence of Stacks 03G1. So the direct image and the inverse image of
abelian sheaves on the small étale sites exist for an arbitrary morphism, as the conjugates of the
spaces-étale ones by the comparison equivalences. For a morphism with representable underlying
morphism this direct image is `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`: the direct image `f_*` of abelian
  sheaves on the small étale sites along an arbitrary `f : Y ⟶ X`.
* `AlgebraicGeometry.Space.smallEtaleAbelianGeneralInverseImage`: its left adjoint `f^{-1}`.
* `AlgebraicGeometry.Space.smallEtaleAbelianGeneralAdjunction`: the adjunction
  `f^{-1} ⊣ f_*`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageIso`: for a morphism with representable
  underlying morphism `smallEtaleAbelianDirectImage` is the direct image
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward`.
* `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageCompIso`: **Stacks 03G2, part (2)** for
  the direct image of abelian sheaves, with no hypothesis on either morphism.
* `AlgebraicGeometry.Space.preservesFiniteLimits_smallEtaleAbelianGeneralInverseImage`:
  **Stacks 04K2, part (1)** with no hypothesis on the morphism.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {W X Y Z : AlgebraicSpaces B S hS}

/-- Left Kan extensions of abelian presheaves along the opposite of spaces-étale base change
exist; instance search does not find the universally quantified hypothesis on its own. -/
instance hasLeftKanExtension_spacesBaseChange_functor_op (f : Y ⟶ X)
    (F : (SpacesEtale B S hS X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (spacesBaseChange B S hS f).functor.op.HasLeftKanExtension F :=
  inferInstance

/-- Restriction of abelian sheaves along spaces-étale base change has a left adjoint, built from
left Kan extension and sheafification. -/
instance isRightAdjoint_spacesBaseChange_sheafPushforwardContinuous (f : Y ⟶ X) :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).isRightAdjoint

/-- **The direct image of abelian sheaves on the small étale sites along an arbitrary morphism
`f : Y ⟶ X` of algebraic spaces over `S`**: the spaces-étale direct image of Stacks 03G2,
part (1), conjugated by the comparison equivalences of Stacks 03G1. -/
def smallEtaleAbelianDirectImage (f : Y ⟶ X) :
    Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  (smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse ⋙
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
    (smallEtaleAbelianSheafComparisonEquiv B S hS X).functor

/-- **The inverse image of abelian sheaves on the small étale sites along an arbitrary morphism
`f : Y ⟶ X` of algebraic spaces over `S`**: the spaces-étale inverse image conjugated by the
comparison equivalences of Stacks 03G1. It is left adjoint to
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage`. -/
def smallEtaleAbelianGeneralInverseImage (f : Y ⟶ X) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} :=
  (smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse ⋙
    (spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
    (smallEtaleAbelianSheafComparisonEquiv B S hS Y).functor

/-- **The inverse image is left adjoint to the direct image**, for an arbitrary morphism of
algebraic spaces: the conjugate of the spaces-étale adjunction by the comparison equivalences of
Stacks 03G1. -/
def smallEtaleAbelianGeneralAdjunction (f : Y ⟶ X) :
    smallEtaleAbelianGeneralInverseImage B S hS f ⊣ smallEtaleAbelianDirectImage B S hS f :=
  ((smallEtaleAbelianSheafComparisonEquiv B S hS X).symm.toAdjunction.comp
      ((spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))).comp
    (smallEtaleAbelianSheafComparisonEquiv B S hS Y).toAdjunction

/-- For a morphism `f` with representable underlying morphism,
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward` along `f` is
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImage` along `f`. -/
def smallEtaleAbelianDirectImageIso (f : Y ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) :
    smallEtaleAbelianPushforward.{u + 1} B S hS f hf ≅
      smallEtaleAbelianDirectImage B S hS f :=
  smallEtaleAbelianPushforwardConjIso B S hS f hf

/-- **Stacks 03G2, part (2), for the direct image of abelian sheaves on the small étale sites,
with no hypothesis on either morphism.** For `f : Y ⟶ X` and `g : X ⟶ Z` the composite
`f_* ⋙ g_*` is `(f ≫ g)_*`. -/
def smallEtaleAbelianDirectImageCompIso (f : Y ⟶ X) (g : X ⟶ Z) :
    smallEtaleAbelianDirectImage B S hS f ⋙ smallEtaleAbelianDirectImage B S hS g ≅
      smallEtaleAbelianDirectImage B S hS (f ≫ g) :=
  Equivalence.conjugateCompIso (smallEtaleAbelianSheafComparisonEquiv B S hS Y)
      (smallEtaleAbelianSheafComparisonEquiv B S hS X)
      (smallEtaleAbelianSheafComparisonEquiv B S hS Z) _ _ ≪≫
    Functor.isoWhiskerLeft (smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse
      (Functor.isoWhiskerRight (spacesBaseChangeAbelianPushforwardComp B S hS f g) _)

/-- **Stacks 03G2, part (2)** for the direct image of abelian sheaves, stated for a morphism `d`
together with a factorization `f ≫ g = d`. -/
def smallEtaleAbelianDirectImageCompIsoOfEq (f : Y ⟶ X) (g : X ⟶ Z) (d : Y ⟶ Z)
    (he : f ≫ g = d) :
    smallEtaleAbelianDirectImage B S hS f ⋙ smallEtaleAbelianDirectImage B S hS g ≅
      smallEtaleAbelianDirectImage B S hS d := by
  subst he
  exact smallEtaleAbelianDirectImageCompIso B S hS f g

/-- **The direct image of abelian sheaves across a commutative square, with no hypothesis on any
side.** For a commutative square whose two diagonals are both `d` — that is,
`i' ≫ f = d = f' ≫ i` — one has `i'_* ⋙ f_* ≅ f'_* ⋙ i_*`. -/
def smallEtaleAbelianDirectImageSquareIso (i' : W ⟶ Y) (f' : W ⟶ Z) (f : Y ⟶ X) (i : Z ⟶ X)
    (d : W ⟶ X) (h₁ : i' ≫ f = d) (h₂ : f' ≫ i = d) :
    smallEtaleAbelianDirectImage B S hS i' ⋙ smallEtaleAbelianDirectImage B S hS f ≅
      smallEtaleAbelianDirectImage B S hS f' ⋙ smallEtaleAbelianDirectImage B S hS i :=
  smallEtaleAbelianDirectImageCompIsoOfEq B S hS i' f d h₁ ≪≫
    (smallEtaleAbelianDirectImageCompIsoOfEq B S hS f' i d h₂).symm

/-- **Stacks 04K2, part (1), with no hypothesis on the morphism.** The inverse image of abelian
sheaves along an arbitrary morphism of algebraic spaces is left exact. -/
theorem preservesFiniteLimits_smallEtaleAbelianGeneralInverseImage (f : Y ⟶ X) :
    PreservesFiniteLimits (smallEtaleAbelianGeneralInverseImage B S hS f) := by
  have : PreservesFiniteLimits ((spacesBaseChange B S hS f).functor.sheafPullback
      AddCommGrpCat.{u + 1} (SpacesEtale.topology B S hS X)
      (SpacesEtale.topology B S hS Y)) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits
      (spacesBaseChange B S hS f).functor AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  unfold smallEtaleAbelianGeneralInverseImage
  infer_instance

/-- Restriction along the comparison functor of Stacks 03G1 is additive on abelian sheaves. -/
instance smallEtaleAbelianSheafComparisonEquiv_functor_additive (X : AlgebraicSpaces B S hS) :
    (smallEtaleAbelianSheafComparisonEquiv B S hS X).functor.Additive where
  map_add := by
    refine Sheaf.hom_ext ?_
    ext U x
    rfl

/-- Restriction along base change on the spaces-étale sites is additive on abelian sheaves. -/
instance spacesBaseChangeAbelianPushforward_additive (f : Y ⟶ X) :
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).Additive where
  map_add := by
    refine Sheaf.hom_ext ?_
    ext U x
    rfl

/-- The direct image of abelian sheaves along an arbitrary morphism is additive. -/
instance smallEtaleAbelianDirectImage_additive (f : Y ⟶ X) :
    (smallEtaleAbelianDirectImage B S hS f).Additive := by
  unfold smallEtaleAbelianDirectImage
  infer_instance

/-- The direct image of abelian sheaves along an arbitrary morphism preserves finite limits. -/
instance preservesFiniteLimits_smallEtaleAbelianDirectImage (f : Y ⟶ X) :
    PreservesFiniteLimits (smallEtaleAbelianDirectImage B S hS f) := by
  unfold smallEtaleAbelianDirectImage
  infer_instance

/-- **Stacks 04K2, part (4), for abelian sheaves and an arbitrary morphism of algebraic
spaces.** For `f : Y ⟶ X` and a geometric point `ȳ` of `Y`, the stalk at `ȳ` of the inverse
image of an abelian sheaf on the small étale site of `X` is the stalk of that sheaf at the
image geometric point `f(ȳ)`, naturally in the sheaf. -/
def smallEtaleAbelianGeneralInverseImageStalkIso (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) :
    smallEtaleAbelianGeneralInverseImage B S hS f ⋙
        sheafToPresheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} ⋙
          stalkFunctor AddCommGrpCat.{u + 1} y ≅
      sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⋙
        stalkFunctor AddCommGrpCat.{u + 1} (geometricPointMap f.hom y) := by
  let A := AddCommGrpCat.{u + 1}
  let Jsrc := SmallEtale.topology B S hS Y.1
  let Jtgt := SmallEtale.topology B S hS X.1
  let Ksrc := SpacesEtale.topology B S hS Y
  let Ktgt := SpacesEtale.topology B S hS X
  let g := (spacesBaseChange B S hS f).functor
  let x := geometricPointMap f.hom y
  let q := etaleSitePoint B S hS Y.1 y Y.2
  let p := etaleSitePoint B S hS X.1 x X.2
  let Psrc := spacesEtaleSitePoint y
  let Ptgt := spacesEtaleSitePoint x
  haveI : HasColimitsOfShape (geometricFiber B S hS Y.1 y).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape q.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape (SmallEtaleNeighborhood y)ᵒᵖ A :=
    hasColimitsOfShape_of_equivalence (neighborhoodFiberElementsEquiv B S hS Y.1 y).op.symm
  haveI : HasColimitsOfShape (geometricFiber B S hS X.1 x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape p.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A :=
    hasColimitsOfShape_of_equivalence (neighborhoodFiberElementsEquiv B S hS X.1 x).op.symm
  letI : RepresentablyFlat g := representablyFlat_spacesBaseChange B S hS f
  let hcover : CoverPreserving Ktgt Ksrc g := CoverPreserving.of_isContinuous g Ktgt Ksrc
  let efib : g ⋙ Psrc.fiber ≅ Ptgt.fiber := spacesBaseChangeFiberIso B S hS f y
  haveI : InitiallySmall.{u} (g ⋙ Psrc.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  let Pg := Psrc.comap g hcover
  haveI : HasColimitsOfShape (g ⋙ Psrc.fiber).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape Pg.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape Ptgt.fiber.Elementsᵒᵖ A := inferInstance
  let esrc := smallEtaleAbelianSheafComparisonEquiv B S hS Y
  let etgt := smallEtaleAbelianSheafComparisonEquiv B S hS X
  let eComap : Pg.sheafFiber (A := A) ≅ g.sheafPullback A Ktgt Ksrc ⋙ Psrc.sheafFiber :=
    Psrc.sheafFiberComapIso g hcover A
  let eBase : Pg.sheafFiber (A := A) ≅ Ptgt.sheafFiber :=
    Functor.isoWhiskerLeft (sheafToPresheaf Ktgt A)
      (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients efib)
  let eQ : q.sheafFiber (A := A) ≅ esrc.inverse ⋙ Psrc.sheafFiber :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight esrc.counitIso.symm _ ≪≫ Functor.associator .. ≪≫
      Functor.isoWhiskerLeft esrc.inverse (spacesComparisonSheafFiberIso B S hS y Y.2).symm
  let eP : etgt.inverse ⋙ Ptgt.sheafFiber ≅ p.sheafFiber :=
    Functor.isoWhiskerLeft etgt.inverse (spacesComparisonSheafFiberIso B S hS x X.2) ≪≫
      (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight etgt.counitIso _ ≪≫ Functor.leftUnitor _
  let ePull : smallEtaleAbelianGeneralInverseImage B S hS f ⋙ esrc.inverse ≅
      etgt.inverse ⋙ g.sheafPullback A Ktgt Ksrc :=
    Functor.isoWhiskerLeft (etgt.inverse ⋙ g.sheafPullback A Ktgt Ksrc) esrc.unitIso.symm ≪≫
      Functor.rightUnitor _
  let eFiber : smallEtaleAbelianGeneralInverseImage B S hS f ⋙ q.sheafFiber ≅ p.sheafFiber :=
    Functor.isoWhiskerLeft _ eQ ≪≫ (Functor.associator ..).symm ≪≫
      Functor.isoWhiskerRight ePull _ ≪≫ Functor.associator .. ≪≫
      Functor.isoWhiskerLeft etgt.inverse (eComap.symm ≪≫ eBase) ≪≫ eP
  exact Functor.isoWhiskerLeft (smallEtaleAbelianGeneralInverseImage B S hS f)
      (Functor.isoWhiskerLeft (sheafToPresheaf Jsrc A)
        (etaleSitePointStalkFunctorIso B S hS Y.1 y Y.2).symm) ≪≫
    eFiber ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf Jtgt A)
      (etaleSitePointStalkFunctorIso B S hS X.1 x X.2)

end AlgebraicGeometry.Space

end
