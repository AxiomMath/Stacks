module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperRestriction

/-!
# Stalks of the inverse image along a representable morphism

Let `i : Z ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` and let `z` be
a geometric point of `Z`. The stalk at `z` of the small étale inverse image of a sheaf on `X` is
the stalk of that sheaf at the image geometric point of `X`, naturally in the sheaf.

The mechanism is base change of étale neighbourhoods. A lift of `z` into the base change along
`i` of an étale scheme chart `U ⟶ X` is the same data as a lift of the image point into `U`:
both are sections over the field spectrum of `z` making the obvious triangle commute, and the
cartesian square of Stacks 03G2, part (4), identifies them. So the two fibre functors of the two
points of the two small étale sites agree through the base-change functor, and the identification
of stalks follows from the universal property of skyscraper sheaves: the stalk functor at a point
is left adjoint to the skyscraper functor at that point, the inverse image is left adjoint to the
direct image, and the direct image carries skyscrapers to skyscrapers.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeFiberMap`: the map on lifts of a geometric point
  induced by base change of étale charts.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeFiberMap_bijective`: that map is bijective on every
  chart, so `AlgebraicGeometry.Space.smallBaseChangeFiberIso` is an isomorphism of the two fibre
  functors.
* `AlgebraicGeometry.Space.stalkInverseImageIso`: the stalk of the inverse image at `z` is the
  stalk at the image of `z`, naturally in the sheaf.

## Implementation notes

The statement of Stacks 04K2, part (4), is for an arbitrary morphism of algebraic spaces. What is
proved here is its representable case, which is the case needed for an immersion. The general
case is the same argument on the spaces-étale site, where base change along an arbitrary morphism
exists; it needs the fibre functor of a geometric point on the spaces-étale site, which is not
available here — the points of `AlgebraicGeometry.Space.etaleSitePoint` are points of the *small*
étale site, whose objects are scheme charts.

Bijectivity of the map on lifts is the universal property of the representable base change at the
field spectrum of the geometric point, used through `lift`, `lift_fst`, `lift_snd` and `hom_ext`
rather than through a pullback of sets, so that no limit comparison is needed.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- Base change of étale scheme charts along a representable morphism `i : Z ⟶ X` takes a lift of
a geometric point `z` of `Z` into the base change of a chart `U ⟶ X` to a lift of the image of
`z` into `U`, by composing with the cartesian projection. -/
def smallBaseChangeFiberMap (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom)
    (z : GeometricPoint B S hS Z.1) :
    smallBaseChange B S hS i hi ⋙ geometricFiber B S hS Z.1 z ⟶
      geometricFiber B S hS X.1 (geometricPointMap i.hom z) where
  app U := TypeCat.ofHom fun p ↦ ⟨p.1 ≫ hi.snd U.1.hom, by
    have hw : U.1.hom.app (Opposite.op z.val.siteObject) (p.1 ≫ hi.snd U.1.hom) =
        i.hom.app (Opposite.op z.val.siteObject)
          ((hi.fst U.1.hom).app (Opposite.op z.val.siteObject) p.1) :=
      (congrArg (fun α : yoneda.obj (hi.pullback U.1.hom) ⟶ X.1 ↦
        α.app (Opposite.op z.val.siteObject) p.1) (hi.w U.1.hom)).symm
    have hp : (hi.fst U.1.hom).app (Opposite.op z.val.siteObject) p.1 = z.val.value := p.2
    change U.1.hom.app (Opposite.op z.val.siteObject) (p.1 ≫ hi.snd U.1.hom) =
      i.hom.app (Opposite.op z.val.siteObject) z.val.value
    rw [hw, hp]⟩
  naturality {U V} f := by
    ext p
    refine Subtype.ext ?_
    obtain ⟨p, hp⟩ := p
    dsimp only
    have h₁ : (p ≫ ((smallBaseChange B S hS i hi).map f).hom.left) ≫ hi.snd V.1.hom =
        p ≫ (((smallBaseChange B S hS i hi).map f).hom.left ≫ hi.snd V.1.hom) :=
      Category.assoc _ _ _
    have h₂ : (p ≫ hi.snd U.1.hom) ≫ f.hom.left =
        p ≫ (hi.snd U.1.hom ≫ f.hom.left) := Category.assoc _ _ _
    change (p ≫ ((smallBaseChange B S hS i hi).map f).hom.left) ≫ hi.snd V.1.hom =
      (p ≫ hi.snd U.1.hom) ≫ f.hom.left
    rw [h₁, h₂, smallBaseChange_map_snd]
    rfl

/-- Evaluating the Yoneda correspondent of `yoneda.map p ≫ f` is applying `f` to `p`. -/
private theorem yonedaEquiv_yoneda_map_comp {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type _}
    {X Y : C} (p : X ⟶ Y) (f : yoneda.obj Y ⟶ F) :
    yonedaEquiv (yoneda.map p ≫ f) = f.app (Opposite.op X) p := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- For every étale chart `U ⟶ X`, the map `smallBaseChangeFiberMap` from lifts of `z` into the
base change of `U` along `i` to lifts of the image of `z` into `U` is a bijection. -/
theorem smallBaseChangeFiberMap_bijective (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (z : GeometricPoint B S hS Z.1)
    (U : SmallEtale B S hS X.1) :
    Function.Bijective ((smallBaseChangeFiberMap B S hS i hi z).app U) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
    refine Subtype.ext (hi.hom_ext (yonedaEquiv.injective ?_) (congrArg Subtype.val h))
    change yonedaEquiv (yoneda.map p ≫ hi.fst U.1.hom) =
      yonedaEquiv (yoneda.map p' ≫ hi.fst U.1.hom)
    exact (yonedaEquiv_yoneda_map_comp p _).trans
      (hp.trans (hp'.symm.trans (yonedaEquiv_yoneda_map_comp p' _).symm))
  · rintro ⟨q, hq⟩
    have hw : (yonedaEquiv.symm z.val.value) ≫ i.hom = yoneda.map q ≫ U.1.hom :=
      yonedaEquiv.injective
        (((yonedaEquiv_comp _ _).trans
            (congrArg (i.hom.app _) (yonedaEquiv.apply_symm_apply _))).trans
          (hq.symm.trans (yonedaEquiv_yoneda_map_comp q _).symm))
    refine ⟨⟨hi.lift (yonedaEquiv.symm z.val.value) q hw, ?_⟩, Subtype.ext ?_⟩
    · exact (yonedaEquiv_yoneda_map_comp _ _).symm.trans
        ((congrArg yonedaEquiv (hi.lift_fst _ q hw)).trans (yonedaEquiv.apply_symm_apply _))
    · exact hi.lift_snd _ _ _

/-- The fibre functor of a geometric point of `Z` pulled back along base change of étale charts
is the fibre functor of its image geometric point of `X`. -/
def smallBaseChangeFiberIso (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom)
    (z : GeometricPoint B S hS Z.1) :
    smallBaseChange B S hS i hi ⋙ geometricFiber B S hS Z.1 z ≅
      geometricFiber B S hS X.1 (geometricPointMap i.hom z) :=
  haveI (U : SmallEtale B S hS X.1) : IsIso ((smallBaseChangeFiberMap B S hS i hi z).app U) :=
    (isIso_iff_bijective _).2 (smallBaseChangeFiberMap_bijective B S hS i hi z U)
  haveI := NatIso.isIso_of_isIso_app (smallBaseChangeFiberMap B S hS i hi z)
  asIso (smallBaseChangeFiberMap B S hS i hi z)

/-- The representable case of **Stacks 04K2, part (4)**: for a representable morphism
`i : Z ⟶ X` of algebraic spaces and a geometric point `z` of `Z`, the stalk at `z` of the small
étale inverse image of a sheaf on `X` is the stalk of that sheaf at the image of `z`, naturally
in the sheaf. -/
def stalkInverseImageIso (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom)
    (z : GeometricPoint B S hS Z.1) :
    (smallToposMorphism B S hS i).inverseImage ⋙
        sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)) ⋙
          stalkSetFunctor z ≅
      sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⋙
        stalkSetFunctor (geometricPointMap i.hom z) :=
  haveI := (smallBaseChange_isMorphismOfSites B S hS i hi).toIsContinuous
  let p := etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2
  let q := etaleSitePoint B S hS Z.1 z Z.2
  let e : q.skyscraperSheafFunctor (A := Type (u + 1)) ⋙
      (smallToposMorphism B S hS i).pushforward ≅ p.skyscraperSheafFunctor :=
    Functor.isoWhiskerLeft q.skyscraperSheafFunctor (smallBaseChange_topos B S hS i hi) ≪≫
      GrothendieckTopology.Point.skyscraperSheafFunctorCompSheafPushforwardContinuousIso p q
        (smallBaseChange B S hS i hi) (smallBaseChangeFiberIso B S hS i hi z) (Type (u + 1))
  let e' : p.sheafFiber (A := Type (u + 1)) ≅
      (smallToposMorphism B S hS i).inverseImage ⋙ q.sheafFiber :=
    (conjugateIsoEquiv ((smallToposMorphism B S hS i).adj.comp q.skyscraperSheafAdjunction)
      p.skyscraperSheafAdjunction).symm e
  Functor.isoWhiskerLeft (smallToposMorphism B S hS i).inverseImage
      (Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS Z.1) (Type (u + 1)))
        (etaleSitePointStalkIso B S hS Z.1 z Z.2).symm) ≪≫
    e'.symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
      (etaleSitePointStalkIso B S hS X.1 (geometricPointMap i.hom z) X.2)

end AlgebraicGeometry.Space

end
