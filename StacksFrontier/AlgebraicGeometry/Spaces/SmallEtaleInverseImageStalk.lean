module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSitePoint

/-!
# Stalks of the inverse image on the small étale site of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `x` be a geometric point of
`X`. The stalk at `x` of the inverse image along `f` of a sheaf on the small étale site of `Y`
is the stalk of that sheaf at the image geometric point `f ∘ x`, naturally in the sheaf. This is
part (4) of Stacks 04K2, for an arbitrary — not necessarily representable — morphism.

## Main definitions

* `AlgebraicGeometry.Space.spacesBaseChangeFiberMap`: the map on lifts of a geometric point
  induced by base change of algebraic spaces étale over the target.

## Main results

* `AlgebraicGeometry.Space.spacesBaseChangeFiberMap_bijective` and
  `AlgebraicGeometry.Space.spacesBaseChangeFiberIso`: that map is bijective on every object, so
  the fibre functor of `x` composed with base change is the fibre functor of `f ∘ x`.
* `AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso`: the stalk comparison, which is
  Stacks 04K2, part (4).

## Implementation notes

The identification is Stacks 05V1 — the stalk at the inverse image of a point along a morphism
of sites — but on the *spaces*-étale sites, where base change along an arbitrary morphism of
algebraic spaces is available (Stacks 03G2, part (1)); on the small étale sites it is not, since
the base change of a scheme chart of `Y` is only an algebraic space étale over `X`. The point of
the spaces-étale site is `AlgebraicGeometry.Space.spacesEtaleSitePoint` and the comparison of its
stalk with the small-site stalk of Stacks 04JY is
`AlgebraicGeometry.Space.spacesEtaleSitePointStalkIso` composed with Stacks 04JZ.

The descent from the spaces-étale sites to the small étale sites is by uniqueness of adjoints
only. The comparison equivalences of Stacks 03G1 and
`AlgebraicGeometry.Space.smallToposMorphism_comparison` turn the three stalk isomorphisms into
isomorphisms of the corresponding skyscraper functors, whose composite is an isomorphism
`q_* ∘ f_* ≅ p_*` of right adjoints; conjugating it gives the isomorphism of left adjoints,
which is the statement.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The algebraic space over `S` represented by an object of the big fppf site. -/
private def representedSpace (t : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj t, isAlgebraicSpace_yoneda B S hS t⟩

/-- A section of an algebraic space over an object `t` of the big fppf site is a morphism of
algebraic spaces out of the one `t` represents. -/
private def representedSpaceHom (t : BigFppfOver B S hS) (Z : AlgebraicSpaces B S hS) :
    Z.1.obj (Opposite.op t) ≃ (representedSpace B S hS t ⟶ Z) where
  toFun a := ObjectProperty.homMk (yonedaEquiv.symm a)
  invFun g := yonedaEquiv g.hom
  left_inv a := yonedaEquiv.apply_symm_apply a
  right_inv g := by
    apply ObjectProperty.hom_ext
    exact yonedaEquiv.symm_apply_apply g.hom

/-- The identification of sections with morphisms is natural: the image of a section under a
morphism of algebraic spaces corresponds to the composite. -/
private theorem representedSpaceHom_comp (t : BigFppfOver B S hS)
    {Z W : AlgebraicSpaces B S hS} (g : Z ⟶ W) (a : Z.1.obj (Opposite.op t)) :
    representedSpaceHom B S hS t W (g.hom.app (Opposite.op t) a) =
      representedSpaceHom B S hS t Z a ≫ g := by
  apply ObjectProperty.hom_ext
  show yonedaEquiv.symm (g.hom.app (Opposite.op t) a) = yonedaEquiv.symm a ≫ g.hom
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- Two composites of sections with morphisms of algebraic spaces agree exactly when the
corresponding sections agree. -/
private theorem representedSpaceHom_comp_eq_comp_iff (t : BigFppfOver B S hS)
    {Z Z' W : AlgebraicSpaces B S hS} (g : Z ⟶ W) (g' : Z' ⟶ W) (a : Z.1.obj (Opposite.op t))
    (a' : Z'.1.obj (Opposite.op t)) :
    representedSpaceHom B S hS t Z a ≫ g = representedSpaceHom B S hS t Z' a' ≫ g' ↔
      g.hom.app (Opposite.op t) a = g'.hom.app (Opposite.op t) a' := by
  rw [← representedSpaceHom_comp, ← representedSpaceHom_comp, Equiv.apply_eq_iff_eq]

variable {X Y : AlgebraicSpaces B S hS}

/-- Base change of algebraic spaces étale over `Y` along `f : X ⟶ Y` takes a lift of a geometric
point `x` of `X` into the base change of `V` to a lift of the image of `x` into `V`, by composing
with the cartesian projection. -/
def spacesBaseChangeFiberMap (f : X ⟶ Y) (x : GeometricPoint B S hS X.1) :
    (spacesBaseChange B S hS f).functor ⋙ spacesGeometricFiber x ⟶
      spacesGeometricFiber (geometricPointMap f.hom x) where
  app V := TypeCat.ofHom fun a =>
    ⟨((spacesBaseChange B S hS f).projection.app V).hom.app
      (Opposite.op x.val.siteObject) a.1, by
      have hw := congrArg (fun k => k.hom.app (Opposite.op x.val.siteObject) a.1)
        ((spacesBaseChange B S hS f).isPullback V).w
      exact hw.trans (congrArg (f.hom.app (Opposite.op x.val.siteObject)) a.2)⟩
  naturality {V W} g := by
    ext a
    exact Subtype.ext <| congrArg (fun k => k.hom.app (Opposite.op x.val.siteObject) a.1)
      ((spacesBaseChange B S hS f).projection.naturality g)

/-- The map on lifts induced by base change is bijective. -/
theorem spacesBaseChangeFiberMap_bijective (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)
    (V : SpacesEtale B S hS Y) :
    Function.Bijective ((spacesBaseChangeFiberMap B S hS f x).app V) := by
  have hp := (spacesBaseChange B S hS f).isPullback V
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    refine Subtype.ext ?_
    apply (representedSpaceHom B S hS x.val.siteObject _).injective
    apply hp.hom_ext
    · exact (representedSpaceHom_comp_eq_comp_iff B S hS _ _ _ _ _).2 (congrArg Subtype.val hab)
    · exact (representedSpaceHom_comp_eq_comp_iff B S hS _ _ _ _ _).2 (ha.trans hb.symm)
  · rintro ⟨b, hb⟩
    have h : representedSpaceHom B S hS x.val.siteObject
          ((SpacesEtale.toSpaces B S hS Y).obj V) b ≫ V.1.hom =
        representedSpaceHom B S hS x.val.siteObject X x.val.value ≫ f :=
      (representedSpaceHom_comp_eq_comp_iff B S hS _ _ _ _ _).2 hb
    obtain ⟨a, ha⟩ : ∃ a : ((SpacesEtale.toSpaces B S hS X).obj
        ((spacesBaseChange B S hS f).functor.obj V)).1.obj (Opposite.op x.val.siteObject),
        representedSpaceHom B S hS x.val.siteObject
            ((SpacesEtale.toSpaces B S hS X).obj
              ((spacesBaseChange B S hS f).functor.obj V)) a =
          hp.lift _ _ h :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    refine ⟨⟨a, ?_⟩, Subtype.ext ?_⟩
    · apply (representedSpaceHom B S hS x.val.siteObject X).injective
      exact (representedSpaceHom_comp B S hS x.val.siteObject
          ((spacesBaseChange B S hS f).functor.obj V).1.hom a).trans
        ((congrArg (fun k => k ≫ ((spacesBaseChange B S hS f).functor.obj V).1.hom) ha).trans
          (hp.lift_snd _ _ h))
    · apply (representedSpaceHom B S hS x.val.siteObject
        ((SpacesEtale.toSpaces B S hS Y).obj V)).injective
      exact (representedSpaceHom_comp B S hS x.val.siteObject
          ((spacesBaseChange B S hS f).projection.app V) a).trans
        ((congrArg (fun k => k ≫ (spacesBaseChange B S hS f).projection.app V) ha).trans
          (hp.lift_fst _ _ h))

/-- The fibre functor of a geometric point of `X` on the spaces-étale site, composed with base
change along `f`, is the fibre functor of the image geometric point of `Y`. -/
def spacesBaseChangeFiberIso (f : X ⟶ Y) (x : GeometricPoint B S hS X.1) :
    (spacesBaseChange B S hS f).functor ⋙ spacesGeometricFiber x ≅
      spacesGeometricFiber (geometricPointMap f.hom x) :=
  haveI (V : SpacesEtale B S hS Y) : IsIso ((spacesBaseChangeFiberMap B S hS f x).app V) :=
    (isIso_iff_bijective _).2 (spacesBaseChangeFiberMap_bijective B S hS f x V)
  haveI := NatIso.isIso_of_isIso_app (spacesBaseChangeFiberMap B S hS f x)
  asIso (spacesBaseChangeFiberMap B S hS f x)

/-- The stalk at a geometric point of a sheaf on the spaces-étale site of `X` is the stalk of its
restriction along the comparison functor of Stacks 03G1, that is, the geometric stalk of Stacks
04JY on the small étale site. -/
def spacesEtaleSitePointSheafFiberIso (Z : AlgebraicSpaces B S hS)
    (z : GeometricPoint B S hS Z.1) :
    (spacesEtaleSitePoint z).sheafFiber (A := Type (u + 1)) ≅
      (comparisonFunctor B S hS Z).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z) ⋙
        (etaleSitePoint B S hS Z.1 z Z.2).sheafFiber :=
  let cZ := comparisonFunctor B S hS Z
  let ePresheaf : (spacesEtaleSitePoint z).presheafFiber (A := Type (u + 1)) ≅
      (Functor.whiskeringLeft (SmallEtale B S hS Z.1)ᵒᵖ (SpacesEtale B S hS Z)ᵒᵖ
          (Type (u + 1))).obj cZ.op ⋙
        (etaleSitePoint B S hS Z.1 z Z.2).presheafFiber :=
    spacesEtaleSitePointStalkIso z ≪≫ (stalkSpacesEtaleIso z).symm ≪≫
      Functor.isoWhiskerLeft _ (etaleSitePointStalkIso B S hS Z.1 z Z.2).symm
  Functor.isoWhiskerLeft (sheafToPresheaf (SpacesEtale.topology B S hS Z) (Type (u + 1)))
      ePresheaf ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight (cZ.sheafPushforwardContinuousCompSheafToPresheafIso (Type (u + 1))
      (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z)).symm _ ≪≫
    Functor.associator ..

/-- **Stacks 04K2, part (4).** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` and a
geometric point `x` of `X`, the stalk at `x` of the small étale inverse image of a sheaf on `Y`
is the stalk of that sheaf at the image geometric point `f ∘ x`, naturally in the sheaf. -/
@[stacks 04K2 "stalk_pullback"]
def smallEtaleInverseImageStalkIso (f : X ⟶ Y) (x : GeometricPoint B S hS X.1) :
    (smallToposMorphism B S hS f).inverseImage ⋙
        sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) ⋙ stalkSetFunctor x ≅
      sheafToPresheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)) ⋙
        stalkSetFunctor (geometricPointMap f.hom x) := by
  let A := Type (u + 1)
  let KX := SpacesEtale.topology B S hS X
  let KY := SpacesEtale.topology B S hS Y
  let u := (spacesBaseChange B S hS f).functor
  let y := geometricPointMap f.hom x
  let q := etaleSitePoint B S hS X.1 x X.2
  let p := etaleSitePoint B S hS Y.1 y Y.2
  let Px := spacesEtaleSitePoint x
  let Py := spacesEtaleSitePoint y
  let cXstar := (comparisonFunctor B S hS X).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS X.1) KX
  let cYstar := (comparisonFunctor B S hS Y).sheafPushforwardContinuous A
    (SmallEtale.topology B S hS Y.1) KY
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SpacesEtale.isTerminal_idObj B S hS Y)
      (isTerminal_spacesBaseChange_idObj B S hS f)
  letI : HasFiniteLimits (SpacesEtale B S hS Y) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving KY KX u := CoverPreserving.of_isContinuous u KY KX
  let efib : u ⋙ Px.fiber ≅ Py.fiber := spacesBaseChangeFiberIso B S hS f x
  haveI : InitiallySmall.{u} (u ⋙ Px.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  let Pxc := Px.comap u hcover
  let eComap : Pxc.sheafFiber (A := A) ≅ u.sheafPullback A KY KX ⋙ Px.sheafFiber :=
    Px.sheafFiberComapIso u hcover A
  let eBase : Pxc.sheafFiber (A := A) ≅ Py.sheafFiber :=
    CategoryOfElements.sheafColimIsoOfNatIso KY efib
  haveI : cXstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS X A
  haveI : cYstar.IsEquivalence := comparisonFunctor_sheafEquivalence B S hS Y A
  let eX := cXstar.asEquivalence
  let eY := cYstar.asEquivalence
  let skyX : Px.skyscraperSheafFunctor (A := A) ⋙ cXstar ≅ q.skyscraperSheafFunctor :=
    Adjunction.rightAdjointUniq
      ((eX.symm.toAdjunction.comp Px.skyscraperSheafAdjunction).ofNatIsoLeft
        (Functor.isoWhiskerLeft eX.inverse (spacesEtaleSitePointSheafFiberIso B S hS X x) ≪≫
          (Functor.associator ..).symm ≪≫
          Functor.isoWhiskerRight eX.counitIso q.sheafFiber ≪≫
          Functor.leftUnitor _))
      q.skyscraperSheafAdjunction
  let skyY : Py.skyscraperSheafFunctor (A := A) ⋙ cYstar ≅ p.skyscraperSheafFunctor :=
    Adjunction.rightAdjointUniq
      ((eY.symm.toAdjunction.comp Py.skyscraperSheafAdjunction).ofNatIsoLeft
        (Functor.isoWhiskerLeft eY.inverse (spacesEtaleSitePointSheafFiberIso B S hS Y y) ≪≫
          (Functor.associator ..).symm ≪≫
          Functor.isoWhiskerRight eY.counitIso p.sheafFiber ≪≫
          Functor.leftUnitor _))
      p.skyscraperSheafAdjunction
  let skyBase : Px.skyscraperSheafFunctor (A := A) ⋙ u.sheafPushforwardContinuous A KY KX ≅
      Py.skyscraperSheafFunctor :=
    Px.skyscraperSheafFunctorCompSheafPushforwardContinuous u hcover A ≪≫
      Adjunction.rightAdjointUniq
        (Pxc.skyscraperSheafAdjunction.ofNatIsoLeft eBase) Py.skyscraperSheafAdjunction
  let eSky : q.skyscraperSheafFunctor (A := A) ⋙ (smallToposMorphism B S hS f).pushforward ≅
      p.skyscraperSheafFunctor :=
    Functor.isoWhiskerRight skyX.symm _ ≪≫ Functor.associator .. ≪≫
      Functor.isoWhiskerLeft _ (smallToposMorphism_comparison B S hS f) ≪≫
      (Functor.associator ..).symm ≪≫ Functor.isoWhiskerRight skyBase _ ≪≫ skyY
  let eStalk : p.sheafFiber (A := A) ≅
      (smallToposMorphism B S hS f).inverseImage ⋙ q.sheafFiber :=
    (conjugateIsoEquiv ((smallToposMorphism B S hS f).adj.comp q.skyscraperSheafAdjunction)
      p.skyscraperSheafAdjunction).symm eSky
  exact Functor.isoWhiskerLeft (smallToposMorphism B S hS f).inverseImage
      (Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS X.1) A)
        (etaleSitePointStalkIso B S hS X.1 x X.2).symm) ≪≫
    eStalk.symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS Y.1) A)
      (etaleSitePointStalkIso B S hS Y.1 y Y.2)

end AlgebraicGeometry.Space

end
