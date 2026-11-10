module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsSchemeStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of the small étale direct image along a finite morphism of algebraic spaces

Let `π : X ⟶ Y` be a finite morphism of algebraic spaces over a scheme `S` and let `y` be a
geometric point of `Y` with lifts `x₁, …, xₙ` in `X`. Stacks 0DK3 computes the stalk of the
direct image of a sheaf of sets on `X_étale` as `(π_*F)_y = ∏ᵢ F_{xᵢ}`.

A lift of `y` is a section of `X` over the field spectrum of `y` whose image under `π` is the
section `y`; the lifts form a finite set, because base change of `π` along `y` is a finite
morphism of affine schemes and the lifts are its sections. Each lift carries a canonical map
`(π_*F)_y ⟶ F_{xᵢ}`: the stalk at `xᵢ` of the inverse image of a sheaf on `Y` is the stalk of
that sheaf at the image of `xᵢ` (Stacks 04K2, part (4)), and composing that identification at
`π_*F` with the stalk of the counit `π⁻¹π_*F ⟶ F` gives it. Together these assemble the
comparison map into the product.

## Main definitions

* `AlgebraicGeometry.Space.GeometricLifts`: the lifts of a geometric point of `Y` to `X`.
* `AlgebraicGeometry.Space.geometricLiftPoint`: a lift, read as a geometric point of `X`.
* `AlgebraicGeometry.Space.stalkPushforwardHom`: the canonical map from the stalk of a direct
  image at the image of a geometric point to the stalk at that point.
* `AlgebraicGeometry.Space.stalkPushforwardComponent`: the same map at a geometric point of `Y`
  presented together with an identification of it as the image point.
* `AlgebraicGeometry.Space.stalkPushforwardToProduct`: the comparison map
  `(π_*F)_y ⟶ ∏ᵢ F_{xᵢ}` of Stacks 0DK3.
* `AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback`: the index set of that product is
  unchanged by base change — for a cartesian square the lifts of a geometric point of the new
  base are the lifts of its image in the old one.
* `AlgebraicGeometry.Space.PushforwardStalkSchemeComparison`: the reduction of Stacks 0DK3 to
  Stacks 03QP at a geometric point, as a datum — a presentation of the situation by a finite
  morphism of schemes under which the two comparison maps correspond.
* `AlgebraicGeometry.Space.smallEtaleSchemeDirectImage`,
  `AlgebraicGeometry.Space.chartBaseScheme` and `AlgebraicGeometry.Space.chartBasePoint`: the
  scheme-side direct image, and the scheme and geometric point on which the reduction reads the
  stalk at `y`.

## Main results

* `AlgebraicGeometry.Space.finite_geometricLifts`: a geometric point of the target of a finite
  morphism has finitely many lifts.
* `AlgebraicGeometry.Space.geometricLiftPoint_map`: a lift lies over the point it lifts.
* `AlgebraicGeometry.Space.stalkPushforwardHom_natural` and
  `AlgebraicGeometry.Space.stalkPushforwardToProduct_natural`: naturality in the sheaf.
* `AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback_apply` and
  `AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback_symm_apply`: that bijection and its
  inverse are the maps on sections induced by the upper arrow of the square.

## Implementation notes

Lifts are indexed by sections of `X` over the field spectrum of `y` rather than by abstract
geometric points of `X` lying over `y`: a geometric point of `X` over `y` has the same field
and the same structure morphism to the base as `y`, so the two notions agree, and the section
form is a type in `Type u` whose finiteness is the finiteness of a fibre.
`AlgebraicGeometry.Space.geometricLiftPoint` is the resulting geometric point of `X` and
`AlgebraicGeometry.Space.geometricLiftPoint_map` is the statement that it lies over `y`. This
is the indexing that `AlgebraicGeometry.finitePushforwardStalkToProduct` uses for schemes.

Finiteness of the fibre of lifts is where the finiteness of `π` is used. Testing `π` against
the field spectrum of `y`, which is affine, produces an affine scheme `V` finite over it
together with a pullback square; a lift is then a section of `V` over that field spectrum, and
those are finite in number by `AlgebraicGeometry.finite_lifts_of_isFinite`. The passage from
sections of the presheaf `X` to morphisms of the site and then to morphisms of schemes uses
that the Yoneda embedding and the functor to schemes are both faithful.

Bijectivity of the comparison map is not proved in this file. What the file records towards it
is `AlgebraicGeometry.Space.PushforwardStalkSchemeComparison`, the presentation of the situation
at the geometric point by a finite morphism of schemes under which the two comparison maps
correspond. What is proved is the construction of the comparison map, the finiteness of the
index set over which the product is taken, and naturality of the comparison in the sheaf. The
bijectivity of Stacks 0DK3 is proved, for the comparison map
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompToPi`, as
`AlgebraicGeometry.Space.bijective_presheafFiberCompToPi_of_isFinite` in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteStalkPushforwardProduct`.

For a finite morphism of *schemes* the bijectivity is the content of Stacks 03QP and **is**
proved in this repository, as `AlgebraicGeometry.finitePushforwardStalkToProduct_bijective` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk`, which this file imports
directly; it is stated for a morphism of a big étale site, hence on the small étale site of a
scheme of that site, which is the site an étale scheme chart of `Y` carries. The reduction of
Stacks 0DK3 to it along such a chart is Stacks 03LR, available as
`AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso`. The first thing that reduction
owes, the identification of the index sets — the lifts of a geometric point of `Y` to `X` with
the lifts of the corresponding geometric point of the chart to the base change — is
`AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback` below, proved for an arbitrary
cartesian square. The passage from the small étale site of the chart as an algebraic space to
the small étale site of the chart as a scheme of the associated big étale site is
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` for the *sites*, and for the *stalk of
a sheaf of sets* it is `AlgebraicGeometry.Space.chartEtaleStalkIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsSchemeStalk`, a named isomorphism at the
chart that `AlgebraicGeometry.Space.chartStalkPresentation` chooses.

What the presentation assumes, and the only thing it assumes beyond data that is separately
available, is the compatibility of `AlgebraicGeometry.Space.stalkPushforwardToProduct` with
`AlgebraicGeometry.finitePushforwardStalkToProduct` across that passage: the two comparison maps
are built independently, one from `AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso` and the
counit of the small étale adjunction, the other inside the big étale site of schemes, and no
declaration of this repository relates them. The compatibility in addition has to bridge the two
spellings of the index set: sections of `X` over the field spectrum of `y` here
(`AlgebraicGeometry.Space.GeometricLifts`) against morphisms of schemes splitting the morphism of
schemes there (`AlgebraicGeometry.GeometricLifts`); for a cartesian square of algebraic spaces
the corresponding bijection is `AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback`, so what
the presentation adds there is the passage to the represented case.

Why the presentation is not the conclusion in disguise: it asserts an equation between two maps
that this repository defines separately, and no field of it asserts that either map is injective
or surjective. Bijectivity is supplied for the scheme-side map by Stacks 03QP, and the
presentation would transport it.
The presentation also fixes the base of the reduction to be the scheme and the geometric point
that `AlgebraicGeometry.Space.chartStalkPresentation` chooses at `y`, which is what ties it to
`AlgebraicGeometry.Space.chartEtaleStalkIso` rather than to an arbitrary identification of
stalks.

Sheaves of sets are valued in `Type (u + 1)`, the universe of the objects of the small étale
site of an algebraic space over `Scheme.{u}`; this is the universe of the morphism of small
étale topoi of Stacks 03G2, part (3), and of the set-valued stalk functor of Stacks 04JY.

## References

* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (π : X ⟶ Y)

/-- The lifts of a geometric point `y` of `Y` to `X` along `π`: the sections of `X` over the
field spectrum of `y` that `π` carries to the section `y`. -/
abbrev GeometricLifts (y : GeometricPoint B S hS Y.1) : Type u :=
  {v : X.1.obj (Opposite.op y.val.siteObject) //
    π.hom.app (Opposite.op y.val.siteObject) v = y.val.value}

/-- A lift of a geometric point `y` of `Y`, read as a geometric point of `X`: it has the field,
the structure morphism to the base and hence the algebraically closed field of `y`. -/
def geometricLiftPoint (y : GeometricPoint B S hS Y.1) (v : GeometricLifts B S hS π y) :
    GeometricPoint B S hS X.1 :=
  ⟨{ carrier := y.val.carrier
     contained := y.val.contained
     toBase := y.val.toBase
     value := v.1 }, y.property⟩

/-- A lift of a geometric point `y` of `Y` lies over `y`. -/
theorem geometricLiftPoint_map (y : GeometricPoint B S hS Y.1)
    (v : GeometricLifts B S hS π y) :
    geometricPointMap π.hom (geometricLiftPoint B S hS π y v) = y := by
  apply Subtype.ext
  dsimp [geometricPointMap, geometricLiftPoint, FieldValuedPoint.map]
  exact congrArg _ v.2

/-- **Stacks 0DK3, finiteness of the index set.** A geometric point of the target of a finite
morphism of algebraic spaces has finitely many lifts, so the product in the statement is a
finite one.

The field spectrum of `y` is affine, so testing `π` against the section `y` produces an affine
scheme `V`, a finite morphism `V ⟶ Spec κ(y)` and a pullback square exhibiting `V` as the base
change of `X`. A lift of `y` therefore determines a section of that finite morphism, and
`AlgebraicGeometry.finite_lifts_of_isFinite` makes those finite in number; the assignment is
injective because the Yoneda embedding and the functor to schemes are faithful. -/
@[stacks 0DK3 "the lifts `x₁, …, xₙ` of `y` are finite in number"]
theorem finite_geometricLifts (hπ : IsFinite B S hS π.hom)
    (y : GeometricPoint B S hS Y.1) :
    Finite (GeometricLifts B S hS π y) := by
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj y.val.siteObject) := by
    dsimp [FieldValuedPoint.siteObject, BigFppfOver.toScheme, BigFppfSite.obj]
    infer_instance
  obtain ⟨V, p, i, hV, hfin, sq⟩ :=
    hπ y.val.siteObject hU (yonedaEquiv.symm y.val.value)
  have := hfin
  have key : ∀ v : GeometricLifts B S hS π y,
      (yonedaEquiv.symm v.1) ≫ π.hom =
        𝟙 (yoneda.obj y.val.siteObject) ≫ yonedaEquiv.symm y.val.value := by
    intro v
    rw [Category.id_comp, yonedaEquiv_symm_naturality_right, v.2]
  have hfinite : Finite {g : (BigFppfOver.toScheme B S hS).obj y.val.siteObject ⟶
      (BigFppfOver.toScheme B S hS).obj V //
      g ≫ (BigFppfOver.toScheme B S hS).map p = 𝟙 _} :=
    AlgebraicGeometry.finite_lifts_of_isFinite ((BigFppfOver.toScheme B S hS).map p) (𝟙 _)
  set q : GeometricLifts B S hS π y → (y.val.siteObject ⟶ V) := fun v =>
    (yoneda (C := BigFppfOver B S hS)).preimage (sq.lift _ _ (key v)) with hq
  have hqp : ∀ v, q v ≫ p = 𝟙 _ := by
    intro v
    apply (yoneda (C := BigFppfOver B S hS)).map_injective
    rw [CategoryTheory.Functor.map_comp, hq, Functor.map_preimage,
      sq.lift_snd (yonedaEquiv.symm v.1) (𝟙 _) (key v), CategoryTheory.Functor.map_id]
  refine @Finite.of_injective _ _ hfinite
    (fun v => ⟨(BigFppfOver.toScheme B S hS).map (q v), ?_⟩) ?_
  · rw [← CategoryTheory.Functor.map_comp, hqp v, CategoryTheory.Functor.map_id]
  · intro v w hvw
    simp only [Subtype.mk.injEq] at hvw
    have hq' : q v = q w := (BigFppfOver.toScheme B S hS).map_injective hvw
    have h3 : sq.lift (yonedaEquiv.symm v.1) (𝟙 _) (key v) =
        sq.lift (yonedaEquiv.symm w.1) (𝟙 _) (key w) := by
      have h := congrArg (yoneda (C := BigFppfOver B S hS)).map hq'
      rwa [hq, Functor.map_preimage, Functor.map_preimage] at h
    have h4 : yonedaEquiv.symm v.1 = yonedaEquiv.symm w.1 := by
      rw [← sq.lift_fst (yonedaEquiv.symm v.1) (𝟙 _) (key v),
        ← sq.lift_fst (yonedaEquiv.symm w.1) (𝟙 _) (key w), h3]
    exact Subtype.ext (yonedaEquiv.symm.injective h4)

/-- **The canonical map from a direct-image stalk to a stalk of the sheaf.** For a geometric
point `x` of `X` the stalk at the image of `x` of the direct image of a sheaf of sets `F` on
`X_étale` maps canonically to the stalk of `F` at `x`.

The stalk at `x` of the inverse image of a sheaf on `Y` is the stalk of that sheaf at the image
of `x`, by Stacks 04K2, part (4); reading that identification backwards at `π_*F` and following
it with the stalk at `x` of the counit `π⁻¹π_*F ⟶ F` gives the map. No hypothesis on `π`
enters. -/
def stalkPushforwardHom (x : GeometricPoint B S hS X.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (stalkSetFunctor (geometricPointMap π.hom x)).obj
        ((smallToposMorphism B S hS π).pushforward.obj F).obj ⟶
      (stalkSetFunctor x).obj F.obj :=
  (smallEtaleInverseImageStalkIso B S hS π x).inv.app
      ((smallToposMorphism B S hS π).pushforward.obj F) ≫
    (stalkSetFunctor x).map ((smallToposMorphism B S hS π).adj.counit.app F).hom

/-- The canonical map from a direct-image stalk to a stalk of the sheaf is natural in the
sheaf. -/
theorem stalkPushforwardHom_natural (x : GeometricPoint B S hS X.1)
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (α : F ⟶ G) :
    (stalkSetFunctor (geometricPointMap π.hom x)).map
          ((smallToposMorphism B S hS π).pushforward.map α).hom ≫
        stalkPushforwardHom B S hS π x G =
      stalkPushforwardHom B S hS π x F ≫ (stalkSetFunctor x).map α.hom := by
  have hnat : (stalkSetFunctor (geometricPointMap π.hom x)).map
          ((smallToposMorphism B S hS π).pushforward.map α).hom ≫
        (smallEtaleInverseImageStalkIso B S hS π x).inv.app
          ((smallToposMorphism B S hS π).pushforward.obj G) =
      (smallEtaleInverseImageStalkIso B S hS π x).inv.app
          ((smallToposMorphism B S hS π).pushforward.obj F) ≫
        (stalkSetFunctor x).map
          ((smallToposMorphism B S hS π).inverseImage.map
            ((smallToposMorphism B S hS π).pushforward.map α)).hom :=
    (smallEtaleInverseImageStalkIso B S hS π x).inv.naturality
      ((smallToposMorphism B S hS π).pushforward.map α)
  have hcnat := (smallToposMorphism B S hS π).adj.counit.naturality α
  dsimp only [stalkPushforwardHom]
  rw [← Category.assoc, hnat, Category.assoc, Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg (fun β : (smallToposMorphism B S hS π).inverseImage.obj
      ((smallToposMorphism B S hS π).pushforward.obj F) ⟶ G => β.hom) hcnat

/-- The canonical map from the stalk of a direct image at a geometric point `y` of `Y` to the
stalk at a geometric point `x` of `X` presented together with an identification of `y` as the
image of `x`. -/
def stalkPushforwardComponent (x : GeometricPoint B S hS X.1)
    (y : GeometricPoint B S hS Y.1) (h : geometricPointMap π.hom x = y)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj →
      stalkSet x F.obj :=
  fun z => stalkPushforwardHom B S hS π x F (h ▸ z)

/-- The canonical map at a geometric point of `Y` with a chosen point above it is natural in
the sheaf. -/
theorem stalkPushforwardComponent_natural (x : GeometricPoint B S hS X.1)
    (y : GeometricPoint B S hS Y.1) (h : geometricPointMap π.hom x = y)
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (α : F ⟶ G)
    (z : stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj) :
    stalkPushforwardComponent B S hS π x y h G
        (stalkSetMap y ((smallToposMorphism B S hS π).pushforward.map α).hom z) =
      stalkSetMap x α.hom (stalkPushforwardComponent B S hS π x y h F z) := by
  subst h
  dsimp only [stalkPushforwardComponent]
  have hn := ConcreteCategory.congr_hom (stalkPushforwardHom_natural B S hS π x α) z
  simp only [CategoryTheory.comp_apply, stalkSetFunctor_map_apply] at hn
  exact hn

/-- **The comparison map of Stacks 0DK3.** For a finite morphism `π : X ⟶ Y` of algebraic
spaces and a geometric point `y` of `Y`, the stalk at `y` of the direct image of a sheaf of
sets `F` on `X_étale` maps canonically to the product of the stalks of `F` over the lifts of
`y`, the component at a lift being
`AlgebraicGeometry.Space.stalkPushforwardComponent`.

Stacks 0DK3 asserts that this map is bijective. That assertion is not proved for this map; it
is proved for the comparison map `CategoryTheory.GrothendieckTopology.Point.presheafFiberCompToPi`
as `AlgebraicGeometry.Space.bijective_presheafFiberCompToPi_of_isFinite`. What is proved about
this map is its construction and its naturality in the sheaf. -/
@[stacks 0DK3 "the canonical map `(π_*F)_y ⟶ ∏ᵢ F_{xᵢ}` over the lifts of `y`"]
def stalkPushforwardToProduct (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj →
      (∀ v : GeometricLifts B S hS π y,
        stalkSet (geometricLiftPoint B S hS π y v) F.obj) :=
  fun z v =>
    stalkPushforwardComponent B S hS π (geometricLiftPoint B S hS π y v) y
      (geometricLiftPoint_map B S hS π y v) F z

/-- Each component of the comparison map is the canonical map at the corresponding lift. -/
theorem stalkPushforwardToProduct_apply (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (z : stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj)
    (v : GeometricLifts B S hS π y) :
    stalkPushforwardToProduct B S hS π y F z v =
      stalkPushforwardComponent B S hS π (geometricLiftPoint B S hS π y v) y
        (geometricLiftPoint_map B S hS π y v) F z :=
  rfl

/-- **Stacks 0DK3 is natural in the sheaf.** The comparison map commutes with the stalk maps
induced by a morphism of sheaves of sets on `X_étale`. -/
@[stacks 0DK3 "naturality of the comparison map in the sheaf"]
theorem stalkPushforwardToProduct_natural (y : GeometricPoint B S hS Y.1)
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))} (α : F ⟶ G)
    (z : stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj)
    (v : GeometricLifts B S hS π y) :
    stalkPushforwardToProduct B S hS π y G
        (stalkSetMap y ((smallToposMorphism B S hS π).pushforward.map α).hom z) v =
      stalkSetMap (geometricLiftPoint B S hS π y v) α.hom
        (stalkPushforwardToProduct B S hS π y F z v) :=
  stalkPushforwardComponent_natural B S hS π (geometricLiftPoint B S hS π y v) y
    (geometricLiftPoint_map B S hS π y v) α z

/-! ### The index set of Stacks 0DK3 under base change

The source's proof of Stacks 0DK3 begins by replacing `Y` by an étale neighbourhood `(V, v)`
of `y` and `X` by the fibre product `X ×_Y V`, so that the morphism in question becomes a
finite morphism of schemes and Stacks 03QP applies to it. For that replacement to be a
replacement, the product in the statement must be taken over the same index set before and
after, that is the lifts of `v` along the base change of `π` must be the lifts of `y` along
`π`. That bijection is proved here, for an arbitrary cartesian square and with no hypothesis
on any of its four arrows. -/

/-- Sections over one object of the site of a cartesian square of algebraic spaces form a
cartesian square of sets: the inclusion into presheaves preserves the fibre product and so
does evaluation at an object. -/
private theorem isPullback_app_of_isPullback {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (T : (BigFppfOver B S hS)ᵒᵖ) :
    IsPullback (i.hom.app T) (f'.hom.app T) (π.hom.app T) (g.hom.app T) :=
  Functor.map_isPullback
    ((CategoryTheory.evaluation (BigFppfOver B S hS)ᵒᵖ (Type u)).obj T)
    (AlgebraicSpaces.isPullback_hom B S hS sq)

/-- Sections of the base change over the field spectrum of a geometric point of `V`,
identified with the set-theoretic fibre product of the sections of `X` and of `V`. -/
private noncomputable def liftsPullbackObjEquiv {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (v : GeometricPoint B S hS V.1) :
    X'.1.obj (Opposite.op v.val.siteObject) ≃
      Limits.Types.PullbackObj (π.hom.app (Opposite.op v.val.siteObject))
        (g.hom.app (Opposite.op v.val.siteObject)) :=
  Limits.PullbackCone.IsLimit.equivPullbackObj
    (isPullback_app_of_isPullback B S hS π sq (Opposite.op v.val.siteObject)).isLimit

/-- The first component of the identification is the image under `i`. -/
private theorem liftsPullbackObjEquiv_fst {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (v : GeometricPoint B S hS V.1) (w : X'.1.obj (Opposite.op v.val.siteObject)) :
    (liftsPullbackObjEquiv B S hS π sq v w).1.1 =
      i.hom.app (Opposite.op v.val.siteObject) w :=
  Limits.PullbackCone.IsLimit.equivPullbackObj_apply_fst
    (isPullback_app_of_isPullback B S hS π sq (Opposite.op v.val.siteObject)).isLimit w

/-- The second component of the identification is the image under `f'`. -/
private theorem liftsPullbackObjEquiv_snd {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (v : GeometricPoint B S hS V.1) (w : X'.1.obj (Opposite.op v.val.siteObject)) :
    (liftsPullbackObjEquiv B S hS π sq v w).1.2 =
      f'.hom.app (Opposite.op v.val.siteObject) w :=
  Limits.PullbackCone.IsLimit.equivPullbackObj_apply_snd
    (isPullback_app_of_isPullback B S hS π sq (Opposite.op v.val.siteObject)).isLimit w

/-- The section of the image of a geometric point is the image of its section; the two points
have the same field spectrum, so the two sides are sections over the same object. -/
private theorem geometricPointMap_val_value {V : AlgebraicSpaces B S hS} (g : V ⟶ Y)
    (v : GeometricPoint B S hS V.1) :
    (geometricPointMap g.hom v).val.value =
      g.hom.app (Opposite.op v.val.siteObject) v.val.value := by
  dsimp only [geometricPointMap, FieldValuedPoint.map]

/-- **Stacks 0DK3: the index set of the product is unchanged by base change.** For a
cartesian square

```
X' --i--> X
|         |
f'        π
↓         ↓
V --g---> Y
```

of algebraic spaces over `S` and a geometric point `v` of `V`, the lifts of `v` along `f'`
are the lifts along `π` of the image of `v` in `Y`, the bijection sending a lift to its image
under `i`.

This is the step with which the source's proof of Stacks 0DK3 begins, specialized to the
index set: it replaces `Y` by an étale neighbourhood `(V, v)` of `y` and `X` by `X ×_Y V`, and
the product over the lifts is the same product before and after exactly because of this
bijection. Nothing is assumed of the four arrows beyond the square being cartesian, so neither
finiteness of `π` nor étaleness of `g` is needed; the lifts of a geometric point are sections
over its field spectrum, and sections over one object of the site of a cartesian square of
algebraic spaces form a cartesian square of sets. -/
@[no_expose, stacks 0DK3 "the lifts of `y` are the lifts of `v` along the base change of `π`"]
noncomputable def geometricLiftsEquivOfIsPullback {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (v : GeometricPoint B S hS V.1) :
    GeometricLifts B S hS f' v ≃ GeometricLifts B S hS π (geometricPointMap g.hom v) where
  toFun w := ⟨(liftsPullbackObjEquiv B S hS π sq v w.1).1.1, by
    refine Eq.trans (liftsPullbackObjEquiv B S hS π sq v w.1).2 ?_
    rw [liftsPullbackObjEquiv_snd B S hS π sq v w.1, w.2,
      geometricPointMap_val_value B S hS g v]⟩
  invFun u := ⟨(liftsPullbackObjEquiv B S hS π sq v).symm ⟨(u.1, v.val.value), u.2⟩, by
    have h := liftsPullbackObjEquiv_snd B S hS π sq v
      ((liftsPullbackObjEquiv B S hS π sq v).symm ⟨(u.1, v.val.value), u.2⟩)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm⟩
  left_inv w := by
    refine Subtype.ext ((liftsPullbackObjEquiv B S hS π sq v).injective ?_)
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (Prod.ext rfl
      (Eq.trans (liftsPullbackObjEquiv_snd B S hS π sq v w.1) w.2).symm)
  right_inv u := by
    refine Subtype.ext ?_
    change (liftsPullbackObjEquiv B S hS π sq v
        ((liftsPullbackObjEquiv B S hS π sq v).symm ⟨(u.1, v.val.value), u.2⟩)).1.1 = u.1
    rw [Equiv.apply_symm_apply]

/-- The bijection of lift sets sends a lift to its image under the upper arrow of the
square. -/
theorem geometricLiftsEquivOfIsPullback_apply {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (v : GeometricPoint B S hS V.1) (w : GeometricLifts B S hS f' v) :
    (geometricLiftsEquivOfIsPullback B S hS π sq v w).1 =
      i.hom.app (Opposite.op v.val.siteObject) w.1 := by
  change (liftsPullbackObjEquiv B S hS π sq v w.1).1.1 = _
  exact liftsPullbackObjEquiv_fst B S hS π sq v w.1

/-- The inverse of the bijection of lift sets sends a lift of the image point to the unique
section of the fibre product over the two of them. -/
theorem geometricLiftsEquivOfIsPullback_symm_apply {X' V : AlgebraicSpaces B S hS}
    {i : X' ⟶ X} {f' : X' ⟶ V} {g : V ⟶ Y} (sq : IsPullback i f' π g)
    (v : GeometricPoint B S hS V.1)
    (u : GeometricLifts B S hS π (geometricPointMap g.hom v)) :
    i.hom.app (Opposite.op v.val.siteObject)
        ((geometricLiftsEquivOfIsPullback B S hS π sq v).symm u).1 = u.1 := by
  have h := geometricLiftsEquivOfIsPullback_apply B S hS π sq v
    ((geometricLiftsEquivOfIsPullback B S hS π sq v).symm u)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ### The reduction of Stacks 0DK3 to Stacks 03QP

The source proves the bijectivity of the comparison map by replacing `Y` by an étale chart
`(V, v)` through `y` and `X` by `X ×_Y V`, which for finite `π` is a scheme finite over `V`, and
then quoting Stacks 03QP for that finite morphism of schemes. Stacks 03QP is available in this
repository, as `AlgebraicGeometry.finitePushforwardStalkToProduct_bijective`; what the reduction
to it needs is a *presentation* of the situation at `y` by such a morphism of schemes, under
which the comparison map of this file and the comparison map
`AlgebraicGeometry.finitePushforwardStalkToProduct` of that tag correspond.

`AlgebraicGeometry.Space.PushforwardStalkSchemeComparison` is that presentation. What the
presentation assumes is a commuting square between two comparison
maps that are built independently of one another — this one from
`AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso` and the counit of the small étale
adjunction, that one inside the big étale site of schemes — and not the bijectivity of either of
them. -/

/-- The direct image of a sheaf of sets along a morphism of schemes of a big étale site, read on
the small étale site of the target: the sheaf whose stalk Stacks 03QP computes, hence the sheaf
whose stalk is the source of `AlgebraicGeometry.finitePushforwardStalkToProduct`. -/
@[sga "4½ Arcata 2.3.3"]
abbrev smallEtaleSchemeDirectImage {B' : _root_.AlgebraicGeometry.BigEtaleSite.{u}}
    {V W : B'.Scheme} (p : V ⟶ W)
    (G : Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology B' V.1 V.2) (Type (u + 1))) :
    Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology B' W.1 W.2) (Type (u + 1)) :=
  ((_root_.AlgebraicGeometry.smallEtaleBaseChange B' p).sheafPushforwardContinuous (Type (u + 1))
    (_root_.AlgebraicGeometry.SmallEtale.topology B' W.1 W.2)
    (_root_.AlgebraicGeometry.SmallEtale.topology B' V.1 V.2)).obj G

/-- The scheme on which the stalk at a geometric point `y` of `Y` is read after the reduction to
schemes: the scheme underlying the chart of `AlgebraicGeometry.Space.chartStalkPresentation` at
`y`, as an object of the associated big étale site.

Taking this chart rather than an arbitrary one is what ties the reduction to the named
isomorphism `AlgebraicGeometry.Space.chartEtaleStalkIso`, whose right-hand side is the étale
stalk on exactly this scheme at exactly the point
`AlgebraicGeometry.Space.chartBasePoint`. -/
abbrev chartBaseScheme (y : GeometricPoint B S hS Y.1) : (associatedBigEtaleSite B).Scheme :=
  ⟨(BigFppfOver.toScheme B S hS).obj (chartStalkPresentation B S hS Y.1 Y.2 y).chart.obj.left,
    (chartStalkPresentation B S hS Y.1 Y.2 y).chart.obj.left.left.property⟩

/-- The geometric point of `AlgebraicGeometry.Space.chartBaseScheme` at which the stalk at `y` is
read after the reduction to schemes: the point of
`AlgebraicGeometry.Space.chartStalkPresentation` at `y`. -/
abbrev chartBasePoint (y : GeometricPoint B S hS Y.1) :
    _root_.AlgebraicGeometry.GeometricPoint (chartBaseScheme B S hS y).1 :=
  (chartStalkPresentation B S hS Y.1 Y.2 y).point

/-- **The reduction of Stacks 0DK3 to Stacks 03QP at a geometric point, as a datum.** A
presentation of the stalk of `π_*F` at `y` by a finite morphism of *schemes*: a scheme
`schemeSource` of the associated big étale site, a finite morphism `schemeMap` from it to the
scheme `AlgebraicGeometry.Space.chartBaseScheme` underlying the chart at `y`, a sheaf of sets
`schemeSheaf` on its small étale site, identifications of the index set of the product and of
both sides' stalks with the scheme-theoretic ones, and the statement that the comparison map
`AlgebraicGeometry.Space.stalkPushforwardToProduct` of this file and the comparison map
`AlgebraicGeometry.finitePushforwardStalkToProduct` of Stacks 03QP correspond under those
identifications.

This is the datum the source's proof constructs: `schemeSource` is `X ×_Y V` for `V` the chart,
`schemeMap` is the base change of `π` — a finite morphism of schemes because `π` is finite and
representable, which is the only place finiteness of `π` is used — and `schemeSheaf` is the
restriction of `F`. The three identifications it carries are of a kind this repository already
proves: the index set is unchanged by base change along a cartesian square, which is
`AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback`, and a geometric stalk of an algebraic
space is a scheme-theoretic étale stalk on a chart, which is
`AlgebraicGeometry.Space.chartEtaleStalkIso` — at the chart that
`AlgebraicGeometry.Space.chartStalkPresentation` chooses, which is why `chartBaseScheme` and
`chartBasePoint` are that chart and that point, while on the side of the lifts a single scheme
`schemeSource` has to serve every lift and so the identification is carried. What is
genuinely assumed is the last field, `comparison`: that the two comparison maps — built
independently, one from `AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso` and the counit
of the small étale adjunction, the other inside the big étale site of schemes — agree under the
transport. Bijectivity of either map is **not** assumed; it is supplied for the scheme-side map
by `AlgebraicGeometry.finitePushforwardStalkToProduct_bijective`. -/
structure PushforwardStalkSchemeComparison (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) where
  /-- The scheme presenting `X` over the chart at `y`; in the source's proof, `X ×_Y V`. -/
  schemeSource : (associatedBigEtaleSite B).Scheme
  /-- The morphism of schemes presenting `π` over the chart at `y`; in the source's proof, the
  base change of `π` along the chart. -/
  schemeMap : schemeSource ⟶ chartBaseScheme B S hS y
  /-- That morphism of schemes is finite. This is the form in which finiteness of `π` enters:
  the base change of a finite morphism of algebraic spaces along a chart is a finite morphism of
  schemes. -/
  isFinite : _root_.AlgebraicGeometry.IsFinite
    ((associatedBigEtaleSite B).inclusion.map schemeMap)
  /-- The sheaf of sets on the small étale site of `schemeSource` presenting `F`; in the source's
  proof, the restriction of `F`. -/
  schemeSheaf : Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    schemeSource.1 schemeSource.2) (Type (u + 1))
  /-- The index set of the product is the scheme-theoretic one: the lifts of `y` to `X` are the
  lifts of the chart point along `schemeMap`. For a cartesian square the corresponding statement
  at the level of algebraic spaces is
  `AlgebraicGeometry.Space.geometricLiftsEquivOfIsPullback`. -/
  indexEquiv : GeometricLifts B S hS π y ≃
    {g : (chartBasePoint B S hS y).source ⟶ schemeSource.1 //
      g ≫ (associatedBigEtaleSite B).inclusion.map schemeMap = (chartBasePoint B S hS y).hom}
  /-- The stalk at `y` of the direct image is the scheme-theoretic étale stalk, at the chart
  point, of the direct image of `schemeSheaf`. The corresponding statement for a stalk of a sheaf
  on `Y_étale` itself is `AlgebraicGeometry.Space.chartEtaleStalkIso`. -/
  baseStalkEquiv : stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj ≃
    _root_.AlgebraicGeometry.etaleStalk (associatedBigEtaleSite B)
      (chartBaseScheme B S hS y).1 (chartBaseScheme B S hS y).2 (chartBasePoint B S hS y)
      (smallEtaleSchemeDirectImage schemeMap schemeSheaf).obj
  /-- The stalk of `F` at a lift of `y` is the scheme-theoretic étale stalk of `schemeSheaf` at
  the corresponding lift of the chart point. The corresponding statement for a stalk of a sheaf
  on `X_étale` is again `AlgebraicGeometry.Space.chartEtaleStalkIso`. -/
  liftStalkEquiv (v : GeometricLifts B S hS π y) :
    stalkSet (geometricLiftPoint B S hS π y v) F.obj ≃
      _root_.AlgebraicGeometry.etaleStalk (associatedBigEtaleSite B)
        schemeSource.1 schemeSource.2
        (_root_.AlgebraicGeometry.geometricPointLift
          ((associatedBigEtaleSite B).inclusion.map schemeMap) (chartBasePoint B S hS y)
          (indexEquiv v))
        schemeSheaf.obj
  /-- **The compatibility square.** The comparison map of this file and the comparison map of
  Stacks 03QP agree under the transport: the component at a lift `v` of the image of a germ `z`
  is the component at `indexEquiv v` of the image of the transported germ. This is the one field
  that is not separately available in this repository, and it is a statement about two
  independently defined maps, not about either of them being bijective. -/
  comparison (z : stalkSet y ((smallToposMorphism B S hS π).pushforward.obj F).obj)
      (v : GeometricLifts B S hS π y) :
    liftStalkEquiv v (stalkPushforwardToProduct B S hS π y F z v) =
      _root_.AlgebraicGeometry.finitePushforwardStalkToProduct (associatedBigEtaleSite B)
        schemeMap (chartBasePoint B S hS y) schemeSheaf (baseStalkEquiv z) (indexEquiv v)

end AlgebraicGeometry.Space

end
