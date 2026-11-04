module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSectionCover

/-!
# The algebraic space of arrows with prescribed endpoints, after enlarging the big fppf site

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space over a scheme
`S` of a big fppf site `B`, let `x`, `y` be two points of the object space over a test object `T`,
and let `B'` be a larger big fppf site, with `i` the localized inclusion and `f` the morphism of
sites it determines.

This file builds the algebraic space whose sections over a test object `W` are the pairs
consisting of a morphism `d : W ⟶ T` and an arrow of `R` over `W` whose target is `y` restricted
along `d` and whose source is `x` restricted along `d`, and records that it stays cartesian after
enlarging the big fppf site.

It is the arrow fibre `R ×_{(t, s), U × U} T` of Stacks 044V, but formed as an iterated fibre
product over the *final* representable algebraic space rather than over `U × U`: the square of the
object space is taken as `U ×_⋆ U`. That is what makes the transport available, because the inverse
image of a fibre product of algebraic spaces is cartesian, while a product would need the further
identification of the inverse image of the final representable algebraic space — which is again
final, and is recorded here.

## Main definitions

* `AlgebraicGeometry.Space.finalOver` and `AlgebraicGeometry.Space.toFinalSpace`: the final object
  of a localized big fppf site and the structural morphism to the algebraic space it represents.
* `AlgebraicGeometry.Space.objectsSquare`: the square of the object space.
* `AlgebraicGeometry.Space.endpointPairSpace` and `AlgebraicGeometry.Space.pointPairSpace`: the
  pair of endpoints of an arrow, and a pair of points of the object space.
* `AlgebraicGeometry.Space.arrowSpace`: the algebraic space of arrows with prescribed endpoints.
* `AlgebraicGeometry.Space.arrowSpaceSection`: the section of the inverse image of the arrow space
  determined by a point of the enlarged site and an arrow with the transported endpoints.

## Main results

* `AlgebraicGeometry.Space.isPullback_objectsSquare`,
  `AlgebraicGeometry.Space.isPullback_arrowSpace` and
  `AlgebraicGeometry.Space.isPullback_changeBigSite_objectsSquare`: the square of the object space
  and the arrow space are cartesian, before and after enlarging the big fppf site.
* `AlgebraicGeometry.Space.isPullback_changeBigSite_arrowSpace`: the arrow space stays cartesian
  after enlarging the big fppf site.
* `AlgebraicGeometry.Space.isTerminal_changeBigSite_finalSpace`: the inverse image of the final
  representable algebraic space is final.
* `AlgebraicGeometry.Space.changeBigSite_map_point_changeBigSiteYonedaHom`: the canonical
  comparison of Stacks 03FP, part (1), followed by the inverse image of a point, is the
  restriction of the transported point.
* `AlgebraicGeometry.Space.arrowSpace_target` and `AlgebraicGeometry.Space.arrowSpace_source`: the
  two endpoint conditions on a section of the arrow space.
* `AlgebraicGeometry.Space.exists_covering_arrow_restrict`: **every arrow of the inverse image of
  the groupoid between transported points is locally a transported arrow**, with both endpoint
  conditions holding over the smaller site.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ u₁

/-- **The Yoneda transpose of a restriction followed by a map of presheaves.** Stated for a
generic category, where it is a composition of the two halves of the Yoneda correspondence. -/
theorem yonedaEquiv_restrict_comp {C : Type u₁} [Category.{v₁} C] {A V : C}
    {P Q : Cᵒᵖ ⥤ Type v₁} (ξ : V ⟶ A) (η : yoneda.obj A ⟶ P) (ψ : P ⟶ Q) :
    yonedaEquiv ((yoneda.map ξ ≫ η) ≫ ψ) = ψ.app (op V) (η.app (op V) ξ) := by
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **The Yoneda transpose of a restriction.** -/
theorem yonedaEquiv_restrict {C : Type u₁} [Category.{v₁} C] {A V : C}
    {P : Cᵒᵖ ⥤ Type v₁} (ξ : V ⟶ A) (η : yoneda.obj A ⟶ P) :
    yonedaEquiv (yoneda.map ξ ≫ η) = η.app (op V) ξ := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **The Yoneda transpose of a section followed by a map of presheaves.** -/
theorem yonedaEquiv_sectionComp {C : Type u₁} [Category.{v₁} C] {V : C}
    {P Q : Cᵒᵖ ⥤ Type v₁} (s : P.obj (op V)) (ψ : P ⟶ Q) :
    yonedaEquiv (yonedaEquiv.symm s ≫ ψ) = ψ.app (op V) s := by
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- **Naturality of a map of presheaves out of a representable, read on a restriction.** -/
theorem yoneda_naturality_restrict {C : Type u₁} [Category.{v₁} C] {A V V' : C}
    {P : Cᵒᵖ ⥤ Type v₁} (η : yoneda.obj A ⟶ P) (ξ : V ⟶ A) (β : V' ⟶ V) :
    η.app (op V') (β ≫ ξ) = P.map β.op (η.app (op V) ξ) := by
  have h := NatTrans.naturality_apply η β.op ξ
  simpa using h

/-- **Regrouping a restriction against a composite of maps of presheaves.** -/
theorem yoneda_map_comp_assoc {C : Type u₁} [Category.{v₁} C] {A V : C}
    {P Q R : Cᵒᵖ ⥤ Type v₁} (ξ : V ⟶ A) (η : yoneda.obj A ⟶ P) (ψ : P ⟶ Q) (χ : Q ⟶ R) :
    ((yoneda.map ξ ≫ η) ≫ ψ) ≫ χ = (yoneda.map ξ ≫ η) ≫ (ψ ≫ χ) := Category.assoc _ _ _

/-- **Regrouping a section against a composite of maps of presheaves.** -/
theorem yonedaEquiv_sectionComp_assoc {C : Type u₁} [Category.{v₁} C] {V : C}
    {P Q R : Cᵒᵖ ⥤ Type v₁} (s : P.obj (op V)) (ψ : P ⟶ Q) (χ : Q ⟶ R) :
    (yonedaEquiv.symm s ≫ ψ) ≫ χ = yonedaEquiv.symm s ≫ (ψ ≫ χ) := Category.assoc _ _ _

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

section Small

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Composition of morphisms of algebraic spaces is composition of the underlying maps. -/
theorem comp_hom {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b).hom = a.hom ≫ b.hom := rfl

/-- The final object of a localized big fppf site: the base over itself. -/
abbrev finalOver : BigFppfOver B S hS := Over.mk (𝟙 (base (τ := .fppf) B S hS))

/-- The sheaf represented by the final object of a localized big fppf site is final. -/
def isTerminal_yoneda_finalOver :
    IsTerminal (yoneda.obj (finalOver B S hS) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (Over.mkIdTerminal : IsTerminal (finalOver B S hS)).isTerminalObj yoneda _

/-- The structural morphism of an algebraic space to the final representable one. -/
def toFinalSpace (X : AlgebraicSpaces B S hS) :
    X ⟶ (schemeSpaceFunctor B S hS).obj (finalOver B S hS) :=
  ObjectProperty.homMk ((isTerminal_yoneda_finalOver B S hS).from X.obj)

/-- The structural morphism to the final representable algebraic space is the only one. -/
theorem toFinalSpace_unique {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (schemeSpaceFunctor B S hS).obj (finalOver B S hS)) : f = toFinalSpace B S hS X := by
  refine ObjectProperty.hom_ext _ ?_
  exact (isTerminal_yoneda_finalOver B S hS).hom_ext _ _

variable {Bs : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The square of the object space of a groupoid in algebraic spaces**, formed as the fibre
product over the final representable algebraic space, so that it is again an algebraic space
without appeal to products. -/
abbrev objectsSquare : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS
    (toFinalSpace B S hS G.objects) (toFinalSpace B S hS G.objects)

/-- The first projection of the square of the object space. -/
abbrev objectsSquareFst : objectsSquare B S hS G ⟶ G.objects :=
  ObjectProperty.homMk (pullback.fst (toFinalSpace B S hS G.objects).hom
    (toFinalSpace B S hS G.objects).hom)

/-- The second projection of the square of the object space. -/
abbrev objectsSquareSnd : objectsSquare B S hS G ⟶ G.objects :=
  ObjectProperty.homMk (pullback.snd (toFinalSpace B S hS G.objects).hom
    (toFinalSpace B S hS G.objects).hom)

/-- The square of the object space is cartesian over the final representable algebraic space. -/
theorem isPullback_objectsSquare :
    IsPullback (objectsSquareFst B S hS G) (objectsSquareSnd B S hS G)
      (toFinalSpace B S hS G.objects) (toFinalSpace B S hS G.objects) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- **The pair of endpoints of an arrow**, as a morphism from the arrow space to the square of the
object space. -/
def endpointPairSpace : G.arrows ⟶ objectsSquare B S hS G :=
  (isPullback_objectsSquare B S hS G).lift G.target G.source
    ((toFinalSpace_unique B S hS _).trans (toFinalSpace_unique B S hS _).symm)

/-- **A pair of points of the object space**, as a morphism from the representable algebraic space
of the test object to the square of the object space. -/
def pointPairSpace (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    (schemeSpaceFunctor B S hS).obj T ⟶ objectsSquare B S hS G :=
  (isPullback_objectsSquare B S hS G).lift
    (ObjectProperty.homMk (yonedaEquiv.symm y)) (ObjectProperty.homMk (yonedaEquiv.symm x))
    ((toFinalSpace_unique B S hS _).trans (toFinalSpace_unique B S hS _).symm)

/-- The pair of endpoints has the target as its first component. -/
theorem endpointPairSpace_fst :
    endpointPairSpace B S hS G ≫ objectsSquareFst B S hS G = G.target :=
  (isPullback_objectsSquare B S hS G).lift_fst _ _ _

/-- The pair of endpoints has the source as its second component. -/
theorem endpointPairSpace_snd :
    endpointPairSpace B S hS G ≫ objectsSquareSnd B S hS G = G.source :=
  (isPullback_objectsSquare B S hS G).lift_snd _ _ _

/-- The pair of points has `y` as its first component. -/
theorem pointPairSpace_fst (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    pointPairSpace B S hS G T x y ≫ objectsSquareFst B S hS G =
      ObjectProperty.homMk (yonedaEquiv.symm y) :=
  (isPullback_objectsSquare B S hS G).lift_fst _ _ _

/-- The pair of points has `x` as its second component. -/
theorem pointPairSpace_snd (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    pointPairSpace B S hS G T x y ≫ objectsSquareSnd B S hS G =
      ObjectProperty.homMk (yonedaEquiv.symm x) :=
  (isPullback_objectsSquare B S hS G).lift_snd _ _ _

/-- **The algebraic space of arrows with prescribed endpoints.** Its sections over a test object
`W` are the pairs consisting of a morphism `d : W ⟶ T` and an arrow over `W` whose target is the
restriction of `y` along `d` and whose source is the restriction of `x` along `d`. -/
abbrev arrowSpace (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS
    (pointPairSpace B S hS G T x y) (endpointPairSpace B S hS G)

/-- The projection of the arrow space to the representable algebraic space of the test object. -/
abbrev arrowSpaceFst (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    arrowSpace B S hS G T x y ⟶ (schemeSpaceFunctor B S hS).obj T :=
  ObjectProperty.homMk (pullback.fst (pointPairSpace B S hS G T x y).hom
    (endpointPairSpace B S hS G).hom)

/-- The projection of the arrow space to the arrow space of the groupoid. -/
abbrev arrowSpaceSnd (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    arrowSpace B S hS G T x y ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.snd (pointPairSpace B S hS G T x y).hom
    (endpointPairSpace B S hS G).hom)

/-- The arrow space is cartesian over the square of the object space. -/
theorem isPullback_arrowSpace (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    IsPullback (arrowSpaceFst B S hS G T x y) (arrowSpaceSnd B S hS G T x y)
      (pointPairSpace B S hS G T x y) (endpointPairSpace B S hS G) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The first component of a section of the arrow space has `y` restricted along it as the target
of the second. -/
theorem arrowSpace_comp_target (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    arrowSpaceFst B S hS G T x y ≫ ObjectProperty.homMk (yonedaEquiv.symm y) =
      arrowSpaceSnd B S hS G T x y ≫ G.target := by
  rw [← pointPairSpace_fst B S hS G T x y, ← endpointPairSpace_fst B S hS G,
    ← Category.assoc, ← Category.assoc, (isPullback_arrowSpace B S hS G T x y).w]

/-- The first component of a section of the arrow space has `x` restricted along it as the source
of the second. -/
theorem arrowSpace_comp_source (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T)) :
    arrowSpaceFst B S hS G T x y ≫ ObjectProperty.homMk (yonedaEquiv.symm x) =
      arrowSpaceSnd B S hS G T x y ≫ G.source := by
  rw [← pointPairSpace_snd B S hS G T x y, ← endpointPairSpace_snd B S hS G,
    ← Category.assoc, ← Category.assoc, (isPullback_arrowSpace B S hS G T x y).w]

/-- A section of the arrow space satisfies an endpoint condition, given the matching equation of
maps out of the arrow space. -/
private theorem arrowSpace_apply_eq (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T))
    (z : G.objects.obj.obj (op T)) (m : G.arrows ⟶ G.objects)
    (h : arrowSpaceFst B S hS G T x y ≫ ObjectProperty.homMk (yonedaEquiv.symm z) =
      arrowSpaceSnd B S hS G T x y ≫ m)
    (W : BigFppfOver B S hS) (w : (arrowSpace B S hS G T x y).obj.obj (op W)) :
    m.hom.app (op W) ((arrowSpaceSnd B S hS G T x y).hom.app (op W) w) =
      G.objects.obj.map ((arrowSpaceFst B S hS G T x y).hom.app (op W) w).op z := by
  have h0 := congrArg (fun (f : arrowSpace B S hS G T x y ⟶ G.objects) =>
    f.hom.app (op W) w) h
  simp only [comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at h0
  rw [← h0]
  exact (yonedaEquiv_symm_app_apply z (op W) _).symm

/-- **The target condition on a section of the arrow space.** -/
theorem arrowSpace_target (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T))
    (W : BigFppfOver B S hS) (w : (arrowSpace B S hS G T x y).obj.obj (op W)) :
    G.target.hom.app (op W) ((arrowSpaceSnd B S hS G T x y).hom.app (op W) w) =
      G.objects.obj.map ((arrowSpaceFst B S hS G T x y).hom.app (op W) w).op y :=
  arrowSpace_apply_eq B S hS G T x y y _ (arrowSpace_comp_target B S hS G T x y) W w

/-- **The source condition on a section of the arrow space.** -/
theorem arrowSpace_source (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T))
    (W : BigFppfOver B S hS) (w : (arrowSpace B S hS G T x y).obj.obj (op W)) :
    G.source.hom.app (op W) ((arrowSpaceSnd B S hS G T x y).hom.app (op W) w) =
      G.objects.obj.map ((arrowSpaceFst B S hS G T x y).hom.app (op W) w).op x :=
  arrowSpace_apply_eq B S hS G T x y x _ (arrowSpace_comp_source B S hS G T x y) W w

end Small

section Change

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- The inverse image of the final representable algebraic space is final. -/
def isTerminal_changeBigSite_finalSpace :
    IsTerminal (((changeBigSite B B' h S hS).obj
      ((schemeSpaceFunctor B S hS).obj (finalOver B S hS))).obj) :=
  IsTerminal.ofIso (isTerminal_yoneda_finalOver B' S (largerContains h hS))
    (changeBigSiteYonedaIso B B' h S hS (finalOver B S hS))

/-- The square of the object space stays cartesian after enlarging the big fppf site. -/
theorem isPullback_changeBigSite_objectsSquare :
    IsPullback
      ((changeBigSite B B' h S hS).map (objectsSquareFst B S hS G)).hom
      ((changeBigSite B B' h S hS).map (objectsSquareSnd B S hS G)).hom
      ((changeBigSite B B' h S hS).map (toFinalSpace B S hS G.objects)).hom
      ((changeBigSite B B' h S hS).map (toFinalSpace B S hS G.objects)).hom :=
  isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS _ _

/-- The arrow space stays cartesian after enlarging the big fppf site. -/
theorem isPullback_changeBigSite_arrowSpace (T : BigFppfOver B S hS)
    (x y : G.objects.obj.obj (op T)) :
    IsPullback
      ((changeBigSite B B' h S hS).map (arrowSpaceFst B S hS G T x y)).hom
      ((changeBigSite B B' h S hS).map (arrowSpaceSnd B S hS G T x y)).hom
      ((changeBigSite B B' h S hS).map (pointPairSpace B S hS G T x y)).hom
      ((changeBigSite B B' h S hS).map (endpointPairSpace B S hS G)).hom :=
  isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS _ _

/-- **The canonical comparison of Stacks 03FP, part (1), followed by the inverse image of a point,
is the restriction of the transported point.** -/
theorem changeBigSite_map_point_changeBigSiteYonedaHom (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (y : X.obj.obj (op T))
    (V : BigFppfOver B' S (largerContains h hS)) (ξ : V ⟶ (inclusionOver h S hS).obj T) :
    ((changeBigSite B B' h S hS).map
        (ObjectProperty.homMk (yonedaEquiv.symm y) :
          (schemeSpaceFunctor B S hS).obj T ⟶ X)).hom.app (op V)
        ((changeBigSiteYonedaHom B B' h S hS T).app (op V) ξ) =
      ((changeBigSite B B' h S hS).obj X).obj.map ξ.op
        (changeBigSiteSectionEquiv B B' h S hS X T y) := by
  have e1 := changeBigSiteYonedaHom_app B B' h S hS T V ξ
  have e2 := NatTrans.naturality_apply
    ((changeBigSite B B' h S hS).map
      (ObjectProperty.homMk (yonedaEquiv.symm y) :
        (schemeSpaceFunctor B S hS).obj T ⟶ X)).hom ξ.op
    (changeBigSiteSectionEquiv B B' h S hS
      ((schemeSpaceFunctor B S hS).obj T) T (𝟙 T))
  have e3 := changeBigSiteSectionEquiv_map B B' h S hS
    (ObjectProperty.homMk (yonedaEquiv.symm y) :
      (schemeSpaceFunctor B S hS).obj T ⟶ X) T (𝟙 T)
  have e4 : (ObjectProperty.homMk (yonedaEquiv.symm y) :
      (schemeSpaceFunctor B S hS).obj T ⟶ X).hom.app (op T) (𝟙 T) = y := by
    have h0 : yonedaEquiv (yonedaEquiv.symm y) = y := yonedaEquiv.apply_symm_apply y
    rw [yonedaEquiv_apply] at h0
    exact h0
  rw [e1, e2, ← e3, e4]

/-- Enlarging the big fppf site commutes with composition, on the underlying maps. -/
theorem changeBigSite_map_comp_hom {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) :
    ((changeBigSite B B' h S hS).map a).hom ≫ ((changeBigSite B B' h S hS).map b).hom =
      ((changeBigSite B B' h S hS).map (a ≫ b)).hom := by
  rw [Functor.map_comp]
  rfl

variable (T : BigFppfOver B S hS) (x y : G.objects.obj.obj (op T))
  (V : BigFppfOver B' S (largerContains h hS))
  (ξ : V ⟶ (inclusionOver h S hS).obj T)
  (r : ((changeBigSite B B' h S hS).obj G.arrows).obj.obj (op V))
  (hy : ((changeBigSite B B' h S hS).map G.target).hom.app (op V) r =
    ((changeBigSite B B' h S hS).obj G.objects).obj.map ξ.op
      (changeBigSiteSectionEquiv B B' h S hS G.objects T y))
  (hx : ((changeBigSite B B' h S hS).map G.source).hom.app (op V) r =
    ((changeBigSite B B' h S hS).obj G.objects).obj.map ξ.op
      (changeBigSiteSectionEquiv B B' h S hS G.objects T x))

include hy hx in
/-- **The point and the arrow agree over the square of the object space.** This is the
compatibility that makes them a section of the inverse image of the arrow space: the two
projections of the square are checked separately, and on each the comparison of Stacks 03FP,
part (1) turns the transported point into the restriction of the transported point. -/
theorem changeBigSite_pointPairSpace_comm :
    (yoneda.map ξ ≫ changeBigSiteYonedaHom B B' h S hS T) ≫
        ((changeBigSite B B' h S hS).map (pointPairSpace B S hS G T x y)).hom =
      yonedaEquiv.symm r ≫
        ((changeBigSite B B' h S hS).map (endpointPairSpace B S hS G)).hom := by
  have key : ∀ (z : G.objects.obj.obj (op T)) (m : G.arrows ⟶ G.objects)
      (pr : objectsSquare B S hS G ⟶ G.objects),
      pointPairSpace B S hS G T x y ≫ pr =
        (ObjectProperty.homMk (yonedaEquiv.symm z) :
          (schemeSpaceFunctor B S hS).obj T ⟶ G.objects) →
      endpointPairSpace B S hS G ≫ pr = m →
      ((changeBigSite B B' h S hS).map m).hom.app (op V) r =
        ((changeBigSite B B' h S hS).obj G.objects).obj.map ξ.op
          (changeBigSiteSectionEquiv B B' h S hS G.objects T z) →
      ((yoneda.map ξ ≫ changeBigSiteYonedaHom B B' h S hS T) ≫
          ((changeBigSite B B' h S hS).map (pointPairSpace B S hS G T x y)).hom) ≫
          ((changeBigSite B B' h S hS).map pr).hom =
        (yonedaEquiv.symm r ≫
          ((changeBigSite B B' h S hS).map (endpointPairSpace B S hS G)).hom) ≫
          ((changeBigSite B B' h S hS).map pr).hom := by
    intro z m pr hp he hm
    refine Eq.trans (yoneda_map_comp_assoc _ _ _ _) ?_
    refine Eq.trans ?_ (yonedaEquiv_sectionComp_assoc _ _ _).symm
    refine Eq.trans (congrArg
      (fun g => (yoneda.map ξ ≫ changeBigSiteYonedaHom B B' h S hS T) ≫ g)
      ((changeBigSite_map_comp_hom B B' h S hS _ pr).trans
        (congrArg (fun f : (changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T) ⟶
          (changeBigSite B B' h S hS).obj G.objects => f.hom)
          (congrArg (changeBigSite B B' h S hS).map hp)))) ?_
    refine Eq.trans ?_ (congrArg (fun g => yonedaEquiv.symm r ≫ g)
      ((changeBigSite_map_comp_hom B B' h S hS _ pr).trans
        (congrArg (fun f : (changeBigSite B B' h S hS).obj G.arrows ⟶
          (changeBigSite B B' h S hS).obj G.objects => f.hom)
          (congrArg (changeBigSite B B' h S hS).map he)))).symm
    refine yonedaEquiv.injective ?_
    refine Eq.trans (yonedaEquiv_restrict_comp ξ _ _) ?_
    refine Eq.trans ?_ (yonedaEquiv_sectionComp r _).symm
    exact (changeBigSite_map_point_changeBigSiteYonedaHom B B' h S hS G.objects T z V ξ).trans
      hm.symm
  exact (isPullback_changeBigSite_objectsSquare B B' h S hS G).hom_ext
    (key y G.target (objectsSquareFst B S hS G) (pointPairSpace_fst B S hS G T x y)
      (endpointPairSpace_fst B S hS G) hy)
    (key x G.source (objectsSquareSnd B S hS G) (pointPairSpace_snd B S hS G T x y)
      (endpointPairSpace_snd B S hS G) hx)

include hy hx in
/-- **The section of the inverse image of the arrow space determined by a point of the enlarged
site and an arrow with the transported endpoints.** -/
def arrowSpaceSection :
    yoneda.obj V ⟶ ((changeBigSite B B' h S hS).obj (arrowSpace B S hS G T x y)).obj :=
  (isPullback_changeBigSite_arrowSpace B B' h S hS G T x y).lift
    (yoneda.map ξ ≫ changeBigSiteYonedaHom B B' h S hS T) (yonedaEquiv.symm r)
    (changeBigSite_pointPairSpace_comm B B' h S hS G T x y V ξ r hy hx)

include hy hx in
/-- The section projects to the given point of the enlarged site. -/
theorem arrowSpaceSection_fst :
    arrowSpaceSection B B' h S hS G T x y V ξ r hy hx ≫
        ((changeBigSite B B' h S hS).map (arrowSpaceFst B S hS G T x y)).hom =
      yoneda.map ξ ≫ changeBigSiteYonedaHom B B' h S hS T :=
  IsPullback.lift_fst _ _ _ _

include hy hx in
/-- The section projects to the given arrow. -/
theorem arrowSpaceSection_snd :
    arrowSpaceSection B B' h S hS G T x y V ξ r hy hx ≫
        ((changeBigSite B B' h S hS).map (arrowSpaceSnd B S hS G T x y)).hom =
      yonedaEquiv.symm r :=
  IsPullback.lift_snd _ _ _ _

include hy hx in
/-- **Every arrow of the inverse image of a groupoid in algebraic spaces between transported
points is locally a transported arrow.** Along a covering sieve of the test object of the enlarged
site, the arrow is the restriction, along a morphism to the image of a test object of the smaller
site, of the transport of an arrow there — and over that test object both endpoint conditions hold
and the given morphism factors.

This is the inverse image of the morphism presheaf of a quotient stack read on arrows: by
Stacks 044V an arrow with prescribed endpoints is a section of the arrow space, which is an
algebraic space, so the statement is the local description of sections of an inverse image of
Stacks 04W1 applied to it. -/
theorem exists_covering_arrow_restrict :
    ∃ R ∈ BigFppfOver.topology B' S (largerContains h hS) V,
      ∀ ⦃V' : BigFppfOver B' S (largerContains h hS)⦄ ⦃β : V' ⟶ V⦄, R.arrows β →
        ∃ (W : BigFppfOver B S hS) (d : W ⟶ T)
          (χ : V' ⟶ (inclusionOver h S hS).obj W) (r₀ : G.arrows.obj.obj (op W)),
          χ ≫ (inclusionOver h S hS).map d = β ≫ ξ ∧
          G.target.hom.app (op W) r₀ = G.objects.obj.map d.op y ∧
          G.source.hom.app (op W) r₀ = G.objects.obj.map d.op x ∧
          ((changeBigSite B B' h S hS).obj G.arrows).obj.map β.op r =
            ((changeBigSite B B' h S hS).obj G.arrows).obj.map χ.op
              (changeBigSiteSectionEquiv B B' h S hS G.arrows W r₀) := by
  obtain ⟨W, w, R, hR, hspec⟩ := exists_sectionEquiv_restrict B B' h S hS
    (arrowSpace B S hS G T x y) V
    (yonedaEquiv (arrowSpaceSection B B' h S hS G T x y V ξ r hy hx))
  refine ⟨R, hR, ?_⟩
  intro V' β hβ
  obtain ⟨φ, hφ⟩ := hspec β hβ
  have key : ∀ {X : AlgebraicSpaces B S hS} (p : arrowSpace B S hS G T x y ⟶ X),
      ((changeBigSite B B' h S hS).obj X).obj.map β.op
          (((changeBigSite B B' h S hS).map p).hom.app (op V)
            (yonedaEquiv (arrowSpaceSection B B' h S hS G T x y V ξ r hy hx))) =
        ((changeBigSite B B' h S hS).obj X).obj.map φ.op
          (changeBigSiteSectionEquiv B B' h S hS X W (p.hom.app (op W) w)) := by
    intro X p
    have h1 := congrArg (fun z => ((changeBigSite B B' h S hS).map p).hom.app (op V') z) hφ
    simp only at h1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
      ← changeBigSiteSectionEquiv_map B B' h S hS p W w] at h1
    exact h1
  refine ⟨W, (arrowSpaceFst B S hS G T x y).hom.app (op W) w, φ,
    (arrowSpaceSnd B S hS G T x y).hom.app (op W) w, ?_,
    arrowSpace_target B S hS G T x y W w, arrowSpace_source B S hS G T x y W w, ?_⟩
  · have h1 := key (arrowSpaceFst B S hS G T x y)
    have e1 : ((changeBigSite B B' h S hS).map
        (arrowSpaceFst B S hS G T x y)).hom.app (op V)
        (yonedaEquiv (arrowSpaceSection B B' h S hS G T x y V ξ r hy hx)) =
        (changeBigSiteYonedaHom B B' h S hS T).app (op V) ξ :=
      ((yonedaEquiv_comp _ _).symm.trans (congrArg yonedaEquiv
        (arrowSpaceSection_fst B B' h S hS G T x y V ξ r hy hx))).trans
        (yonedaEquiv_restrict ξ (changeBigSiteYonedaHom B B' h S hS T))
    rw [e1] at h1
    have hinj : Function.Injective
        ((changeBigSiteYonedaHom B B' h S hS T).app (op V')) := by
      have hio := isIso_changeBigSiteYonedaHom B B' h S hS T
      have : IsIso ((changeBigSiteYonedaHom B B' h S hS T).app (op V')) :=
        NatIso.isIso_app_of_isIso (changeBigSiteYonedaHom B B' h S hS T) (op V')
      exact (ConcreteCategory.bijective_of_isIso _).injective
    refine hinj ?_
    refine Eq.trans (yoneda_naturality_restrict _ ((inclusionOver h S hS).map
      ((arrowSpaceFst B S hS G T x y).hom.app (op W) w)) φ) ?_
    refine Eq.trans (congrArg (fun z => (((changeBigSite B B' h S hS).obj
      ((schemeSpaceFunctor B S hS).obj T)).obj.map φ.op) z)
      (changeBigSiteYonedaHom_app_map B B' h S hS T W
        ((arrowSpaceFst B S hS G T x y).hom.app (op W) w))) ?_
    exact h1.symm.trans (yoneda_naturality_restrict _ ξ β).symm
  · have h4 := key (arrowSpaceSnd B S hS G T x y)
    have e1 : ((changeBigSite B B' h S hS).map
        (arrowSpaceSnd B S hS G T x y)).hom.app (op V)
        (yonedaEquiv (arrowSpaceSection B B' h S hS G T x y V ξ r hy hx)) = r :=
      ((yonedaEquiv_comp _ _).symm.trans (congrArg yonedaEquiv
        (arrowSpaceSection_snd B B' h S hS G T x y V ξ r hy hx))).trans
        (yonedaEquiv.apply_symm_apply r)
    rwa [e1] at h4

end Change

end AlgebraicGeometry.Space

end
