module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Pullback
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of abelian sheaves along an étale morphism of algebraic spaces

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`. Postcomposition with
`f` is a continuous functor `X_étale ⥤ Y_étale` of small étale sites, so restriction of abelian
sheaves along it has a left adjoint, *extension by zero* `f_!`.

## Main definitions

* `AlgebraicGeometry.Space.abelianEtaleRestriction` is `f^{-1}`, restriction along
  postcomposition.
* `AlgebraicGeometry.Space.abelianEtaleExtensionByZero` is `f_!`, the chosen left adjoint of
  restriction.
* `AlgebraicGeometry.Space.abelianEtaleExtensionByZeroAdjunction` is `f_! ⊣ f^{-1}`.
* `AlgebraicGeometry.Space.liftGeometricPoint` is the geometric point of `X` attached to a
  lift of a geometric point of `Y`.
* `AlgebraicGeometry.Space.liftFiberEquiv`: lifting a geometric point of `Y` to an étale
  chart of `X` is the same as lifting it to `X` and then lifting the resulting geometric
  point of `X` to the chart.

## References

* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Postcomposition along an étale morphism of algebraic spaces admits pointwise left Kan
extensions of abelian presheaves. -/
instance hasPointwiseLeftKanExtension_smallEtalePostcomp (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (G : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtalePostcomp B S hS f hf).op.HasPointwiseLeftKanExtension G := fun W => by
  let _ := hasColimitsOfShape_of_essentiallySmall.{u}
    (CostructuredArrow (smallEtalePostcomp B S hS f hf).op W) AddCommGrpCat.{u}
  infer_instance

/-- **Restriction of abelian étale sheaves** along an étale morphism `f : X ⟶ Y` of algebraic
spaces: restriction along postcomposition with `f`. -/
@[stacks 03LP "restriction of abelian sheaves"]
abbrev abelianEtaleRestriction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)

/-- **Extension by zero of abelian étale sheaves** along an étale morphism `f : X ⟶ Y` of
algebraic spaces: the left adjoint of restriction, constructed as the sheafification of the
left Kan extension along postcomposition. -/
@[stacks 03S3 "extension by zero of abelian sheaves"]
def abelianEtaleExtensionByZero (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u} :=
  (smallEtalePostcomp B S hS f hf).sheafPullback AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)

/-- **Extension by zero is left adjoint to restriction** for abelian étale sheaves along an
étale morphism of algebraic spaces. -/
@[stacks 03S3 "the adjunction"]
def abelianEtaleExtensionByZeroAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    abelianEtaleExtensionByZero B S hS f hf ⊣ abelianEtaleRestriction B S hS f hf :=
  Functor.sheafAdjunctionContinuous (smallEtalePostcomp B S hS f hf) AddCommGrpCat.{u}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)

section Lifts

variable {x : GeometricPoint B S hS Y.1}

/-- The geometric point of `X` determined by a lift of a geometric point of `Y`, with the same
field as the point of `Y`. -/
def liftGeometricPoint (f : X ⟶ Y) (t : GeometricPointLift B S hS f.hom x) :
    GeometricPoint B S hS X.1 :=
  ⟨{ carrier := x.val.carrier
     field := x.val.field
     contained := x.val.contained
     toBase := x.val.toBase
     value := t.1 }, x.2⟩

/-- The point of the small étale site of `X` attached to a lift. -/
abbrev liftSitePoint (f : X ⟶ Y) (t : GeometricPointLift B S hS f.hom x) :
    (SmallEtale.topology B S hS X.1).Point.{u} :=
  etaleSitePoint B S hS X.1 (liftGeometricPoint B S hS f t) X.2

/-- The lifts of the geometric point attached to `t` into an étale chart `W` of `X`: the
sections of `W` over the field spectrum of `x` that map to the section `t`. -/
abbrev LiftFiber (f : X ⟶ Y) (t : GeometricPointLift B S hS f.hom x)
    (W : SmallEtale B S hS X.1) : Type u :=
  {p : (x.val.siteObject B S hS Y.1) ⟶ W.obj.left //
    W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) p = t.1}

/-- The fibre of the point attached to a lift is the type of lifts into the chart. -/
theorem liftSitePoint_fiber_obj (f : X ⟶ Y) (t : GeometricPointLift B S hS f.hom x)
    (W : SmallEtale B S hS X.1) :
    (liftSitePoint B S hS f t).fiber.obj W = LiftFiber B S hS f t W :=
  rfl

/-- The section of the chart underlying a lift of the geometric point attached to `t`. -/
abbrev liftFiberVal (f : X ⟶ Y) {t : GeometricPointLift B S hS f.hom x}
    {W : SmallEtale B S hS X.1} (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (x.val.siteObject B S hS Y.1) ⟶ W.obj.left :=
  (show LiftFiber B S hS f t W from w).1

/-- The section underlying a lift maps to the section defining the lifted point. -/
theorem liftFiberVal_spec (f : X ⟶ Y) {t : GeometricPointLift B S hS f.hom x}
    {W : SmallEtale B S hS X.1} (w : (liftSitePoint B S hS f t).fiber.obj W) :
    W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) (liftFiberVal B S hS f w) = t.1 :=
  (show LiftFiber B S hS f t W from w).2

/-- A lift of `x` to `X` together with a lift of the resulting geometric point of `X` to an
étale chart `W` of `X` gives a lift of `x` to `W` viewed as an étale chart of `Y`. -/
def pushLift (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (W : SmallEtale B S hS X.1)
    (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
      ((smallEtalePostcomp B S hS f hf).obj W) :=
  ⟨liftFiberVal B S hS f w, by
    change f.hom.app (op (x.val.siteObject B S hS Y.1))
      (W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) (liftFiberVal B S hS f w)) =
        x.val.value
    rw [liftFiberVal_spec]
    exact t.2⟩

/-- Pushing a lift forward commutes with restriction along a morphism of the small étale site
of `X`. -/
theorem pushLift_map (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {W V : SmallEtale B S hS X.1} (g : W ⟶ V)
    (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (etaleSitePoint B S hS Y.1 x Y.2).fiber.map ((smallEtalePostcomp B S hS f hf).map g)
        (pushLift B S hS f hf W t w) =
      pushLift B S hS f hf V t ((liftSitePoint B S hS f t).fiber.map g w) :=
  Subtype.ext rfl

/-- **The lifts of a geometric point of `Y` to an étale chart of `X`, viewed as a chart of
`Y`, are the pairs consisting of a lift to `X` and a lift of the resulting geometric point of
`X` to the chart.** -/
def liftFiberEquiv (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (W : SmallEtale B S hS X.1) :
    (Σ t : GeometricPointLift B S hS f.hom x,
        (liftSitePoint B S hS f t).fiber.obj W) ≃
      (etaleSitePoint B S hS Y.1 x Y.2).fiber.obj
        ((smallEtalePostcomp B S hS f hf).obj W) where
  toFun tw := pushLift B S hS f hf W tw.1 tw.2
  invFun q := ⟨⟨W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) q.1, q.2⟩, ⟨q.1, rfl⟩⟩
  left_inv := by
    rintro ⟨t, w⟩
    refine Sigma.ext (Subtype.ext (liftFiberVal_spec B S hS f w))
      ((Subtype.heq_iff_coe_eq ?_).2 rfl)
    intro p
    change (W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) p =
        W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) (liftFiberVal B S hS f w)) ↔
      (W.obj.hom.app (op (x.val.siteObject B S hS Y.1)) p = t.1)
    rw [liftFiberVal_spec]
  right_inv q := Subtype.ext rfl

/-- The equivalence `liftFiberEquiv` sends a pair `⟨t, w⟩` to `pushLift f hf W t w`. -/
@[simp]
theorem liftFiberEquiv_apply (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (W : SmallEtale B S hS X.1) (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    liftFiberEquiv B S hS f hf W ⟨t, w⟩ = pushLift B S hS f hf W t w :=
  rfl

end Lifts

end AlgebraicGeometry.Space

end
