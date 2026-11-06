module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroStalk
public import StacksFrontier.CategoryTheory.Sites.Point.LeftAdjointPushforwardFiber
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of extension by zero of sheaves of modules on the small étale site

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`, let
`Λ` be a ring and let `x` be a geometric point of `X`. The stalk at `x` of the extension by zero
`j_!F` of an étale sheaf of `Λ`-modules `F` on `U` is the direct sum of the stalks of `F` at the
lifts of `x` to `U`:
```
  (j_!F)_x = ⨁_{x̄ ↦ U} F_{x̄}     naturally in `F`.
```
This is Stacks 03S5 for sheaves of modules. The stalks are read at the universe lifts of the
points of the small étale sites attached to the geometric points, whose fibres live in the
universe `max (u + 1) r` of the module sections; that is the form in which the stalks of the
change of coefficients of Tag 03TR are compared with the stalks of sheaves of `Λ`-modules.

## Main definitions

* `AlgebraicGeometry.uliftLiftedSitePoint`: the universe lift of the point of the small étale
  site of `U` attached to a lift of `x`.

## Main results

* `AlgebraicGeometry.uliftGeometricPointFiberPostcomposeEquiv`: the lifts of `x` to an étale
  `W ⟶ U` viewed over `X` are the pairs of a lift `x̄` of `x` to `U` and a lift of `x̄` to `W`,
  at the universe of the lifted points.
* `AlgebraicGeometry.moduleExtensionByZeroSheafFiberIso`: **Stacks 03S5 for sheaves of
  modules.** The stalk of `j_!F` at `x` is the direct sum of the stalks of `F` at the lifts.

## Implementation notes

The isomorphism is the instance of
`CategoryTheory.GrothendieckTopology.Point.sheafFiberLeftAdjointIso` at the continuous functor
`AlgebraicGeometry.smallEtalePostcompose` and the adjunction
`AlgebraicGeometry.moduleExtensionByZeroAdjunction` of Tag 03S3; the decomposition of fibres it
asks for is `AlgebraicGeometry.liftFiberEquiv`, lifted to the universe of the points.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (U : SmallEtale B X.obj X.property)
  (x : GeometricPoint X.obj)

/-- The universe lift of the point of the small étale site of `U` attached to a lift `p` of the
geometric point `x` of `X`. -/
abbrev uliftLiftedSitePoint (p : geometricPointLifts B X.obj X.property U x) :
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property).Point.{max (u + 1) r} :=
  (geometricSitePoint B U.obj.left
    (geometricPointOfLift B X.obj X.property U x p)).ulift.{max (u + 1) r}

/-- The lifts of `x` to an étale `W ⟶ U` viewed over `X` are the pairs of a lift `p` of `x` to `U`
and a lift to `W` of the geometric point of `U` that `p` determines, at the universe
`max (u + 1) r` of the lifted points. -/
def uliftGeometricPointFiberPostcomposeEquiv
    (W : SmallEtale B U.obj.left.obj U.obj.left.property) :
    (Σ p : ULift.{max (u + 1) r} (geometricPointLifts B X.obj X.property U x),
        (uliftLiftedSitePoint.{u, r} B X U x p.down).fiber.obj W) ≃
      ((geometricSitePoint B X x).ulift.{max (u + 1) r}).fiber.obj
        ((smallEtalePostcompose B X.obj X.property U).obj W) :=
  (Equiv.sigmaCongr Equiv.ulift (fun _ => Equiv.ulift)).trans
    ((liftFiberEquiv B X.obj X.property U x W).trans Equiv.ulift.symm)

/-- The bijection of lifts commutes with restriction along a morphism of the small étale site of
`U`. -/
lemma uliftGeometricPointFiberPostcomposeEquiv_naturality
    ⦃W V : SmallEtale B U.obj.left.obj U.obj.left.property⦄ (f : W ⟶ V)
    (p : ULift.{max (u + 1) r} (geometricPointLifts B X.obj X.property U x))
    (w : (uliftLiftedSitePoint.{u, r} B X U x p.down).fiber.obj W) :
    ((geometricSitePoint B X x).ulift.{max (u + 1) r}).fiber.map
        ((smallEtalePostcompose B X.obj X.property U).map f)
        (uliftGeometricPointFiberPostcomposeEquiv.{u, r} B X U x W ⟨p, w⟩) =
      uliftGeometricPointFiberPostcomposeEquiv.{u, r} B X U x V
        ⟨p, (uliftLiftedSitePoint.{u, r} B X U x p.down).fiber.map f w⟩ :=
  ULift.ext (pushLift_map B X.obj X.property U x f p.down w.down)

variable (Λ : Type r) [Ring Λ]

/-- **Stacks 03S5 for sheaves of modules.** The stalk at a geometric point `x` of `X` of the
extension by zero along `j : U ⟶ X` of an étale sheaf of `Λ`-modules on `U` is the direct sum of
its stalks at the lifts of `x` to `U`, naturally in the sheaf. The stalks are the fibres at the
universe lifts of the points of the small étale sites attached to the geometric points. -/
@[sga "4 IV 11.3.5" "special case"]
def moduleExtensionByZeroSheafFiberIso :
    moduleExtensionByZero B X.obj X.property U Λ ⋙
        ((geometricSitePoint B X x).ulift.{max (u + 1) r}).sheafFiber ≅
      GrothendieckTopology.Point.sigmaSheafFiber (A := ModuleCat.{max (u + 1) r} Λ)
        (fun p : ULift.{max (u + 1) r} (geometricPointLifts B X.obj X.property U x) =>
          uliftLiftedSitePoint.{u, r} B X U x p.down) :=
  GrothendieckTopology.Point.sheafFiberLeftAdjointIso (A := ModuleCat.{max (u + 1) r} Λ)
    (smallEtalePostcompose B X.obj X.property U)
    ((geometricSitePoint B X x).ulift.{max (u + 1) r})
    (fun p : ULift.{max (u + 1) r} (geometricPointLifts B X.obj X.property U x) =>
      uliftLiftedSitePoint.{u, r} B X U x p.down)
    (uliftGeometricPointFiberPostcomposeEquiv.{u, r} B X U x)
    (uliftGeometricPointFiberPostcomposeEquiv_naturality.{u, r} B X U x)
    (moduleExtensionByZero B X.obj X.property U Λ)
    (moduleExtensionByZeroAdjunction B X.obj X.property U Λ)

end AlgebraicGeometry
