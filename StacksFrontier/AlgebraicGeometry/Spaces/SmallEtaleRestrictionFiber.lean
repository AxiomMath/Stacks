module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# The fibre at a lift of the restriction of a sheaf along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, let `x̄` be a
geometric point of `Y` and let `t` be a lift of `x̄` to `X`.  Restriction of sheaves along `f`
is restriction along postcomposition of étale charts, so the fibre at the point of the small
étale site attached to `t` of the restriction of a sheaf on `Y` is a colimit of the same
sections as the fibre at `x̄` of the sheaf itself, reindexed along postcomposition.  That
reindexing is initial, so the two fibres agree:

`(F|_X)_t = F_x̄`.

This is Stacks' Equation 08GT with coefficients in an arbitrary category with colimits of the
size of the site, in the shape in which a point of a site computes its fibre.

## Main definitions

* `AlgebraicGeometry.Space.liftNeighborhoodPostcomp` is postcomposition from the small étale
  neighbourhoods of the geometric point attached to a lift to the small étale neighbourhoods
  of the original point.
* `AlgebraicGeometry.Space.liftFiberPostcomp` is the same functor read on the categories of
  elements of the two fibre functors: it sends a lift of `t` to an étale chart `W` of `X` to
  the induced lift of `x̄` to `W` viewed as a chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.restrictionPresheafFiberIso`: for the fibre functors of points of the
  small étale site, the fibre at `t` of the restriction of a presheaf on `Y` is its fibre at `x̄`,
  naturally in the presheaf.
* `AlgebraicGeometry.Space.restrictionPresheafFiberIso_toPresheafFiber`: that comparison on
  germs, which characterises it.
* `AlgebraicGeometry.Space.restrictionSheafFiberIso` and
  `AlgebraicGeometry.Space.restrictionSheafFiberIso_toPresheafFiber`: the same for sheaves and
  the restriction functor `AlgebraicGeometry.Space.abelianEtaleRestriction`.

## Implementation notes

The geometric point of `Y` obtained by pushing the geometric point attached to a lift `t`
forward along `f` is the original point `x̄`, but it is not *syntactically* so: its section is
`f ∘ t` rather than `x̄`'s own section, and the two agree only by the defining property of `t`.
The small étale neighbourhoods of the two points therefore have the same charts and the same
lifts and differ only in which proposition the lift is required to satisfy, so
`AlgebraicGeometry.Space.liftImageNeighborhoodEquiv` is the identity on all data.

## References

* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  {x : GeometricPoint B S hS Y.1}

/-- The small étale neighbourhoods of the image under `f` of the geometric point attached to a
lift `t` of `x̄` are the small étale neighbourhoods of `x̄`: the chart and the lift are the same
data, and only the proposition they satisfy is spelled differently. -/
def liftImageNeighborhoodEquiv (t : GeometricPointLift B S hS f.hom x) :
    SmallEtaleNeighborhood (geometricPointMap f.hom (liftGeometricPoint B S hS f t)) ≌
      SmallEtaleNeighborhood x where
  functor :=
    { obj A := ⟨A.chart, A.point, A.point_comp.trans t.2⟩
      map g := ⟨g.hom, g.point_comp⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
  inverse :=
    { obj A := ⟨A.chart, A.point, A.point_comp.trans t.2.symm⟩
      map g := ⟨g.hom, g.point_comp⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
  unitIso := NatIso.ofComponents (fun A => Iso.refl A) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun A => Iso.refl A) (fun _ => rfl)
  functor_unitIso_comp _ := rfl

/-- Postcomposition with `f`, from the small étale neighbourhoods of the geometric point
attached to a lift `t` of `x̄` to the small étale neighbourhoods of `x̄`. -/
def liftNeighborhoodPostcomp (t : GeometricPointLift B S hS f.hom x) :
    SmallEtaleNeighborhood (liftGeometricPoint B S hS f t) ⥤ SmallEtaleNeighborhood x :=
  SmallEtaleNeighborhood.postcomp B S hS f hf (liftGeometricPoint B S hS f t) ⋙
    (liftImageNeighborhoodEquiv B S hS f t).functor

/-- Postcomposition is initial on the neighbourhoods of the point attached to a lift. -/
instance initial_liftNeighborhoodPostcomp (t : GeometricPointLift B S hS f.hom x) :
    (liftNeighborhoodPostcomp B S hS f hf t).Initial :=
  have := SmallEtaleNeighborhood.initial_postcomp B S hS f hf
    (liftGeometricPoint B S hS f t)
  Functor.initial_comp_equivalence _ _

/-- Postcomposition with `f` read on the categories of elements of the two fibre functors: a
lift of the geometric point attached to `t` into an étale chart `W` of `X` goes to the induced
lift of `x̄` into `W` viewed as an étale chart of `Y`. -/
def liftFiberPostcomp (t : GeometricPointLift B S hS f.hom x) :
    (liftSitePoint B S hS f t).fiber.Elements ⥤
      (etaleSitePoint B S hS Y.1 x Y.2).fiber.Elements :=
  (neighborhoodFiberElementsEquiv B S hS X.1 (liftGeometricPoint B S hS f t)).inverse ⋙
    liftNeighborhoodPostcomp B S hS f hf t ⋙
      (neighborhoodFiberElementsEquiv B S hS Y.1 x).functor

/-- The reindexing of elements is initial, postcomposition being initial on neighbourhoods. -/
instance initial_liftFiberPostcomp (t : GeometricPointLift B S hS f.hom x) :
    (liftFiberPostcomp B S hS f hf t).Initial := by
  have : (liftNeighborhoodPostcomp B S hS f hf t ⋙
      (neighborhoodFiberElementsEquiv B S hS Y.1 x).functor).Initial :=
    Functor.initial_comp_equivalence _ _
  have : (neighborhoodFiberElementsEquiv B S hS X.1
      (liftGeometricPoint B S hS f t)).inverse.IsEquivalence :=
    (neighborhoodFiberElementsEquiv B S hS X.1
      (liftGeometricPoint B S hS f t)).symm.isEquivalence_functor
  exact Functor.initial_equivalence_comp
    (neighborhoodFiberElementsEquiv B S hS X.1
      (liftGeometricPoint B S hS f t)).inverse
    (liftNeighborhoodPostcomp B S hS f hf t ⋙
      (neighborhoodFiberElementsEquiv B S hS Y.1 x).functor)

/-- On objects the reindexing is `AlgebraicGeometry.Space.pushLift`. -/
theorem liftFiberPostcomp_obj (t : GeometricPointLift B S hS f.hom x)
    (W : SmallEtale B S hS X.1) (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (liftFiberPostcomp B S hS f hf t).obj ⟨W, w⟩ =
      ⟨(smallEtalePostcomp B S hS f hf).obj W, pushLift B S hS f hf W t w⟩ :=
  rfl

/-- The reindexing of elements covers postcomposition of charts, on the nose. -/
theorem liftFiberPostcomp_comp_π (t : GeometricPointLift B S hS f.hom x) :
    liftFiberPostcomp B S hS f hf t ⋙
        CategoryOfElements.π (etaleSitePoint B S hS Y.1 x Y.2).fiber =
      CategoryOfElements.π (liftSitePoint B S hS f t).fiber ⋙
        smallEtalePostcomp B S hS f hf :=
  rfl

section Fiber

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- For the fibre functors of points of the small étale site, the fibre at the point attached to
a lift `t` of `x̄` of the restriction along `f` of a presheaf on the small étale site of `Y` is
the fibre of that presheaf at `x̄`, naturally in the presheaf. -/
@[stacks 08GT "the fibre of a restriction at a lift"]
def restrictionPresheafFiberIso (t : GeometricPointLift B S hS f.hom x) :
    (Functor.whiskeringLeft (SmallEtale B S hS X.1)ᵒᵖ (SmallEtale B S hS Y.1)ᵒᵖ A).obj
          (smallEtalePostcomp B S hS f hf).op ⋙
        (liftSitePoint B S hS f t).presheafFiber ≅
      (etaleSitePoint B S hS Y.1 x Y.2).presheafFiber :=
  colimIsoOfFinalPrecomp
    (CategoryOfElements.π (etaleSitePoint B S hS Y.1 x Y.2).fiber).op
    (liftFiberPostcomp B S hS f hf t).op

/-- On germs, `AlgebraicGeometry.Space.restrictionPresheafFiberIso` carries the germ at the lift
`t` of a section over an étale chart `W` of `X` to the germ at `x̄` of the same section, read over
the chart `W` of `Y` and at the induced lift. -/
@[stacks 08GT "the comparison on germs"]
theorem restrictionPresheafFiberIso_toPresheafFiber (t : GeometricPointLift B S hS f.hom x)
    (P : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ A) (W : SmallEtale B S hS X.1)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (liftSitePoint B S hS f t).toPresheafFiber W w
          ((smallEtalePostcomp B S hS f hf).op ⋙ P) ≫
        (restrictionPresheafFiberIso B S hS f hf t).hom.app P =
      (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
        ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w) P :=
  Functor.Final.ι_colimitIso_hom (liftFiberPostcomp B S hS f hf t).op
    ((CategoryOfElements.π (etaleSitePoint B S hS Y.1 x Y.2).fiber).op ⋙ P) (op ⟨W, w⟩)

end Fiber

/-- For abelian sheaves, the fibre at the point attached to a lift
`t` of `x̄` of the restriction along `f` of an abelian sheaf on the small étale site of `Y` is
its fibre at `x̄`, naturally in the sheaf. -/
@[stacks 08GT "the fibre of a restriction of abelian sheaves at a lift"]
def restrictionSheafFiberIso (t : GeometricPointLift B S hS f.hom x) :
    abelianEtaleRestriction B S hS f hf ⋙ (liftSitePoint B S hS f t).sheafFiber ≅
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber (A := AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun G => (restrictionPresheafFiberIso B S hS f hf t).app G.obj)
    (fun α => (restrictionPresheafFiberIso B S hS f hf t).hom.naturality α.hom)

/-- On germs, `AlgebraicGeometry.Space.restrictionSheafFiberIso` carries the germ at
the lift `t` of a section over an étale chart `W` of `X` to the germ at `x̄` of the same section
over `W` read as a chart of `Y`, at the induced lift. -/
@[stacks 08GT "the comparison of abelian sheaf fibres on germs"]
theorem restrictionSheafFiberIso_toPresheafFiber (t : GeometricPointLift B S hS f.hom x)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u})
    (W : SmallEtale B S hS X.1) (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (liftSitePoint B S hS f t).toPresheafFiber W w
          ((abelianEtaleRestriction B S hS f hf).obj G).obj ≫
        (restrictionSheafFiberIso B S hS f hf t).hom.app G =
      (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
        ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w) G.obj :=
  restrictionPresheafFiberIso_toPresheafFiber B S hS f hf t G.obj W w

end AlgebraicGeometry.Space

end
