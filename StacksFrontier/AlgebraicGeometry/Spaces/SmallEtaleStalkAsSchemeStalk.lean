module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfSmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# The geometric stalk of an algebraic space is a scheme-theoretic étale stalk

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `x` be
a geometric point of `F`.  The stalk at `x` of a sheaf on the small étale site of `F` is
`AlgebraicGeometry.Space.stalkSet`, a colimit over the small étale neighbourhoods of `x`
(Stacks 04JY).  For a *scheme* the corresponding object is `AlgebraicGeometry.etaleStalk`, a
colimit over the étale neighbourhoods of a geometric point inside a big étale site
(Stacks 040R).

After choosing an étale chart `X` of `F` through `x`, a sheaf on `F_étale` restricts to a sheaf
on the small étale site of the scheme underlying `X`, taken in the associated big étale site, and
the stalk at `x` is the étale stalk of that restriction at a geometric point of that scheme.

## Main definitions

* `AlgebraicGeometry.Space.ChartStalkPresentation`: the chart, the chart identification, the
  geometric point of the underlying scheme and the comparison, as one datum.
* `AlgebraicGeometry.Space.chartStalkPresentation`: a chosen such datum.
* `AlgebraicGeometry.Space.chartStalkFunctorIso` and
  `AlgebraicGeometry.Space.chartEtaleStalkIso`: the comparison as a named isomorphism, of
  functors and objectwise.

## Main results

* `AlgebraicGeometry.Space.exists_chart_stalkSetFunctor_iso_schemeStalk`: the geometric stalk
  functor of `x` on sheaves of sets is, on a chart, the scheme-theoretic étale stalk functor at
  a geometric point of the scheme underlying the chart.
* `AlgebraicGeometry.Space.exists_chart_stalkSet_equiv_etaleStalk`: the same objectwise, with
  the right-hand side named as `AlgebraicGeometry.etaleStalk`.
* `AlgebraicGeometry.Space.nonempty_chartStalkPresentation`: the two statements above, repackaged
  as nonemptiness of the datum type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The point of the small étale topos of `F` attached to a geometric point `x` of `F`: the
point of the site of Stacks 04K0, raised to the universe of the coefficients and read as a
morphism of topoi. -/
def geometricPointOfTopos (x : GeometricPoint B S hS F) (hF : IsAlgebraicSpace B S hS F) :
    PointOfTopos.{u + 1} (SmallEtale.topology B S hS F) :=
  ((etaleSitePoint B S hS F x hF).ulift.{u + 1}).pointOfTopos

/-- The inverse image of the point of the topos attached to a geometric point is the geometric
stalk functor of Stacks 04JY. -/
def geometricPointOfToposInverseImageIso (x : GeometricPoint B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    (geometricPointOfTopos B S hS F x hF).inverseImage ≅
      sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙ stalkSetFunctor x :=
  Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)))
    (GrothendieckTopology.Point.uliftPresheafFiberIso.{u + 1, u, _, _, _, _}
        (etaleSitePoint B S hS F x hF) ≪≫
      etaleSitePointStalkIso B S hS F x hF)

/-- **The geometric stalk of an algebraic space, computed on a chart as a scheme-theoretic étale
stalk.**  For a geometric point `x` of an algebraic space `F` there are an étale chart `X` of
`F`, the identification `e` of the small étale site of `F` over `X` with the small étale site of
the representing object (Stacks 04M0), and a geometric point `s` of the *scheme* underlying `X`,
such that the set-valued geometric stalk functor `AlgebraicGeometry.Space.stalkSetFunctor x` of
Stacks 04JY is restriction of a sheaf along the chart followed by the étale stalk at `s` of
Stacks 040R. -/
theorem exists_chart_stalkSetFunctor_iso_schemeStalk (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    ∃ (X : SmallEtale B S hS F)
      (e : SmallEtale B S hS (yoneda.obj X.obj.left) ≌ Over X),
      (e.functor ⋙ Over.post (SmallEtale.toOver B S hS F ⋙ yoneda) =
        SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
          CostructuredArrow.toOver yoneda (yoneda.obj X.obj.left)) ∧
      ∃ s : _root_.AlgebraicGeometry.GeometricPoint
        ((BigFppfOver.toScheme B S hS).obj X.obj.left),
      Nonempty (sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙
          stalkSetFunctor x ≅
        sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          ((representedSmallEtaleEquivalence B S hS X.obj.left).inverse ⋙
            e.functor ⋙ Over.forget X).op ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Functor.Elements.π (geometricPointFiber (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj X.obj.left)
            X.obj.left.left.property s)).op ⋙ colim) :=
  let ⟨X, e, he, s, ⟨hs⟩⟩ :=
    exists_chart_geometric_stalk B S hS F hF (geometricPointOfTopos B S hS F x hF)
  ⟨X, e, he, s, ⟨(geometricPointOfToposInverseImageIso B S hS F x hF).symm ≪≫ hs⟩⟩

/-- **The geometric stalk of an algebraic space at a geometric point is an étale stalk of a
scheme**, objectwise: in the situation of
`AlgebraicGeometry.Space.exists_chart_stalkSetFunctor_iso_schemeStalk`, the stalk at `x` of a
sheaf of sets `G` on `F_étale` is isomorphic to `AlgebraicGeometry.etaleStalk` of Stacks 040R,
at the geometric point `s` of the scheme underlying the chart, of the restriction of `G` to the
small étale site of that scheme. -/
theorem exists_chart_stalkSet_equiv_etaleStalk (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    ∃ (X : SmallEtale B S hS F)
      (e : SmallEtale B S hS (yoneda.obj X.obj.left) ≌ Over X),
      (e.functor ⋙ Over.post (SmallEtale.toOver B S hS F ⋙ yoneda) =
        SmallEtale.inclusion B S hS (yoneda.obj X.obj.left) ⋙
          CostructuredArrow.toOver yoneda (yoneda.obj X.obj.left)) ∧
      ∃ s : _root_.AlgebraicGeometry.GeometricPoint
        ((BigFppfOver.toScheme B S hS).obj X.obj.left),
      ∀ G : Sheaf (SmallEtale.topology B S hS F) (Type (u + 1)),
        Nonempty (stalkSet x G.obj ≅
          _root_.AlgebraicGeometry.etaleStalk (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj X.obj.left) X.obj.left.left.property s
            (((representedSmallEtaleEquivalence B S hS X.obj.left).inverse ⋙
              e.functor ⋙ Over.forget X).op ⋙ G.obj)) :=
  let ⟨X, e, he, s, ⟨hs⟩⟩ := exists_chart_stalkSetFunctor_iso_schemeStalk B S hS F hF x
  ⟨X, e, he, s, fun G => ⟨hs.app G⟩⟩

/-! ### The same reduction as data -/

/-- The reduction of the geometric stalk at `x` to a scheme-theoretic étale stalk, as data: an
étale chart `X` of `F`, the identification `e` of the small étale site of `F` over `X` with the
small étale site of the representing object (Stacks 04M0), a geometric point `s` of the scheme
underlying `X`, and an isomorphism of functors exhibiting the set-valued geometric stalk functor
at `x` as restriction along the chart followed by the étale stalk at `s`. -/
structure ChartStalkPresentation (x : GeometricPoint B S hS F) where
  /-- The étale chart of `F` through which the stalk is computed. -/
  chart : SmallEtale B S hS F
  /-- The identification of the small étale site of `F` over the chart with the small étale site
  of the object representing it, Stacks 04M0. -/
  chartEquivalence : SmallEtale B S hS (yoneda.obj chart.obj.left) ≌ Over chart
  /-- The identification is compatible with the two inclusions into the big site. -/
  chartEquivalence_comp :
    chartEquivalence.functor ⋙ Over.post (SmallEtale.toOver B S hS F ⋙ yoneda) =
      SmallEtale.inclusion B S hS (yoneda.obj chart.obj.left) ⋙
        CostructuredArrow.toOver yoneda (yoneda.obj chart.obj.left)
  /-- The geometric point of the scheme underlying the chart at which the stalk is taken. -/
  point : _root_.AlgebraicGeometry.GeometricPoint
    ((BigFppfOver.toScheme B S hS).obj chart.obj.left)
  /-- The geometric stalk functor at `x` is restriction along the chart followed by the étale
  stalk at `point`, as an isomorphism of functors. -/
  stalkFunctorIso :
    sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙ stalkSetFunctor x ≅
      sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((representedSmallEtaleEquivalence B S hS chart.obj.left).inverse ⋙
          chartEquivalence.functor ⋙ Over.forget chart).op ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (Functor.Elements.π (geometricPointFiber (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj chart.obj.left)
          chart.obj.left.left.property point)).op ⋙ colim

/-- A chart presentation of the geometric stalk at `x` exists. -/
theorem nonempty_chartStalkPresentation (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    Nonempty (ChartStalkPresentation B S hS F x) :=
  let ⟨X, e, he, s, ⟨hs⟩⟩ := exists_chart_stalkSetFunctor_iso_schemeStalk B S hS F hF x
  ⟨⟨X, e, he, s, hs⟩⟩

/-- The chosen chart presentation of the geometric stalk at `x`.  Its fields are the chart, the
chart identification, the geometric point of the underlying scheme and the natural isomorphism
identifying the geometric stalk functor with the scheme-theoretic étale stalk of the restriction.
-/
def chartStalkPresentation (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    ChartStalkPresentation B S hS F x :=
  Classical.choice (nonempty_chartStalkPresentation B S hS F hF x)

/-- **The geometric stalk of an algebraic space at a geometric point is an étale stalk of a
scheme**, as a named isomorphism natural in the sheaf: the set-valued geometric stalk functor at
`x` is restriction to the chosen chart followed by the étale stalk of Stacks 040R at the chosen
geometric point of the scheme underlying that chart. -/
def chartStalkFunctorIso (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙ stalkSetFunctor x ≅
      sheafToPresheaf (SmallEtale.topology B S hS F) (Type (u + 1)) ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((representedSmallEtaleEquivalence B S hS
            (chartStalkPresentation B S hS F hF x).chart.obj.left).inverse ⋙
          (chartStalkPresentation B S hS F hF x).chartEquivalence.functor ⋙
            Over.forget (chartStalkPresentation B S hS F hF x).chart).op ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (Functor.Elements.π (geometricPointFiber (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj
            (chartStalkPresentation B S hS F hF x).chart.obj.left)
          (chartStalkPresentation B S hS F hF x).chart.obj.left.left.property
          (chartStalkPresentation B S hS F hF x).point)).op ⋙ colim :=
  (chartStalkPresentation B S hS F hF x).stalkFunctorIso

/-- **The geometric stalk of an algebraic space at a geometric point is an étale stalk of a
scheme**, objectwise and as a named isomorphism: for a sheaf of sets `G` on `F_étale` the stalk
`AlgebraicGeometry.Space.stalkSet x G` is `AlgebraicGeometry.etaleStalk` of Stacks 040R, at the
chosen geometric point of the scheme underlying the chosen chart, of the restriction of `G` to the
small étale site of that scheme. -/
def chartEtaleStalkIso (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    (G : Sheaf (SmallEtale.topology B S hS F) (Type (u + 1))) :
    stalkSet x G.obj ≅
      _root_.AlgebraicGeometry.etaleStalk (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj
          (chartStalkPresentation B S hS F hF x).chart.obj.left)
        (chartStalkPresentation B S hS F hF x).chart.obj.left.left.property
        (chartStalkPresentation B S hS F hF x).point
        (((representedSmallEtaleEquivalence B S hS
            (chartStalkPresentation B S hS F hF x).chart.obj.left).inverse ⋙
          (chartStalkPresentation B S hS F hF x).chartEquivalence.functor ⋙
            Over.forget (chartStalkPresentation B S hS F hF x).chart).op ⋙ G.obj) :=
  (chartStalkFunctorIso B S hS F hF x).app G

end AlgebraicGeometry.Space

end
