module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFMapCompChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer

/-!
# The chart component of a composite direct image

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`.  The chart component
`AlgebraicGeometry.Space.modulePushforwardCounitApp` of the direct image along `f ≫ g`, at a
chart diagram which is the composite of a chart diagram over `f` and one over `g`, is **the
chart component along `g` followed by the chart component along `f`**, after the comparison of
the two readings of the composite direct image.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardCounit_eq_compOfIso`: the counit of the chartwise
  universal property along `f ≫ g` is the composite, in the sense of
  `AlgebraicGeometry.Space.ModuleFMap.compOfIso`, of the counit along `g` read through the
  comparison of Stacks 03LU and the counit along `f`.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_chartDiagram_comp`: **the chart formula**
  that follows, at a composite chart diagram.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_comp`: **the same formula with both of its
  factors written as chart components**, which is the form a consumer reads it in: the chart
  component along `g` at the lower diagram followed by the chart component along `f` at the
  upper one, with the comparison of Stacks 03LU evaluated on the section.
* `AlgebraicGeometry.Space.modulePushforwardCounit_app_eq`,
  `AlgebraicGeometry.Space.modulePushforwardHomFMap_app` and
  `AlgebraicGeometry.Space.modulePushforwardHomFMap_app_mk`: the components of the counit and of
  the linear map of sections of a morphism into a direct image, as equations at the type of a
  single section.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_map_mk`: naturality of the chart component
  in the module, with the chart diagram given unbundled.
* `AlgebraicGeometry.Space.modulePushforwardCounitApp_congr_hom` and
  `AlgebraicGeometry.Space.modulePushforwardCounitApp_congr`: the chart component is carried
  along an equality of the morphism, and along an equality of the vertical morphism of the
  diagram, by the transport `eqToHom` of the direct images.  This is what lets the chart formula
  be applied to the two ways around a commutative square, whose composites are equal but not
  identical.

## Implementation notes

The identification of the counit with the composite is proved through the module chart
correspondence of Stacks 03G4 and nothing else: both sides have the same morphism of modules —
the identity — because the morphism of modules of a composite is
`AlgebraicGeometry.Space.moduleFMapCompHom`, which here is the inverse of the comparison
followed by its own inverse's partner, and `AlgebraicGeometry.Space.moduleFMapHom_injective`
turns that into equality of the linear maps of sections.  No property of the comparison is used
in that step, so it holds for the comparison of Stacks 03LU as for any other; the chart formula
below, on the other hand, consumes the geometric compatibility
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`, which is what
makes the composite of the two chart components the chart component of the composite.

Two measurements shape the statements.  First,
`AlgebraicGeometry.Space.modulePushforwardCounitApp_chartDiagram_comp` keeps the components
`AlgebraicGeometry.Space.ModuleFMap.compOfIso_app` produces — the component of
`AlgebraicGeometry.Space.modulePushforwardCounit` and the component of
`AlgebraicGeometry.Space.modulePushforwardHomFMap` — rather than the chart components they are
by definition, and `AlgebraicGeometry.Space.modulePushforwardCounitApp_comp` converts both.
Converting the inner one needs the equation at a chart diagram given **unbundled**, by its two
charts and its vertical morphism, and not as a variable of
`AlgebraicGeometry.Space.ChartDiagram`: that is
`AlgebraicGeometry.Space.modulePushforwardHomFMap_app_mk`, which is a `rfl` because the morphism
into the direct image is a variable there, so the identification of the two spellings of the
middle chart — the diagram's `V` field against the chart it is built from — is decided by
congruence under a rigid head.  Instantiating the bundled
`AlgebraicGeometry.Space.modulePushforwardHomFMap_app` at a chart diagram written out and then
restating its right-hand side at the chart itself is what exceeds the budget instead: there the
morphism is the comparison of Stacks 03LU, whose sheaf of modules the unifier unfolds.

Second, the transport lemmas are stated between two chart diagrams with equal charts and
vertical morphisms rather than by transporting one, so that `Eq.subst` and proof irrelevance
discharge them after the equality of morphisms has been substituted; the morphism of the target
is a variable, which is what makes that substitution legal.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- **The counit of the chartwise universal property along a composite is the composite of the
two counits.**  Along `f ≫ g`, the canonical linear map of sections of
`AlgebraicGeometry.Space.modulePushforwardCounit` is
`AlgebraicGeometry.Space.ModuleFMap.compOfIso` of the counit along `f` and of the counit along
`g` read through the inverse of the comparison of Stacks 03LU.

Both sides have the identity as their morphism of modules, and a linear map of sections is
determined by its morphism of modules. -/
theorem modulePushforwardCounit_eq_compOfIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    modulePushforwardCounit B S hS (f ≫ g) F =
      ModuleFMap.compOfIso B S hS f g F ((modulePushforward B S hS f).obj F)
        ((modulePushforward B S hS (f ≫ g)).obj F)
        (modulePushforwardHomFMap B S hS g ((modulePushforward B S hS f).obj F)
          ((modulePushforward B S hS (f ≫ g)).obj F)
          ((modulePushforwardCompIso B S hS f g).inv.app F))
        (modulePushforwardCounit B S hS f F) (modulePushforwardCompIso B S hS f g) := by
  refine (modulePushforwardHomEquiv B S hS (f ≫ g) F
    ((modulePushforward B S hS (f ≫ g)).obj F)).symm.injective ?_
  refine Eq.trans (moduleFMapHom_modulePushforwardCounit B S hS (f ≫ g) F) ?_
  refine Eq.symm (Eq.trans (moduleFMapHom_modulePushforwardHomFMap B S hS (f ≫ g) F
    ((modulePushforward B S hS (f ≫ g)).obj F) _) ?_)
  rw [moduleFMapCompHom_eq, moduleFMapHom_modulePushforwardHomFMap,
    moduleFMapHom_modulePushforwardCounit, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app]

/-- The component of the counit of the chartwise universal property, as the chart component of
the direct image.  This is the definition of
`AlgebraicGeometry.Space.modulePushforwardCounit`, stated so that it can be used as an equation
at the type of a single section rather than unfolded by unification. -/
theorem modulePushforwardCounit_app_eq (k : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 k.hom)
    (s : ((modulePushforward B S hS k).obj F).val.obj (op d.V)) :
    (modulePushforwardCounit B S hS k F).app d s =
      modulePushforwardCounitApp B S hS k F d s := rfl

/-- `AlgebraicGeometry.Space.modulePushforwardHomFMap_app` with the chart diagram given
unbundled, by its two charts and its vertical morphism of schemes.

This is the form the chart formula below consumes, and the only form in which it can be: the
right-hand side names the lower chart, and writing it as the `V` field of a chart diagram built
from that chart is what makes the two spellings of that chart appear in one term.  Here the
morphism `a` into the direct image is a variable, so the comparison of the two spellings is
settled by congruence under a rigid head. -/
theorem modulePushforwardHomFMap_app_mk (k : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (a : G ⟶ (modulePushforward B S hS k).obj F)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    (c : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hc : U.1.hom ≫ k.hom = yoneda.map c ≫ V.1.hom) (s : G.val.obj (op V)) :
    (modulePushforwardHomFMap B S hS k F G a).app ⟨U, V, c, hc⟩ s =
      modulePushforwardCounitApp B S hS k F ⟨U, V, c, hc⟩ (a.val.app (op V) s) := rfl

section Factor

variable (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- **The chart formula for the chart component of a composite direct image.**  At the chart
diagram over `f ≫ g` obtained by composing a chart diagram over `f` and one over `g`, the chart
component of the direct image along `f ≫ g` is the component at the upper diagram of the linear
map of sections which the inverse of the comparison of Stacks 03LU makes up, followed by the
chart component along `f` at the lower diagram.

The right-hand side is written with the components of the two linear maps of sections, in the
shape `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app` produces, and not with the chart
components those components are; see the implementation notes. -/
theorem modulePushforwardCounitApp_chartDiagram_comp (F : Modules.{u, u} B S hS X.1 X.2)
    (s : ((modulePushforward B S hS (f ≫ g)).obj F).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) F
        (ChartDiagram.comp B S hS f g a b ha hb) s =
      (modulePushforwardCounit B S hS f F).app ⟨U, V, a, ha⟩
        ((modulePushforwardHomFMap B S hS g ((modulePushforward B S hS f).obj F)
            ((modulePushforward B S hS (f ≫ g)).obj F)
            ((modulePushforwardCompIso B S hS f g).inv.app F)).app ⟨V, W, b, hb⟩ s) :=
  have h0 := (modulePushforwardCounit_app_eq B S hS (f ≫ g) F
    (ChartDiagram.comp B S hS f g a b ha hb) s).symm
  have h1 := congrArg
    (fun ξ : ModuleFMap B S hS (f ≫ g) F ((modulePushforward B S hS (f ≫ g)).obj F) ↦
      ξ.app (ChartDiagram.comp B S hS f g a b ha hb) s)
    (modulePushforwardCounit_eq_compOfIso B S hS f g F)
  have h2 := ModuleFMap.compOfIso_app B S hS f g a b ha hb F
    ((modulePushforward B S hS f).obj F) ((modulePushforward B S hS (f ≫ g)).obj F)
    (modulePushforwardHomFMap B S hS g ((modulePushforward B S hS f).obj F)
      ((modulePushforward B S hS (f ≫ g)).obj F)
      ((modulePushforwardCompIso B S hS f g).inv.app F))
    (modulePushforwardCounit B S hS f F) (modulePushforwardCompIso B S hS f g)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g F) s
  h0.trans (h1.trans h2)

/-- **The chart formula for the chart component of a composite direct image, with both factors
written as chart components.**  At the chart diagram over `f ≫ g` obtained by composing a chart
diagram over `f` and one over `g`, the chart component of the direct image along `f ≫ g` is the
inverse of the comparison of Stacks 03LU on the sections over the lowest chart, followed by the
chart component along `g` at the lower diagram, followed by the chart component along `f` at the
upper diagram.

This is `AlgebraicGeometry.Space.modulePushforwardCounitApp_chartDiagram_comp` with its two
factors converted, the outer one by
`AlgebraicGeometry.Space.modulePushforwardCounit_app_eq` and the inner one by
`AlgebraicGeometry.Space.modulePushforwardHomFMap_app_mk`. -/
theorem modulePushforwardCounitApp_comp (F : Modules.{u, u} B S hS X.1 X.2)
    (s : ((modulePushforward B S hS (f ≫ g)).obj F).val.obj (op W)) :
    modulePushforwardCounitApp B S hS (f ≫ g) F
        (ChartDiagram.comp B S hS f g a b ha hb) s =
      modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f).obj F)
            ⟨V, W, b, hb⟩
          (((modulePushforwardCompIso B S hS f g).inv.app F).val.app (op W) s)) :=
  (modulePushforwardCounitApp_chartDiagram_comp B S hS f g a b ha hb F s).trans
    ((modulePushforwardCounit_app_eq B S hS f F ⟨U, V, a, ha⟩ _).trans
      (congrArg (modulePushforwardCounitApp B S hS f F ⟨U, V, a, ha⟩)
        (modulePushforwardHomFMap_app_mk B S hS g ((modulePushforward B S hS f).obj F)
          ((modulePushforward B S hS (f ≫ g)).obj F)
          ((modulePushforwardCompIso B S hS f g).inv.app F) b hb s)))

end Factor

/-- Naturality of the chart component of a direct image in the module, with the chart diagram
given unbundled, by its two charts and its vertical morphism of schemes.  This is the form a
consumer with a concrete diagram needs: both the section it is applied to and the section it
produces are then written at a chart and not at a field of a diagram built from one. -/
theorem modulePushforwardCounitApp_map_mk (k : X ⟶ Z) {F F' : Modules.{u, u} B S hS X.1 X.2}
    (a : F ⟶ F') {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Z.1}
    (c : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hc : U.1.hom ≫ k.hom = yoneda.map c ≫ V.1.hom)
    (x : ((modulePushforward B S hS k).obj F).val.obj (op V)) :
    modulePushforwardCounitApp B S hS k F' ⟨U, V, c, hc⟩
        (((modulePushforward B S hS k).map a).val.app (op V) x) =
      a.val.app (op U) (modulePushforwardCounitApp B S hS k F ⟨U, V, c, hc⟩ x) :=
  modulePushforwardCounitApp_map B S hS k a ⟨U, V, c, hc⟩ x

/-- **The chart component of a direct image is carried along an equality of the morphism.**  If
two morphisms `k, k' : X ⟶ Z` are equal and two chart diagrams, one over each, have the same
charts and the same vertical morphism of schemes, then the chart component along `k'`, applied
after the transport of the direct images, is the chart component along `k`.

This is what lets `AlgebraicGeometry.Space.modulePushforwardCounitApp_chartDiagram_comp` be read
at the two composites around a commutative square: the two composites are equal, and the two
composite chart diagrams agree whenever the chart square commutes. -/
theorem modulePushforwardCounitApp_congr_hom {k k' : X ⟶ Z} (h : k = k')
    (F : Modules.{u, u} B S hS X.1 X.2)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Z.1}
    (c : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hc : U.1.hom ≫ k.hom = yoneda.map c ≫ V.1.hom)
    (hc' : U.1.hom ≫ k'.hom = yoneda.map c ≫ V.1.hom)
    (s : ((modulePushforward B S hS k).obj F).val.obj (op V)) :
    modulePushforwardCounitApp B S hS k' F ⟨U, V, c, hc'⟩
        ((eqToHom (congrArg (fun m : X ⟶ Z ↦ (modulePushforward B S hS m).obj F) h)).val.app
          (op V) s) =
      modulePushforwardCounitApp B S hS k F ⟨U, V, c, hc⟩ s := by
  subst h
  rfl

/-- **The chart component of a direct image is carried along an equality of the morphism and an
equality of the vertical morphism of the diagram at once**, with the transport taken at the
level of the direct-image *functors* rather than of their values.

That is the shape the comparison
`AlgebraicGeometry.Space.modulePushforwardSquareComparison` of the two composite direct images
around a commutative square contains, so this is the lemma that reads the chart formula
`AlgebraicGeometry.Space.modulePushforwardCounitApp_comp` at the two ways around such a square:
the two composites are equal, and the two composite chart diagrams have the same charts and
equal vertical morphisms whenever the chart square commutes. -/
theorem modulePushforwardCounitApp_congr {k k' : X ⟶ Z} (h : k = k')
    (F : Modules.{u, u} B S hS X.1 X.2)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Z.1}
    {c c' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Z.1).obj V}
    (hcc : c = c') (hc : U.1.hom ≫ k.hom = yoneda.map c ≫ V.1.hom)
    (hc' : U.1.hom ≫ k'.hom = yoneda.map c' ≫ V.1.hom)
    (s : ((modulePushforward B S hS k).obj F).val.obj (op V)) :
    modulePushforwardCounitApp B S hS k' F ⟨U, V, c', hc'⟩
        (((eqToHom (congrArg (fun m : X ⟶ Z ↦ modulePushforward B S hS m) h)).app F).val.app
          (op V) s) =
      modulePushforwardCounitApp B S hS k F ⟨U, V, c, hc⟩ s := by
  subst h
  subst hcc
  rfl

end AlgebraicGeometry.Space

end
