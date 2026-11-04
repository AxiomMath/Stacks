module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPresentationComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer

/-!
# The chart sections of an inverse image of modules along a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site `B`, and let `M` be an `𝒪_Z`-module on the small étale site.  Over a commutative diagram
`d` of étale scheme charts over a morphism `h`, a section `s` of `M` over the lower chart has a
canonical image `AlgebraicGeometry.Space.modulePullbackChartFMap` in `h^*M` over the upper
chart: the chart component of the unit of `h^* ⊣ h_*`.

This file proves that these chart sections are compatible with the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso : g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU.  For a
chart diagram `(U, V, a)` over `f` and a chart diagram `(V, W, b)` over `g`, with composite
`(U, W, a ≫ b)` over `f ≫ g`, taking the chart section along `g` and then along `f`, and
applying the comparison, gives the chart section along `f ≫ g`.

## Main results

* `AlgebraicGeometry.Space.moduleFMapHom_modulePullbackChartFMap`: the morphism of modules into
  the direct image attached to the chart sections is the unit of the adjunction.
* `AlgebraicGeometry.Space.moduleFMapCompHom_modulePullbackChartFMap_comp`: the composite
  morphism attached to the two chart sections, followed by the direct image of the
  comparison, is the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*`.
* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_app_modulePullbackChartFMap`: **the
  chart formula** described above.

## Implementation notes

The chart section along `f` of the chart section along `g` is the composite
`AlgebraicGeometry.Space.ModuleFMap.compOfIso` of the two linear maps of sections, by the chart
formula `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app` taken with the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of direct images, whose geometric property
is `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`.  The
morphism of modules of that composite is the composite of the two units and of the comparison
of direct images, and `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_app` says that
it becomes the unit along `f ≫ g` after the comparison of inverse images.  The comparison is
moved inside the chart component of the direct image by its naturality,
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`.

Each step is a named statement and the chain is assembled in term mode with `Eq.trans`, so that
no step has to re-elaborate the comparison isomorphisms.  The two moves that only shuffle
morphisms, `AlgebraicGeometry.Space.val_app_val_app_of_comp_eq` and
`AlgebraicGeometry.Space.val_app_modulePushforwardCounitApp_of_comp_eq`, are stated over
arbitrary morphisms of modules and instantiated once.  The second takes its chart diagram in
constructor form `⟨U', W', e, he⟩` rather than as a variable: instantiated at a variable diagram
and then at `AlgebraicGeometry.Space.ChartDiagram.comp`, the elaborator compares the sections
over `op d.U` with those over `op U` by unfolding the inverse image of modules instead of the
projection, and does not terminate within the default budget; in constructor form the
projections are syntactically the charts.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- **The morphism of modules of the chart sections is the unit.**  The morphism
`M ⟶ f_*f^*M` which the chart correspondence of Stacks 03G4 attaches to the chart sections
`AlgebraicGeometry.Space.modulePullbackChartFMap` is the unit of `f^* ⊣ f_*` at `M`. -/
theorem moduleFMapHom_modulePullbackChartFMap (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    moduleFMapHom B S hS f ((modulePullback B S hS f).obj M) M
        (modulePullbackChartFMap B S hS f M) =
      (modulePullbackAdjunction B S hS f).unit.app M :=
  ((modulePushforwardHomEquiv B S hS f ((modulePullback B S hS f).obj M) M).symm_apply_apply
      ((modulePullbackAdjunction B S hS f).homEquiv M ((modulePullback B S hS f).obj M)
        (𝟙 _))).trans
    ((modulePullbackAdjunction B S hS f).homEquiv_id M)

/-- Two morphisms of modules whose composite is a third act on sections as the third does.
Stated for arbitrary morphisms so that the composite is never unfolded. -/
theorem val_app_val_app_of_comp_eq {M₁ M₂ M₃ : Modules.{u, u} B S hS Z.1 Z.2} (φ₁ : M₁ ⟶ M₂)
    (φ₂ : M₂ ⟶ M₃) (ψ : M₁ ⟶ M₃) (h : φ₁ ≫ φ₂ = ψ) (T : (SmallEtale B S hS Z.1)ᵒᵖ)
    (s : M₁.val.obj T) : φ₂.val.app T (φ₁.val.app T s) = ψ.val.app T s :=
  (comp_val_app_apply B S hS φ₁ φ₂ T s).symm.trans
    (congrArg (fun φ : M₁ ⟶ M₃ ↦ φ.val.app T s) h)

/-- A morphism of modules `φ : P ⟶ Q` moves inside the chart component of the direct image:
if `C : N ⟶ h_*P` followed by `h_*φ` is `D : N ⟶ h_*Q`, then `φ` applied to the chart component
of a value of `C` is the chart component of the corresponding value of `D`.  Stated for
arbitrary morphisms so that nothing is unfolded. -/
theorem val_app_modulePushforwardCounitApp_of_comp_eq {X' : AlgebraicSpaces B S hS} (h : X' ⟶ Z)
    {N : Modules.{u, u} B S hS Z.1 Z.2} {P Q : Modules.{u, u} B S hS X'.1 X'.2} (φ : P ⟶ Q)
    (C : N ⟶ (modulePushforward B S hS h).obj P) (D : N ⟶ (modulePushforward B S hS h).obj Q)
    (hCD : C ≫ (modulePushforward B S hS h).map φ = D) {U' : SmallEtale B S hS X'.1}
    {W' : SmallEtale B S hS Z.1}
    (e : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS Z.1).obj W')
    (he : U'.1.hom ≫ h.hom = yoneda.map e ≫ W'.1.hom) (s : N.val.obj (op W')) :
    φ.val.app (op U') (modulePushforwardCounitApp B S hS h P ⟨U', W', e, he⟩
        (C.val.app (op W') s)) =
      modulePushforwardCounitApp B S hS h Q ⟨U', W', e, he⟩ (D.val.app (op W') s) :=
  (modulePushforwardCounitApp_map B S hS h φ ⟨U', W', e, he⟩ (C.val.app (op W') s)).symm.trans
    (congrArg (modulePushforwardCounitApp B S hS h Q ⟨U', W', e, he⟩)
      (val_app_val_app_of_comp_eq B S hS C ((modulePushforward B S hS h).map φ) D hCD
        (op W') s))

section Comp

variable (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)

/-- The composite morphism of modules attached to the chart sections along `g` and the chart
sections along `f` is the composite of the two units and the comparison of direct images. -/
theorem moduleFMapCompHom_modulePullbackChartFMap :
    moduleFMapCompHom B S hS f g
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
        (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
        (modulePushforwardCompIso B S hS f g) =
      (modulePullbackAdjunction B S hS g).unit.app M ≫
        (modulePushforward B S hS g).map
          ((modulePullbackAdjunction B S hS f).unit.app ((modulePullback B S hS g).obj M)) ≫
        (modulePushforwardCompIso B S hS f g).hom.app
          ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M)) :=
  (moduleFMapCompHom_eq B S hS f g
      ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
      ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
      (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
      (modulePushforwardCompIso B S hS f g)).trans
    (congrArg₂
      (fun (a : M ⟶ (modulePushforward B S hS g).obj ((modulePullback B S hS g).obj M))
          (b : (modulePullback B S hS g).obj M ⟶
            (modulePushforward B S hS f).obj
              ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))) ↦
        a ≫ (modulePushforward B S hS g).map b ≫
          (modulePushforwardCompIso B S hS f g).hom.app
            ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M)))
      (moduleFMapHom_modulePullbackChartFMap B S hS g M)
      (moduleFMapHom_modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M)))

/-- **The composite of the chart sections becomes the unit along the composite.**  The
composite morphism of modules attached to the chart sections along `g` and along `f`, followed
by the direct image along `f ≫ g` of the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU, is
the unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` at `M`. -/
theorem moduleFMapCompHom_modulePullbackChartFMap_comp :
    moduleFMapCompHom B S hS f g
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
        (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
        (modulePushforwardCompIso B S hS f g) ≫
      (modulePushforward B S hS (f ≫ g)).map ((modulePullbackCompIso B S hS f g).hom.app M) =
      (modulePullbackAdjunction B S hS (f ≫ g)).unit.app M :=
  (congrArg (fun a ↦ a ≫ (modulePushforward B S hS (f ≫ g)).map
      ((modulePullbackCompIso B S hS f g).hom.app M))
    (moduleFMapCompHom_modulePullbackChartFMap B S hS f g M)).trans
    (((Category.assoc _ _ _).trans
      (congrArg (fun a ↦ (modulePullbackAdjunction B S hS g).unit.app M ≫ a)
        (Category.assoc _ _ _))).trans
      (modulePullbackAdjunction_unit_comp_app B S hS f g M))

end Comp

section Chart

variable (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- The chart section along `f` of the chart section along `g` is the value of the composite
linear map of sections at the composed chart diagram. -/
theorem modulePullbackChartFMap_app_app_eq_compOfIso (s : M.val.obj (op W)) :
    (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M)).app ⟨U, V, a, ha⟩
        ((modulePullbackChartFMap B S hS g M).app ⟨V, W, b, hb⟩ s) =
      (ModuleFMap.compOfIso B S hS f g
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
        (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
        (modulePushforwardCompIso B S hS f g)).app
        (ChartDiagram.comp B S hS f g a b ha hb) s :=
  (ModuleFMap.compOfIso_app B S hS f g a b ha hb
    ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
    ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
    (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
    (modulePushforwardCompIso B S hS f g)
    (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g
      ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))) s).symm

/-- The value of the composite linear map of sections at the composed chart diagram is the chart
component of the direct image along `f ≫ g` applied to the composite morphism of modules. -/
theorem compOfIso_modulePullbackChartFMap_app (s : M.val.obj (op W)) :
    (ModuleFMap.compOfIso B S hS f g
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
        (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
        (modulePushforwardCompIso B S hS f g)).app
        (ChartDiagram.comp B S hS f g a b ha hb) s =
      modulePushforwardCounitApp B S hS (f ≫ g)
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        (ChartDiagram.comp B S hS f g a b ha hb)
        ((moduleFMapCompHom B S hS f g
            ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
            ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
            (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
            (modulePushforwardCompIso B S hS f g)).val.app (op W) s) :=
  ModuleFMap.compOfIso_app_comp f g a b ha hb _ _ _ _ _ _ s

/-- The chart section along `f ≫ g`, as the chart component of the direct image applied to the
unit. -/
theorem modulePullbackChartFMap_comp_app_eq (s : M.val.obj (op W)) :
    (modulePullbackChartFMap B S hS (f ≫ g) M).app (ChartDiagram.comp B S hS f g a b ha hb) s =
      modulePushforwardCounitApp B S hS (f ≫ g) ((modulePullback B S hS (f ≫ g)).obj M)
        (ChartDiagram.comp B S hS f g a b ha hb)
        (((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M).val.app (op W) s) :=
  modulePullbackHomFMap_app B S hS (f ≫ g) M ((modulePullback B S hS (f ≫ g)).obj M) (𝟙 _)
    (ChartDiagram.comp B S hS f g a b ha hb) s

/-- The comparison of inverse images, applied to the value of the composite linear map of sections
at the composed chart diagram, is the chart component of the unit along `f ≫ g`. -/
theorem modulePullbackCompIso_hom_app_modulePushforwardCounitApp_moduleFMapCompHom
    (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
        (modulePushforwardCounitApp B S hS (f ≫ g)
          ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
          (ChartDiagram.comp B S hS f g a b ha hb) ((moduleFMapCompHom B S hS f g
            ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
            ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
            (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
            (modulePushforwardCompIso B S hS f g)).val.app (op W) s)) =
      modulePushforwardCounitApp B S hS (f ≫ g) ((modulePullback B S hS (f ≫ g)).obj M)
        (ChartDiagram.comp B S hS f g a b ha hb)
        (((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M).val.app (op W) s) :=
  val_app_modulePushforwardCounitApp_of_comp_eq B S hS (f ≫ g)
    ((modulePullbackCompIso B S hS f g).hom.app M) (moduleFMapCompHom B S hS f g
            ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
            ((modulePullback B S hS g).obj M) M (modulePullbackChartFMap B S hS g M)
            (modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M))
            (modulePushforwardCompIso B S hS f g))
    ((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M)
    (moduleFMapCompHom_modulePullbackChartFMap_comp B S hS f g M)
    (a ≫ b) (ChartDiagram.comp B S hS f g a b ha hb).comm s

/-- **The chart formula for the inverse image of modules along a composite.**  For a chart
diagram `(U, V, a)` over `f`, a chart diagram `(V, W, b)` over `g` and a section `s` of `M` over
`W`, the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of Stacks 03LU carries the chart section along `f`
of the chart section along `g` of `s` to the chart section of `s` along `f ≫ g` at the composed
chart diagram `(U, W, a ≫ b)`. -/
theorem modulePullbackCompIso_hom_app_modulePullbackChartFMap (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
        ((modulePullbackChartFMap B S hS f ((modulePullback B S hS g).obj M)).app
          ⟨U, V, a, ha⟩ ((modulePullbackChartFMap B S hS g M).app ⟨V, W, b, hb⟩ s)) =
      (modulePullbackChartFMap B S hS (f ≫ g) M).app
        (ChartDiagram.comp B S hS f g a b ha hb) s :=
  (congrArg (((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U))
      ((modulePullbackChartFMap_app_app_eq_compOfIso B S hS f g M a b ha hb s).trans
        (compOfIso_modulePullbackChartFMap_app B S hS f g M a b ha hb s))).trans
    ((modulePullbackCompIso_hom_app_modulePushforwardCounitApp_moduleFMapCompHom B S hS f g M
        a b ha hb s).trans
      (modulePullbackChartFMap_comp_app_eq B S hS f g M a b ha hb s).symm)

end Chart

end AlgebraicGeometry.Space

end
