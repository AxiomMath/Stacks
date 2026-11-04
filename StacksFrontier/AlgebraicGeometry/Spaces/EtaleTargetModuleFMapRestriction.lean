module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeEtaleSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.PairChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompCoherence

/-!
# Linear maps of sections along a composite with an étale second factor

Let `a : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` and
let `p : Y ⟶ Z` be an **étale** morphism which is relatively representable.  A linear map of
sections `AlgebraicGeometry.Space.ModuleFMap` along `a ≫ p` from an `𝒪_X`-module `N` to an
`𝒪_Z`-module `M` restricts to one along `a` from `N` to the étale restriction `M|_Y`: a diagram
of étale scheme charts over `a` becomes one over `a ≫ p` by postcomposing its chart of `Y` with
`p`, and the sections of `M|_Y` over a chart of `Y` are the sections of `M` over that composite
chart.

This file shows that restriction is a **bijection**.  The content is cofinality of the chart
diagrams over `a ≫ p` whose chart of `Z` comes from a chart of `Y`: a diagram over `a ≫ p` with
chart `W` of `Z` is dominated by the diagram with chart `W ×_Z Y`, which is a chart of `Y`, since
the vertical morphism of the diagram and the structure morphism of its chart of `X` composed with
`a` factor through that fibre product.

For `a` the identity the statement is the hom-set bijection of the adjunction between étale
restriction of modules and the direct image, in the chartwise form of Stacks 03G4.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.postcompTarget`: a diagram of charts over `a`, with its
  chart of `Y` postcomposed with `p`, is a diagram over `a ≫ p`.
* `AlgebraicGeometry.Space.etaleBaseChangeChart` and
  `AlgebraicGeometry.Space.etaleBaseChangeChartMap`: the base change along `p` of a chart of `Z`
  and of a morphism of charts of `Z`, which are `AlgebraicGeometry.Space.smallBaseChange` on
  objects and on morphisms (`AlgebraicGeometry.Space.etaleBaseChangeChart_eq` and
  `AlgebraicGeometry.Space.etaleBaseChangeChartMap_eq` are `rfl`), written reducibly.
* `AlgebraicGeometry.Space.etaleChartProjection`: the cartesian projection of that base change
  to the original chart, read as a morphism of charts of `Z`.
* `AlgebraicGeometry.Space.ChartDiagram.baseChangeTarget`: a diagram of charts over `a ≫ p`,
  with its chart of `Z` replaced by the base change along `p`, is a diagram over `a`.
* `AlgebraicGeometry.Space.etaleChartGraph`: the graph section of a chart of `Y` into the base
  change along `p` of its postcomposition; it splits the projection.
* `AlgebraicGeometry.Space.moduleFMapEtaleRestrict` and
  `AlgebraicGeometry.Space.moduleFMapEtaleExtend`: the restriction of linear maps of sections
  and its inverse.

## Main results

* `AlgebraicGeometry.Space.moduleFMapEtaleRestrict_app_baseChangeTarget`: **the values of a
  linear map of sections along `a ≫ p` are determined by its restriction** — its value at a
  diagram is the value of the restriction at the base-changed diagram, applied to the
  restriction of the section along the projection.
* `AlgebraicGeometry.Space.moduleFMapEtaleRestrictEquiv`: **the restriction is a bijection**
  `ModuleFMap (a ≫ p) N M ≃ ModuleFMap a N (M|_Y)`.

## Implementation notes

The scalars need no transport.  Postcomposition of charts leaves the underlying object of the big
fppf site unchanged, so the ring of regular functions on a chart of `Y` is the ring of regular
functions on its postcomposition, the sections of `M|_Y` over a chart of `Y` *are* the sections
of `M` over its postcomposition, and the two scalar actions agree definitionally.  The pullback
of regular functions along a chart diagram depends only on the vertical morphism of the diagram,
which `AlgebraicGeometry.Space.ChartDiagram.postcompTarget` does not change, so the four fields
of the restriction are the four fields of the given linear map of sections with nothing rewritten.

For the inverse the vertical morphism does change — it becomes the lift to the fibre product —
and the semilinearity field needs the pullback of regular functions along the lift, after the one
along the projection, to be the pullback along the original vertical morphism.  That is
functoriality of global regular functions, isolated as
`AlgebraicGeometry.Space.chartDiagramPullback_comp_apply`.

Three elaboration constraints shape the proofs, none needing a raised limit.

*The base change of charts is taken reducibly.*  `AlgebraicGeometry.Space.smallBaseChange` is a
functor built from the universal property of the fibre product, and at `implicit` transparency
the underlying object of its value is not seen to be that fibre product; a goal about the lift
into it is then not type-correct and `rw` refuses it.  So the base change of a chart and of a
morphism of charts are restated here as reducible definitions, with `rfl` lemmas identifying them
with `AlgebraicGeometry.Space.smallBaseChange`, and every universal-property rewrite is performed
on the lift itself.

*The chart diagrams of the two constructions are reducible*, for the same reason: a statement
mentioning the vertical morphism of a constructed diagram is type-correct only once the chart of
`X` it starts from is seen to be the chart of `X` of the diagram it came from.

*The fields of the inverse are proved in term mode.*  Their statements mention sections of a
module over the chart of a constructed diagram, and the identification of the index category of
the small étale ringed site with the small étale site is again semireducible, so `rw` declines
goals of that shape; `Eq.trans` and `congrArg` do not care.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### Restrictions of sections, on the underlying presheaf -/

/-- Restricting sections along `φ` and then along `ψ` is restricting along `φ ≫ ψ`.  This is
functoriality of the underlying presheaf of abelian groups; the module-level restrictions land in
two different restrictions of scalars, so they are not composed directly. -/
alias val_map_comp_apply := compCoherence_val_map_comp_apply

/-- Restricting sections along the identity does nothing. -/
theorem val_map_id_apply {W : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS W.1 W.2)
    (V : SmallEtale B S hS W.1) (x : M.val.obj (op V)) :
    M.val.map (𝟙 V).op x = x :=
  CategoryTheory.congr_fun (M.val.presheaf.map_id (op V)) x

/-- The morphism of the big fppf site underlying a morphism of étale charts. -/
theorem toOver_map_eq {W : AlgebraicSpaces B S hS} {U V : SmallEtale B S hS W.1} (i : U ⟶ V) :
    (SmallEtale.toOver B S hS W.1).map i = i.hom.left :=
  rfl

/-! ### Pullback of regular functions along a composite of vertical morphisms -/

/-- Pullback of regular functions along a chart diagram depends only on the vertical morphism of
the diagram, and is functorial in it: pulling back along `ψ` and then along `φ` is pulling back
along `φ ≫ ψ`.

Stated on sections, and for two morphisms of the big fppf site alone, so that it applies to any
two chart diagrams whose vertical morphisms compose. -/
theorem chartDiagramPullback_comp_apply {U V W : BigFppfOver B S hS} (φ : U ⟶ V) (ψ : V ⟶ W)
    (r : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj W)))) :
    ((forget₂ CommRingCat.{u} RingCat.{u}).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map φ).op))
        (((forget₂ CommRingCat.{u} RingCat.{u}).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op)) r) =
      ((forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (φ ≫ ψ)).op)) r := by
  rw [CategoryTheory.Functor.map_comp, op_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  rfl

section Restrict

variable (a : X ⟶ Y) (p : Y ⟶ Z) (hp : IsEtale B S hS p.hom)
    (hrep : yoneda.relativelyRepresentable p.hom)

/-! ### Chart diagrams over a composite with an étale second factor -/

/-- **A diagram of étale scheme charts over `a`, with its chart of `Y` postcomposed with the
étale morphism `p`, is a diagram over `a ≫ p`.**  The vertical morphism and the underlying
object of the chart of `Y` are unchanged.

Reducible, so that the vertical morphism of the diagram it produces is seen to start at the
chart of `X` of the given one. -/
abbrev ChartDiagram.postcompTarget (e : ChartDiagram B S hS X.1 Y.1 a.hom) :
    ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom where
  U := e.U
  V := (smallEtalePostcomp B S hS p hp).obj e.V
  g := e.g
  comm := by
    change e.U.1.hom ≫ a.hom ≫ p.hom = yoneda.map e.g ≫ e.V.1.hom ≫ p.hom
    rw [← Category.assoc, e.comm, Category.assoc]

/-! ### The base change of a chart of `Z` along `p`, reducibly -/

/-- The base change along `p` of an étale chart of `Z`: the fibre product of the chart with `Y`
over `Z`, which is an étale chart of `Y`.  This is
`AlgebraicGeometry.Space.smallBaseChange` on objects, written reducibly. -/
noncomputable abbrev etaleBaseChangeChart (W : SmallEtale B S hS Z.1) : SmallEtale B S hS Y.1 :=
  ⟨CostructuredArrow.mk (hrep.fst W.1.hom),
    isEtaleChart_representablePullback B S hS p hrep W⟩

/-- The base change of a chart of `Z` is the one of `AlgebraicGeometry.Space.smallBaseChange`. -/
theorem etaleBaseChangeChart_eq (W : SmallEtale B S hS Z.1) :
    etaleBaseChangeChart B S hS p hrep W = (smallBaseChange B S hS p hrep).obj W :=
  rfl

/-- The base change along `p` of a morphism of étale charts of `Z`: the lift to the fibre
products.  This is `AlgebraicGeometry.Space.smallBaseChange` on morphisms, written reducibly. -/
noncomputable abbrev etaleBaseChangeChartMap {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W) :
    etaleBaseChangeChart B S hS p hrep W' ⟶ etaleBaseChangeChart B S hS p hrep W :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hrep.lift (hrep.fst W'.1.hom) (hrep.snd W'.1.hom ≫ j.hom.left)
      (representablePullback_lift_cond B S hS p hrep j))
    (hrep.lift_fst (hrep.fst W'.1.hom) (hrep.snd W'.1.hom ≫ j.hom.left)
      (representablePullback_lift_cond B S hS p hrep j)))

/-- The base change of a morphism of charts of `Z` is the one of
`AlgebraicGeometry.Space.smallBaseChange`. -/
theorem etaleBaseChangeChartMap_eq {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W) :
    etaleBaseChangeChartMap B S hS p hrep j = (smallBaseChange B S hS p hrep).map j :=
  rfl

/-- The lift underlying the base change of a morphism of charts of `Z`. -/
theorem toOver_map_etaleBaseChangeChartMap {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W) :
    (SmallEtale.toOver B S hS Y.1).map (etaleBaseChangeChartMap B S hS p hrep j) =
      hrep.lift (hrep.fst W'.1.hom) (hrep.snd W'.1.hom ≫ j.hom.left)
        (representablePullback_lift_cond B S hS p hrep j) :=
  rfl

/-- The projection of the base change along `p` of an étale chart of `Z` to that chart, read as
a morphism of charts of `Z` out of the postcomposition of the base change: the cartesian
projection of the fibre product, whose triangle over `Z` is the commutation of the cartesian
square. -/
noncomputable abbrev etaleChartProjection (W : SmallEtale B S hS Z.1) :
    (smallEtalePostcomp B S hS p hp).obj (etaleBaseChangeChart B S hS p hrep W) ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk (hrep.snd W.1.hom) (hrep.w W.1.hom).symm)

/-- The cartesian projection underlying `AlgebraicGeometry.Space.etaleChartProjection`. -/
theorem toOver_map_etaleChartProjection (W : SmallEtale B S hS Z.1) :
    (SmallEtale.toOver B S hS Z.1).map (etaleChartProjection B S hS p hp hrep W) =
      hrep.snd W.1.hom :=
  rfl

/-- **The projections are natural in the chart of `Z`.** -/
theorem etaleChartProjection_naturality {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W) :
    etaleChartProjection B S hS p hp hrep W' ≫ j =
      (smallEtalePostcomp B S hS p hp).map (etaleBaseChangeChartMap B S hS p hrep j) ≫
        etaleChartProjection B S hS p hp hrep W :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (hrep.lift_snd (hrep.fst W'.1.hom) (hrep.snd W'.1.hom ≫ j.hom.left)
      (representablePullback_lift_cond B S hS p hrep j)).symm)

/-! ### The base-changed diagram -/

/-- The compatibility making the vertical morphism of
`AlgebraicGeometry.Space.ChartDiagram.baseChangeTarget` well defined: the structure morphism of
the chart of `X` composed with `a`, and the vertical morphism of the diagram, agree over `Z`. -/
theorem baseChangeTarget_lift_cond (D : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom) :
    (D.U.1.hom ≫ a.hom) ≫ p.hom = yoneda.map D.g ≫ D.V.1.hom := by
  rw [Category.assoc]
  exact D.comm

/-- **A diagram of étale scheme charts over `a ≫ p`, with its chart of `Z` replaced by the base
change along `p`, is a diagram over `a`.**  Its vertical morphism is the lift to the fibre
product of the vertical morphism of the given diagram and of the structure morphism of its chart
of `X` composed with `a`.

Reducible, for the reason recorded at
`AlgebraicGeometry.Space.ChartDiagram.postcompTarget`. -/
noncomputable abbrev ChartDiagram.baseChangeTarget
    (D : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom) :
    ChartDiagram B S hS X.1 Y.1 a.hom where
  U := D.U
  V := etaleBaseChangeChart B S hS p hrep D.V
  g := hrep.lift (D.U.1.hom ≫ a.hom) D.g (baseChangeTarget_lift_cond B S hS a p D)
  comm := (hrep.lift_fst (D.U.1.hom ≫ a.hom) D.g
    (baseChangeTarget_lift_cond B S hS a p D)).symm

/-- The vertical morphism of the base-changed diagram, followed by the projection, is the
vertical morphism of the given diagram. -/
theorem baseChangeTarget_g_comp_projection
    (D : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom) :
    (D.baseChangeTarget B S hS a p hrep).g ≫
        (SmallEtale.toOver B S hS Z.1).map (etaleChartProjection B S hS p hp hrep D.V) =
      D.g :=
  hrep.lift_snd (D.U.1.hom ≫ a.hom) D.g (baseChangeTarget_lift_cond B S hS a p D)

/-- **The morphism of base-changed diagrams attached to a morphism of diagrams over `a ≫ p`.**
Both sides are morphisms into a fibre product, so they agree as soon as their composites with
the two projections do: with the projection to `Y` by the universal property, and with the
projection to the chart of `Z` by the compatibility of the given morphism of diagrams. -/
theorem baseChangeTarget_g_naturality (D D' : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom)
    (i : D'.U ⟶ D.U) (j : D'.V ⟶ D.V)
    (hcond : (SmallEtale.toOver B S hS X.1).map i ≫ D.g =
      D'.g ≫ (SmallEtale.toOver B S hS Z.1).map j) :
    (SmallEtale.toOver B S hS X.1).map i ≫ (D.baseChangeTarget B S hS a p hrep).g =
      (D'.baseChangeTarget B S hS a p hrep).g ≫
        (SmallEtale.toOver B S hS Y.1).map (etaleBaseChangeChartMap B S hS p hrep j) := by
  rw [toOver_map_etaleBaseChangeChartMap B S hS p hrep j]
  refine hrep.hom_ext ?_ ?_
  · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      Category.assoc,
      hrep.lift_fst (hrep.fst D'.V.1.hom) (hrep.snd D'.V.1.hom ≫ j.hom.left)
        (representablePullback_lift_cond B S hS p hrep j),
      hrep.lift_fst (D.U.1.hom ≫ a.hom) D.g (baseChangeTarget_lift_cond B S hS a p D),
      hrep.lift_fst (D'.U.1.hom ≫ a.hom) D'.g (baseChangeTarget_lift_cond B S hS a p D'),
      ← Category.assoc, toOver_map_eq B S hS i, CostructuredArrow.w i.hom]
  · rw [Category.assoc, Category.assoc,
      hrep.lift_snd (D.U.1.hom ≫ a.hom) D.g (baseChangeTarget_lift_cond B S hS a p D),
      hrep.lift_snd (hrep.fst D'.V.1.hom) (hrep.snd D'.V.1.hom ≫ j.hom.left)
        (representablePullback_lift_cond B S hS p hrep j), ← Category.assoc,
      hrep.lift_snd (D'.U.1.hom ≫ a.hom) D'.g (baseChangeTarget_lift_cond B S hS a p D')]
    exact hcond

/-! ### The graph section -/

/-- The compatibility making the graph section well defined: the structure morphism of a chart
of `Y` and the identity agree over `Z`. -/
theorem etaleChartGraph_cond (W : SmallEtale B S hS Y.1) :
    W.1.hom ≫ p.hom =
      yoneda.map (𝟙 ((SmallEtale.toOver B S hS Y.1).obj W)) ≫
        ((smallEtalePostcomp B S hS p hp).obj W).1.hom :=
  ((congrArg (fun m : yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj W) ⟶
        yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj W) ↦ m ≫ (W.1.hom ≫ p.hom))
      (yoneda.map_id ((SmallEtale.toOver B S hS Y.1).obj W))).trans
    (Category.id_comp (W.1.hom ≫ p.hom))).symm

/-- The graph section of an étale chart of `Y` into the base change along `p` of its
postcomposition: the lift of the structure morphism of the chart and of the identity. -/
noncomputable abbrev etaleChartGraph (W : SmallEtale B S hS Y.1) :
    W ⟶ etaleBaseChangeChart B S hS p hrep ((smallEtalePostcomp B S hS p hp).obj W) :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hrep.lift W.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj W))
      (etaleChartGraph_cond B S hS p hp W))
    (hrep.lift_fst W.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj W))
      (etaleChartGraph_cond B S hS p hp W)))

/-- The lift underlying the graph section. -/
theorem toOver_map_etaleChartGraph (W : SmallEtale B S hS Y.1) :
    (SmallEtale.toOver B S hS Y.1).map (etaleChartGraph B S hS p hp hrep W) =
      hrep.lift W.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj W))
        (etaleChartGraph_cond B S hS p hp W) :=
  rfl

/-- **The graph section splits the projection.**  Both sides are morphisms of charts of `Z`, so
they agree as soon as their underlying morphisms of the big fppf site do, and that is the second
component of the universal property of the fibre product. -/
theorem etaleChartGraph_comp_projection (W : SmallEtale B S hS Y.1) :
    (smallEtalePostcomp B S hS p hp).map (etaleChartGraph B S hS p hp hrep W) ≫
        etaleChartProjection B S hS p hp hrep ((smallEtalePostcomp B S hS p hp).obj W) =
      𝟙 ((smallEtalePostcomp B S hS p hp).obj W) :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (hrep.lift_snd W.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj W))
      (etaleChartGraph_cond B S hS p hp W)))

/-- **The base-changed diagram of a postcomposed diagram is dominated by the diagram itself**,
through the graph section: the lift of the postcomposed diagram is the vertical morphism of the
diagram followed by the graph section. -/
theorem baseChangeTarget_postcompTarget_g (e : ChartDiagram B S hS X.1 Y.1 a.hom) :
    ((e.postcompTarget B S hS a p hp).baseChangeTarget B S hS a p hrep).g =
      e.g ≫ (SmallEtale.toOver B S hS Y.1).map (etaleChartGraph B S hS p hp hrep e.V) :=
  hrep.hom_ext
    (Eq.trans
      ((e.postcompTarget B S hS a p hp).baseChangeTarget B S hS a p hrep).comm.symm
      (Eq.trans e.comm
        (Eq.trans
          (congrArg (fun m ↦ yoneda.map e.g ≫ m)
            (hrep.lift_fst e.V.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj e.V))
              (etaleChartGraph_cond B S hS p hp e.V)).symm)
          (Eq.trans (Category.assoc (yoneda.map e.g) _ _).symm
            (congrArg (fun m ↦ m ≫ hrep.fst (e.postcompTarget B S hS a p hp).V.1.hom)
              (yoneda.map_comp e.g
                (hrep.lift e.V.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj e.V))
                  (etaleChartGraph_cond B S hS p hp e.V))).symm)))))
    (Eq.trans
      (hrep.lift_snd (e.U.1.hom ≫ a.hom) e.g
        (baseChangeTarget_lift_cond B S hS a p (e.postcompTarget B S hS a p hp)))
      (Eq.trans (Category.comp_id e.g).symm
        (Eq.trans
          (congrArg (fun m ↦ e.g ≫ m)
            (hrep.lift_snd e.V.1.hom (𝟙 ((SmallEtale.toOver B S hS Y.1).obj e.V))
              (etaleChartGraph_cond B S hS p hp e.V)).symm)
          (Category.assoc e.g _ _).symm)))

/-! ### Restriction of linear maps of sections -/

variable (N : Modules.{u, u} B S hS X.1 X.2) (M : Modules.{u, u} B S hS Z.1 Z.2)

/-- **The restriction of a linear map of sections along `a ≫ p` to one along `a`**: its value at
a diagram over `a` is its value at the diagram over `a ≫ p` obtained by postcomposing the chart
of `Y` with `p`.

All four fields are the four fields of the given linear map of sections at the postcomposed
diagrams: postcomposition leaves the underlying objects of the charts, hence the sections, the
rings of regular functions and the vertical pullback of regular functions, unchanged. -/
def moduleFMapEtaleRestrict (ξ : ModuleFMap B S hS (a ≫ p) N M) :
    ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M) where
  app e := ξ.app (e.postcompTarget B S hS a p hp)
  naturality e e' i j h s := ξ.naturality (e.postcompTarget B S hS a p hp)
    (e'.postcompTarget B S hS a p hp) i ((smallEtalePostcomp B S hS p hp).map j) h s
  map_add e := ξ.map_add (e.postcompTarget B S hS a p hp)
  map_smul e := ξ.map_smul (e.postcompTarget B S hS a p hp)

/-- The restriction, on sections.  This is the definition, stated so that it can be rewritten
with. -/
theorem moduleFMapEtaleRestrict_app (ξ : ModuleFMap B S hS (a ≫ p) N M)
    (e : ChartDiagram B S hS X.1 Y.1 a.hom)
    (s : ((etaleModulePullback B S hS p hp).obj M).val.obj (op e.V)) :
    (moduleFMapEtaleRestrict B S hS a p hp N M ξ).app e s =
      ξ.app (e.postcompTarget B S hS a p hp) s :=
  rfl

/-- **The values of a linear map of sections along `a ≫ p` are determined by its restriction.**
At a diagram `D` over `a ≫ p` the value on a section `s` is the value of the restriction at the
base-changed diagram, applied to the restriction of `s` along the projection.

This is the naturality of the linear map of sections for the morphism of diagrams which is the
identity on the chart of `X` and the projection on the chart of `Z`; what it needs is that the
lift to the fibre product, followed by the projection, is the vertical morphism of `D`. -/
theorem moduleFMapEtaleRestrict_app_baseChangeTarget (ξ : ModuleFMap B S hS (a ≫ p) N M)
    (D : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom) (s : M.val.obj (op D.V)) :
    (moduleFMapEtaleRestrict B S hS a p hp N M ξ).app (D.baseChangeTarget B S hS a p hrep)
        (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s) =
      ξ.app D s := by
  refine Eq.trans (ξ.naturality D
    ((D.baseChangeTarget B S hS a p hrep).postcompTarget B S hS a p hp) (𝟙 D.U)
    (etaleChartProjection B S hS p hp hrep D.V) ?_ s) ?_
  · rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (baseChangeTarget_g_comp_projection B S hS a p hp hrep D).symm
  · exact val_map_id_apply B S hS N D.U (ξ.app D s)

include hrep in
/-- **The restriction of linear maps of sections is injective.**  Every value of a linear map of
sections along `a ≫ p` is a value of its restriction. -/
theorem moduleFMapEtaleRestrict_injective :
    Function.Injective (moduleFMapEtaleRestrict B S hS a p hp N M) := by
  intro ξ ξ' h
  refine ModuleFMap.ext B S hS (funext fun D ↦ funext fun s ↦ ?_)
  refine (moduleFMapEtaleRestrict_app_baseChangeTarget B S hS a p hp hrep N M ξ D s).symm.trans
    (Eq.trans ?_ (moduleFMapEtaleRestrict_app_baseChangeTarget B S hS a p hp hrep N M ξ' D s))
  exact congrArg (fun ζ : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M) ↦
    ζ.app (D.baseChangeTarget B S hS a p hrep)
      (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s)) h

/-! ### The inverse -/

/-- Restricting a section along a morphism of charts of `Z` and then along the projection is
restricting it along the composite. -/
theorem val_map_comp_etaleChartProjection {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W)
    (s : M.val.obj (op W)) :
    M.val.map (etaleChartProjection B S hS p hp hrep W').op (M.val.map j.op s) =
      M.val.map (etaleChartProjection B S hS p hp hrep W' ≫ j).op s :=
  val_map_comp_apply B S hS M j (etaleChartProjection B S hS p hp hrep W') s

/-- The two composites of the naturality square of the projections restrict a section the same
way. -/
theorem val_map_etaleChartProjection_naturality {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W)
    (s : M.val.obj (op W)) :
    M.val.map (etaleChartProjection B S hS p hp hrep W' ≫ j).op s =
      M.val.map ((smallEtalePostcomp B S hS p hp).map (etaleBaseChangeChartMap B S hS p hrep j) ≫
        etaleChartProjection B S hS p hp hrep W).op s :=
  congrArg (fun m : (smallEtalePostcomp B S hS p hp).obj
        (etaleBaseChangeChart B S hS p hrep W') ⟶ W ↦ M.val.map m.op s)
    (etaleChartProjection_naturality B S hS p hp hrep j)

/-- Restricting a section along the projection and then along the postcomposed base change of a
morphism of charts of `Z` is restricting it along the composite. -/
theorem val_map_comp_etaleBaseChangeChartMap {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W)
    (s : M.val.obj (op W)) :
    M.val.map ((smallEtalePostcomp B S hS p hp).map (etaleBaseChangeChartMap B S hS p hrep j) ≫
          etaleChartProjection B S hS p hp hrep W).op s =
      M.val.map ((smallEtalePostcomp B S hS p hp).map
          (etaleBaseChangeChartMap B S hS p hrep j)).op
        (M.val.map (etaleChartProjection B S hS p hp hrep W).op s) :=
  (val_map_comp_apply B S hS M (etaleChartProjection B S hS p hp hrep W)
    ((smallEtalePostcomp B S hS p hp).map (etaleBaseChangeChartMap B S hS p hrep j)) s).symm

/-- Restricting a section of the étale restriction of `M` along the base change of a morphism of
charts of `Z` is restricting it along the postcomposition of that base change.  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleModulePullback_val_map_apply`. -/
theorem val_map_etaleBaseChangeChartMap {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W)
    (s : M.val.obj (op W)) :
    M.val.map ((smallEtalePostcomp B S hS p hp).map
          (etaleBaseChangeChartMap B S hS p hrep j)).op
        (M.val.map (etaleChartProjection B S hS p hp hrep W).op s) =
      ((etaleModulePullback B S hS p hp).obj M).val.map
          (etaleBaseChangeChartMap B S hS p hrep j).op
        (M.val.map (etaleChartProjection B S hS p hp hrep W).op s) :=
  (QuasiCoherentDescent.etaleModulePullback_val_map_apply B S hS p hp M
    (etaleBaseChangeChartMap B S hS p hrep j)
    (M.val.map (etaleChartProjection B S hS p hp hrep W).op s)).symm

/-- **Restricting a section along a morphism of charts of `Z` and then along the projection is
restricting it along the projection and then along the base change of that morphism**, the latter
read as a restriction of the étale restriction of `M`.

The four steps are kept apart: each is one definitional identification, and asking for them at
once exhausts the heartbeat budget. -/
theorem val_map_etaleChartProjection_comm {W W' : SmallEtale B S hS Z.1} (j : W' ⟶ W)
    (s : M.val.obj (op W)) :
    M.val.map (etaleChartProjection B S hS p hp hrep W').op (M.val.map j.op s) =
      ((etaleModulePullback B S hS p hp).obj M).val.map
          (etaleBaseChangeChartMap B S hS p hrep j).op
        (M.val.map (etaleChartProjection B S hS p hp hrep W).op s) :=
  ((val_map_comp_etaleChartProjection B S hS p hp hrep M j s).trans
      ((val_map_etaleChartProjection_naturality B S hS p hp hrep M j s).trans
        (val_map_comp_etaleBaseChangeChartMap B S hS p hp hrep M j s))).trans
    (val_map_etaleBaseChangeChartMap B S hS p hp hrep M j s)

/-- **The extension is compatible with étale restriction of both charts.**  The morphism of
base-changed diagrams is `AlgebraicGeometry.Space.baseChangeTarget_g_naturality`, and the two
restrictions of the section agree by
`AlgebraicGeometry.Space.val_map_etaleChartProjection_comm`. -/
theorem etaleExtend_naturality
    (η : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M))
    (D D' : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom) (i : D'.U ⟶ D.U) (j : D'.V ⟶ D.V)
    (hcond : (SmallEtale.toOver B S hS X.1).map i ≫ D.g =
      D'.g ≫ (SmallEtale.toOver B S hS Z.1).map j) (s : M.val.obj (op D.V)) :
    η.app (D'.baseChangeTarget B S hS a p hrep)
        (M.val.map (etaleChartProjection B S hS p hp hrep D'.V).op (M.val.map j.op s)) =
      N.val.map i.op (η.app (D.baseChangeTarget B S hS a p hrep)
        (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s)) :=
  Eq.trans
    (congrArg (fun y : ((etaleModulePullback B S hS p hp).obj M).val.obj
        (op (D'.baseChangeTarget B S hS a p hrep).V) ↦
      η.app (D'.baseChangeTarget B S hS a p hrep) y)
      (val_map_etaleChartProjection_comm B S hS p hp hrep M j s))
    (η.naturality (D.baseChangeTarget B S hS a p hrep) (D'.baseChangeTarget B S hS a p hrep) i
      (etaleBaseChangeChartMap B S hS p hrep j)
      (baseChangeTarget_g_naturality B S hS a p hrep D D' i j hcond)
      (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s))

/-- **The extension is additive**: the restriction of sections and the given linear map of
sections are. -/
theorem etaleExtend_add
    (η : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M))
    (D : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom) (s t : M.val.obj (op D.V)) :
    η.app (D.baseChangeTarget B S hS a p hrep)
        (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op (s + t)) =
      η.app (D.baseChangeTarget B S hS a p hrep)
          (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s) +
        η.app (D.baseChangeTarget B S hS a p hrep)
          (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op t) :=
  Eq.trans
    (congrArg (fun y ↦ η.app (D.baseChangeTarget B S hS a p hrep) y)
      ((M.val.map (etaleChartProjection B S hS p hp hrep D.V).op).hom.map_add s t))
    (η.map_add (D.baseChangeTarget B S hS a p hrep) _ _)

/-- **The extension is semilinear over the vertical pullback of regular functions of the given
diagram**: the restriction of sections is semilinear over restriction of regular functions, the
given linear map of sections is semilinear over the pullback along the lift, and pulling back
along the lift after the projection is pulling back along the vertical morphism. -/
theorem etaleExtend_smul
    (η : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M))
    (D : ChartDiagram B S hS X.1 Z.1 (a ≫ p).hom)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Z.1 Z.2).O)).obj.obj (op D.V))
    (s : M.val.obj (op D.V)) :
    η.app (D.baseChangeTarget B S hS a p hrep)
        (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op (r • s)) =
      chartDiagramPullback B S hS (a ≫ p) D r •
        η.app (D.baseChangeTarget B S hS a p hrep)
          (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s) :=
  Eq.trans
    (congrArg (fun y ↦ η.app (D.baseChangeTarget B S hS a p hrep) y)
      (M.val.map_smul (etaleChartProjection B S hS p hp hrep D.V).op r s))
    (Eq.trans (η.map_smul (D.baseChangeTarget B S hS a p hrep) _ _)
      (congrArg
        (fun c ↦ c • η.app (D.baseChangeTarget B S hS a p hrep)
          (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s))
        (Eq.trans
          (chartDiagramPullback_comp_apply B S hS (D.baseChangeTarget B S hS a p hrep).g
            ((SmallEtale.toOver B S hS Z.1).map
              (etaleChartProjection B S hS p hp hrep D.V)) r)
          (congrArg (fun m ↦ ((forget₂ CommRingCat.{u} RingCat.{u}).map
              (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) r)
            (baseChangeTarget_g_comp_projection B S hS a p hp hrep D)))))

/-- **The extension of a linear map of sections along `a` to one along `a ≫ p`**: its value at a
diagram over `a ≫ p` is the value of the given map at the base-changed diagram, applied to the
restriction of the section along the projection.

This is the only possible value, by
`AlgebraicGeometry.Space.moduleFMapEtaleRestrict_app_baseChangeTarget`. -/
noncomputable def moduleFMapEtaleExtend
    (η : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M)) :
    ModuleFMap B S hS (a ≫ p) N M where
  app D s := η.app (D.baseChangeTarget B S hS a p hrep)
    (M.val.map (etaleChartProjection B S hS p hp hrep D.V).op s)
  naturality D D' i j hcond s := etaleExtend_naturality B S hS a p hp hrep N M η D D' i j hcond s
  map_add D s t := etaleExtend_add B S hS a p hp hrep N M η D s t
  map_smul D r s := etaleExtend_smul B S hS a p hp hrep N M η D r s

/-! ### The restriction of the extension -/

/-- Restricting a section of the étale restriction of `M` along the graph section is restricting
it along the postcomposition of the graph section.  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleModulePullback_val_map_apply`. -/
theorem val_map_etaleChartGraph (W : SmallEtale B S hS Y.1)
    (t : M.val.obj (op ((smallEtalePostcomp B S hS p hp).obj W))) :
    ((etaleModulePullback B S hS p hp).obj M).val.map
          (etaleChartGraph B S hS p hp hrep W).op
        (M.val.map (etaleChartProjection B S hS p hp hrep
          ((smallEtalePostcomp B S hS p hp).obj W)).op t) =
      M.val.map ((smallEtalePostcomp B S hS p hp).map
          (etaleChartGraph B S hS p hp hrep W)).op
        (M.val.map (etaleChartProjection B S hS p hp hrep
          ((smallEtalePostcomp B S hS p hp).obj W)).op t) :=
  QuasiCoherentDescent.etaleModulePullback_val_map_apply B S hS p hp M
    (etaleChartGraph B S hS p hp hrep W)
    (M.val.map (etaleChartProjection B S hS p hp hrep
      ((smallEtalePostcomp B S hS p hp).obj W)).op t)

/-- Restricting a section along the projection and then along the postcomposed graph section is
restricting it along the composite. -/
theorem val_map_comp_etaleChartGraph (W : SmallEtale B S hS Y.1)
    (t : M.val.obj (op ((smallEtalePostcomp B S hS p hp).obj W))) :
    M.val.map ((smallEtalePostcomp B S hS p hp).map
          (etaleChartGraph B S hS p hp hrep W)).op
        (M.val.map (etaleChartProjection B S hS p hp hrep
          ((smallEtalePostcomp B S hS p hp).obj W)).op t) =
      M.val.map ((smallEtalePostcomp B S hS p hp).map
            (etaleChartGraph B S hS p hp hrep W) ≫
          etaleChartProjection B S hS p hp hrep
            ((smallEtalePostcomp B S hS p hp).obj W)).op t :=
  val_map_comp_apply B S hS M
    (etaleChartProjection B S hS p hp hrep ((smallEtalePostcomp B S hS p hp).obj W))
    ((smallEtalePostcomp B S hS p hp).map (etaleChartGraph B S hS p hp hrep W)) t

/-- The composite of the postcomposed graph section with the projection restricts a section the
way the identity does, the graph section splitting the projection. -/
theorem val_map_etaleChartGraph_comp_projection (W : SmallEtale B S hS Y.1)
    (t : M.val.obj (op ((smallEtalePostcomp B S hS p hp).obj W))) :
    M.val.map ((smallEtalePostcomp B S hS p hp).map
            (etaleChartGraph B S hS p hp hrep W) ≫
          etaleChartProjection B S hS p hp hrep
            ((smallEtalePostcomp B S hS p hp).obj W)).op t =
      M.val.map (𝟙 ((smallEtalePostcomp B S hS p hp).obj W)).op t :=
  congrArg (fun m : (smallEtalePostcomp B S hS p hp).obj W ⟶
      (smallEtalePostcomp B S hS p hp).obj W ↦ M.val.map m.op t)
    (etaleChartGraph_comp_projection B S hS p hp hrep W)

/-- **The graph section cancels the projection on sections.** -/
theorem val_map_etaleChartGraph_cancel (W : SmallEtale B S hS Y.1)
    (t : M.val.obj (op ((smallEtalePostcomp B S hS p hp).obj W))) :
    ((etaleModulePullback B S hS p hp).obj M).val.map
          (etaleChartGraph B S hS p hp hrep W).op
        (M.val.map (etaleChartProjection B S hS p hp hrep
          ((smallEtalePostcomp B S hS p hp).obj W)).op t) =
      t :=
  ((val_map_etaleChartGraph B S hS p hp hrep M W t).trans
      ((val_map_comp_etaleChartGraph B S hS p hp hrep M W t).trans
        (val_map_etaleChartGraph_comp_projection B S hS p hp hrep M W t))).trans
    (val_map_id_apply B S hS M ((smallEtalePostcomp B S hS p hp).obj W) t)

/-- The morphism of diagrams which is the identity on the chart of `X` and the graph section on
the chart of `Y`, from the given diagram to the base change of its postcomposition. -/
theorem baseChangeTarget_postcompTarget_cond (e : ChartDiagram B S hS X.1 Y.1 a.hom) :
    (SmallEtale.toOver B S hS X.1).map (𝟙 e.U) ≫
        ((e.postcompTarget B S hS a p hp).baseChangeTarget B S hS a p hrep).g =
      e.g ≫ (SmallEtale.toOver B S hS Y.1).map (etaleChartGraph B S hS p hp hrep e.V) := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact baseChangeTarget_postcompTarget_g B S hS a p hp hrep e

/-- The restriction of the extension, on sections: the value at the base change of the
postcomposed diagram, applied to the restriction of the section along the projection. -/
theorem moduleFMapEtaleRestrict_moduleFMapEtaleExtend_app
    (η : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M))
    (e : ChartDiagram B S hS X.1 Y.1 a.hom)
    (t : ((etaleModulePullback B S hS p hp).obj M).val.obj (op e.V)) :
    (moduleFMapEtaleRestrict B S hS a p hp N M
          (moduleFMapEtaleExtend B S hS a p hp hrep N M η)).app e t =
      η.app ((e.postcompTarget B S hS a p hp).baseChangeTarget B S hS a p hrep)
        (M.val.map (etaleChartProjection B S hS p hp hrep
          ((smallEtalePostcomp B S hS p hp).obj e.V)).op t) :=
  rfl

/-- **The restriction of the extension is the given linear map of sections.**  The graph section
splits the projection, so the two restrictions of sections cancel, and the morphism of diagrams
which is the identity on the chart of `X` and the graph section on the chart of `Y` carries the
value at the base change of the postcomposed diagram to the value at the given one. -/
theorem moduleFMapEtaleRestrict_moduleFMapEtaleExtend
    (η : ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M)) :
    moduleFMapEtaleRestrict B S hS a p hp N M
        (moduleFMapEtaleExtend B S hS a p hp hrep N M η) = η :=
  ModuleFMap.ext B S hS (funext fun e ↦ funext fun t ↦
    (moduleFMapEtaleRestrict_moduleFMapEtaleExtend_app B S hS a p hp hrep N M η e t).trans
      ((val_map_id_apply B S hS N e.U
            (η.app ((e.postcompTarget B S hS a p hp).baseChangeTarget B S hS a p hrep)
              (M.val.map (etaleChartProjection B S hS p hp hrep
                ((smallEtalePostcomp B S hS p hp).obj e.V)).op t))).symm.trans
        ((η.naturality ((e.postcompTarget B S hS a p hp).baseChangeTarget B S hS a p hrep) e
              (𝟙 e.U) (etaleChartGraph B S hS p hp hrep e.V)
              (baseChangeTarget_postcompTarget_cond B S hS a p hp hrep e)
              (M.val.map (etaleChartProjection B S hS p hp hrep
                ((smallEtalePostcomp B S hS p hp).obj e.V)).op t)).symm.trans
          (congrArg (fun y ↦ η.app e y)
            (val_map_etaleChartGraph_cancel B S hS p hp hrep M e.V t)))))

include hrep in
/-- **Restriction of linear maps of sections along a composite with an étale second factor is a
bijection.**  A linear map of sections along `a ≫ p` from `N` to `M` is exactly a linear map of
sections along `a` from `N` to the étale restriction of `M`.

For `a` the identity this is the hom-set bijection of the adjunction between étale restriction of
modules and the direct image; in the form stated it is what describes a morphism out of a
pullback of an étale restriction. -/
theorem bijective_moduleFMapEtaleRestrict :
    Function.Bijective (moduleFMapEtaleRestrict B S hS a p hp N M) :=
  ⟨moduleFMapEtaleRestrict_injective B S hS a p hp hrep N M,
    fun η ↦ ⟨moduleFMapEtaleExtend B S hS a p hp hrep N M η,
      moduleFMapEtaleRestrict_moduleFMapEtaleExtend B S hS a p hp hrep N M η⟩⟩

/-- The bijection of `AlgebraicGeometry.Space.bijective_moduleFMapEtaleRestrict`, packaged as an
equivalence with `AlgebraicGeometry.Space.moduleFMapEtaleExtend` as its inverse. -/
noncomputable def moduleFMapEtaleRestrictEquiv :
    ModuleFMap B S hS (a ≫ p) N M ≃
      ModuleFMap B S hS a N ((etaleModulePullback B S hS p hp).obj M) where
  toFun := moduleFMapEtaleRestrict B S hS a p hp N M
  invFun := moduleFMapEtaleExtend B S hS a p hp hrep N M
  left_inv _ξ := moduleFMapEtaleRestrict_injective B S hS a p hp hrep N M
    (moduleFMapEtaleRestrict_moduleFMapEtaleExtend B S hS a p hp hrep N M _)
  right_inv η := moduleFMapEtaleRestrict_moduleFMapEtaleExtend B S hS a p hp hrep N M η

end Restrict

end AlgebraicGeometry.Space

end
