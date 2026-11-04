module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCounitComp

/-!
# The base change map of a square, on the chart sections of the base-changed charts

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `f` and `f'` representable, let `K` be an `𝒪_X`-module and let `d` be a diagram of étale
scheme charts over `g`.  Base change of charts turns `d` into the square of charts of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeChartSquare.lean`, whose diagram over `i`
is `AlgebraicGeometry.Space.chartDiagramOfSquare`.  This file assembles the pieces out of which
the two sides of the chartwise identification of the base change map `g^*f_*K ⟶ f'_*(i^*K)` are
built: **both sides are chart components of the two composite direct images around the square**,
one along `i ≫ f` and one along `f' ≫ g`, and the file writes each of them in that form.

Nothing is assumed of `K`, and the square is only required to commute.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardSquareComparison_eq` and
  `AlgebraicGeometry.Space.modulePushforwardSquareComparison_app`: the comparison of the two
  composite direct images around the square, as an equation between natural transformations and
  at a module.
* `AlgebraicGeometry.Space.modulePushforward_map_unit_comp_compIso_hom_comp_compIso_inv`: the
  morphism of `𝒪_Y`-modules the base change map is built from, factored through the direct image
  along `i ≫ f` and the transport along the equality of the two composites.
* `AlgebraicGeometry.Space.counitApp_smallBaseChangeDiagram_comp`: the chart component along
  `f'` at the base-changed chart of `d.U`, after the chart component along `g` at `d`, as the
  chart component along `f' ≫ g` at the composite chart diagram.
* `AlgebraicGeometry.Space.counitApp_chartDiagramOfSquare_comp`: the chart component along
  `i ≫ f` at the composite of the diagram of the chart square and the base-changed chart of
  `d.V`, as the chart component along `f` at the latter followed by the one along `i` at the
  former.
* `AlgebraicGeometry.Space.counitApp_chartDiagramOfSquare_unit`: that composite, applied to the
  direct image along `f` of the unit of the Stacks 03D7 adjunction of `i`, **is the unit section
  along `i` at the chart square** of the chart component along `f`.
* `Space.counitApp_smallBaseChangeDiagram_comp_eq_counitApp_chartDiagramOfSquare_comp`:
  the two sides meet.  The chart component along `f' ≫ g` at the left composite chart diagram,
  read after the transport along the commutativity of the square, is the chart component along
  `i ≫ f` at the right composite chart diagram.
* `AlgebraicGeometry.Space.counitApp_val_app_moduleBaseChangeMap_modulePullbackUnitSection`:
  **the chartwise identification of the base change map.**  The chart component along `f'` at
  the base-changed chart of `d.U`, applied to the value of the base change map on the unit
  section of a section `s` of `f_*K` over `d.V`, is the unit section along `i` at the chart
  square of the chart component along `f` at the base-changed chart of `d.V`, applied to `s`.
  Nothing is assumed: the square is only required to commute, `K` carries no hypothesis and the
  two charts are arbitrary.

## Implementation notes

Every equation here is stated at the smallest type that carries it, and in particular the
unfolding of `AlgebraicGeometry.Space.modulePushforwardSquareComparison` is stated between
*natural transformations* and only then evaluated at a module by `congrArg`: asked for directly
at a component, the same `rfl` makes the kernel take the component of the comparison apart,
which it cannot do inside its budget.  For the same reason the morphisms the base change map
factors through are composed, and their composites simplified, at the level of morphisms of
modules.

The two chart components of each side are glued by
`AlgebraicGeometry.Space.modulePushforwardCounitApp_comp`, whose own two conversions are what
`AlgebraicGeometry.Space.modulePushforwardHomFMap_app_mk` supplies: that equation is stated at a
chart diagram given **unbundled**, by its two charts and its vertical morphism, which is what
makes the two spellings of the middle chart comparable under a rigid head.  The transport
between the two composite chart diagrams — one over `i ≫ f`, one over `f' ≫ g` — is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_congr`, whose two inputs are the
commutativity of the square and the commutativity
`AlgebraicGeometry.Space.baseChangeChartSquareMap_snd` of the chart square.

**The two legs of the chartwise identification are stated with the comparison morphisms they
compose as bare variables**,
`AlgebraicGeometry.Space.counitApp_val_app_moduleBaseChangeMap_of_eq_comp` and
`AlgebraicGeometry.Space.counitApp_chartDiagramOfSquare_comp_of_eq_comp`, with the
factorisation they satisfy as a hypothesis.  That is what makes them affordable, and it is the
one shape in which they are: the step each performs is reading a composite of morphisms of
modules on a section, which is `AlgebraicGeometry.Space.val_app_apply_of_eq_comp`, a `rfl` at
bare variables; instantiated at the component of the comparison of Stacks 03LU and at the
transport `eqToHom` of the two composite direct images, the same conversion is a `whnf` timeout,
because the unifier then unfolds the sheaf of modules of the comparison.  With the morphisms
carried as variables every use is a substitution into a statement already checked, and the
assembly supplies them at the concrete comparison together with the two factorisations, which
are equations between *morphisms* and cost nothing.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **A morphism of modules which factors reads on a section as the second factor applied to the
value of the first.**  All three morphisms are variables and the factorisation is a hypothesis,
so every use is a substitution into a statement already checked; see the implementation notes
for why that matters here. -/
theorem val_app_apply_of_eq_comp {Z : AlgebraicSpaces B S hS}
    {P Q R : Modules.{u, u} B S hS Z.1 Z.2} {m : P ⟶ R} (β : P ⟶ Q) (c : Q ⟶ R)
    (h : m = β ≫ c) (V : SmallEtale B S hS Z.1) (w : P.val.obj (op V)) :
    m.val.app (op V) w = c.val.app (op V) (β.val.app (op V) w) := by
  subst h; rfl

/-! ### The comparison of the two composite direct images around the square -/

/-- **The comparison of the two composite direct images around a commutative square.**  It is
the comparison of Stacks 03LU for `i` then `f`, then the transport along the equality of the two
composites, then the inverse of the comparison for `f'` then `g`: that is its definition, stated
so that it can be used as an equation rather than unfolded by unification.

Stating it at the natural transformations, and not at one of their components, is what makes it
usable at all: asking for the same `rfl` at a component makes the kernel take the component of
the comparison apart, which it cannot do inside its budget. -/
theorem modulePushforwardSquareComparison_eq (comm : i ≫ f = f' ≫ g) :
    modulePushforwardSquareComparison B S hS i f' f g comm =
      (modulePushforwardCompIso B S hS i f).hom ≫
        (eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) comm) ≫
          (modulePushforwardCompIso B S hS f' g).inv) := rfl

/-- `AlgebraicGeometry.Space.modulePushforwardSquareComparison_eq` at a module. -/
theorem modulePushforwardSquareComparison_app (comm : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (modulePushforwardSquareComparison B S hS i f' f g comm).app N =
      (modulePushforwardCompIso B S hS i f).hom.app N ≫
        ((eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) comm)).app N ≫
          (modulePushforwardCompIso B S hS f' g).inv.app N) :=
  (congrArg
      (fun α : modulePushforward B S hS i ⋙ modulePushforward B S hS f ⟶
          modulePushforward B S hS f' ⋙ modulePushforward B S hS g ↦ α.app N)
      (modulePushforwardSquareComparison_eq B S hS i f' f g comm)).trans
  ((NatTrans.comp_app (modulePushforwardCompIso B S hS i f).hom
      (eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) comm) ≫
        (modulePushforwardCompIso B S hS f' g).inv) N).trans
    (congrArg
      (fun m : (modulePushforward B S hS (i ≫ f)).obj N ⟶
          (modulePushforward B S hS f' ⋙ modulePushforward B S hS g).obj N ↦
        (modulePushforwardCompIso B S hS i f).hom.app N ≫ m)
      (NatTrans.comp_app
        (eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) comm))
        (modulePushforwardCompIso B S hS f' g).inv N)))

/-! ### The factorisation of the base change map through the direct image along `i ≫ f` -/

variable (K : Modules.{u, u} B S hS X.1 X.2)

/-- **The morphism of `𝒪_Y`-modules `f_*K ⟶ (i ≫ f)_*(i^*K)` the base change map is built
from**: the direct image along `f` of the unit of the Stacks 03D7 adjunction of `i`, followed by
the comparison of Stacks 03LU for `i` then `f`. -/
theorem modulePushforward_map_unit_comp_compIso_hom_comp_compIso_inv
    (comm : i ≫ f = f' ≫ g) :
    ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
          ((modulePushforwardCompIso B S hS i f).hom.app
              ((modulePullback B S hS i).obj K) ≫
            (eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) comm)).app
              ((modulePullback B S hS i).obj K))) ≫
        (modulePushforwardCompIso B S hS f' g).inv.app ((modulePullback B S hS i).obj K) =
      (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
        (modulePushforwardSquareComparison B S hS i f' f g comm).app
          ((modulePullback B S hS i).obj K) := by
  rw [modulePushforwardSquareComparison_app B S hS i f' f g comm
    ((modulePullback B S hS i).obj K)]
  simp only [Category.assoc]

/-- The unit section along `i`, unfolded: the chart component of the direct image along `i`
applied to the unit of the Stacks 03D7 adjunction.  This is the definition of
`AlgebraicGeometry.Space.modulePullbackUnitSection`, stated so that it can be used as an
equation rather than unfolded by unification. -/
theorem modulePullbackUnitSection_eq_counitApp (q : ChartDiagram B S hS X'.1 X.1 i.hom)
    (y : K.val.obj (op q.V)) :
    modulePullbackUnitSection B S hS i K q y =
      modulePushforwardCounitApp B S hS i ((modulePullback B S hS i).obj K) q
        (((modulePullbackAdjunction B S hS i).unit.app K).val.app (op q.V) y) := rfl

/-! ### The two sides of the identification, as chart components of a composite direct image -/

variable (hf : yoneda.relativelyRepresentable f.hom)
    (hf' : yoneda.relativelyRepresentable f'.hom)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)

/-- **The left-hand side of the identification as a chart component of `(f' ≫ g)_*`.**  The
chart component along `f'` at the base-changed chart of `d.U`, after the chart component along
`g` at `d`, is the chart component along `f' ≫ g` at the composite chart diagram, up to the
inverse of the comparison of Stacks 03LU. -/
theorem counitApp_smallBaseChangeDiagram_comp (N : Modules.{u, u} B S hS X'.1 X'.2)
    (σ : ((modulePushforward B S hS (f' ≫ g)).obj N).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f' N (smallBaseChangeDiagram f' hf' d.U)
        (modulePushforwardCounitApp B S hS g ((modulePushforward B S hS f').obj N) d
          (((modulePushforwardCompIso B S hS f' g).inv.app N).val.app (op d.V) σ)) =
      modulePushforwardCounitApp B S hS (f' ≫ g) N
        (ChartDiagram.comp B S hS f' g (smallBaseChangeDiagram f' hf' d.U).g d.g
          (smallBaseChangeDiagram f' hf' d.U).comm d.comm) σ :=
  (modulePushforwardCounitApp_comp B S hS f' g
    (U := (smallBaseChangeDiagram f' hf' d.U).U) (V := d.U) (W := d.V)
    (smallBaseChangeDiagram f' hf' d.U).g d.g
    (smallBaseChangeDiagram f' hf' d.U).comm d.comm N σ).symm

/-- **The right-hand side of the identification as a chart component of `(i ≫ f)_*`.**  The
chart component along `i ≫ f` at the composite of the diagram of the chart square and the
base-changed chart of `d.V` is the chart component along `f` at the latter followed by the chart
component along `i` at the former, up to the inverse of the comparison of Stacks 03LU. -/
theorem counitApp_chartDiagramOfSquare_comp (comm : i ≫ f = f' ≫ g)
    (ζ : ((modulePushforward B S hS (i ≫ f)).obj
      ((modulePullback B S hS i).obj K)).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS (i ≫ f) ((modulePullback B S hS i).obj K)
        (ChartDiagram.comp B S hS i f
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).g
          (smallBaseChangeDiagram f hf d.V).g
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).comm
          (smallBaseChangeDiagram f hf d.V).comm) ζ =
      modulePushforwardCounitApp B S hS i ((modulePullback B S hS i).obj K)
        (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)
        (modulePushforwardCounitApp B S hS f
          ((modulePushforward B S hS i).obj ((modulePullback B S hS i).obj K))
          (smallBaseChangeDiagram f hf d.V)
          (((modulePushforwardCompIso B S hS i f).inv.app
            ((modulePullback B S hS i).obj K)).val.app (op d.V) ζ)) :=
  modulePushforwardCounitApp_comp B S hS i f
    (U := (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).U)
    (V := (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).V) (W := d.V)
    (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).g
    (smallBaseChangeDiagram f hf d.V).g
    (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).comm
    (smallBaseChangeDiagram f hf d.V).comm ((modulePullback B S hS i).obj K) ζ

/-- **The unit section along `i` at the chart square, from the chart component along `f` at the
base-changed chart.**  Naturality
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map_mk` of the chart component in the module,
applied to the unit of the Stacks 03D7 adjunction of `i`, followed by the definition of the unit
section. -/
theorem counitApp_chartDiagramOfSquare_unit (comm : i ≫ f = f' ≫ g)
    (s : ((modulePushforward B S hS f).obj K).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS i ((modulePullback B S hS i).obj K)
        (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)
        (modulePushforwardCounitApp B S hS f
          ((modulePushforward B S hS i).obj ((modulePullback B S hS i).obj K))
          (smallBaseChangeDiagram f hf d.V)
          (((modulePushforward B S hS f).map
            ((modulePullbackAdjunction B S hS i).unit.app K)).val.app (op d.V) s)) =
      modulePullbackUnitSection B S hS i K
        (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)
        (modulePushforwardCounitApp B S hS f K
          (smallBaseChangeDiagram f hf d.V) s) :=
  Eq.trans
    (congrArg
      (fun y : ((modulePullback B S hS i ⋙ modulePushforward B S hS i).obj K).val.obj
          (op (smallBaseChangeDiagram f hf d.V).U) ↦
        modulePushforwardCounitApp B S hS i ((modulePullback B S hS i).obj K)
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm) y)
      (modulePushforwardCounitApp_map_mk B S hS f
        ((modulePullbackAdjunction B S hS i).unit.app K)
        (U := (smallBaseChangeDiagram f hf d.V).U) (V := d.V)
        (smallBaseChangeDiagram f hf d.V).g
        (smallBaseChangeDiagram f hf d.V).comm s))
    (modulePullbackUnitSection_eq_counitApp B S hS i K
      (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)
      (modulePushforwardCounitApp B S hS f K
        (smallBaseChangeDiagram f hf d.V) s)).symm


/-! ### The junction of the two sides, and the chartwise identification -/

/-- **The two sides of the identification meet.**  The chart component along `f' ≫ g` at the
composite of the base-changed chart of `d.U` and `d`, read after the transport along the
commutativity of the square, is the chart component along `i ≫ f` at the composite of the
diagram of the chart square and the base-changed chart of `d.V`.

The two composite chart diagrams have the same chart of `X'` — the base change of `d.U` along
`f'` is the upper chart of both — and the same chart of `Y`, namely `d.V`; their vertical
morphisms of schemes are the two ways around the chart square, and those agree by
`AlgebraicGeometry.Space.baseChangeChartSquareMap_snd`.  So this is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_congr` at the commutativity of the square
and at that equality, and nothing else. -/
theorem counitApp_smallBaseChangeDiagram_comp_eq_counitApp_chartDiagramOfSquare_comp
    (comm : i ≫ f = f' ≫ g) (N : Modules.{u, u} B S hS X'.1 X'.2)
    (ζ : ((modulePushforward B S hS (i ≫ f)).obj N).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS (f' ≫ g) N
        (ChartDiagram.comp B S hS f' g (smallBaseChangeDiagram f' hf' d.U).g d.g
          (smallBaseChangeDiagram f' hf' d.U).comm d.comm)
        (((eqToHom (congrArg (fun m : X' ⟶ Y ↦ modulePushforward B S hS m) comm)).app N).val.app
          (op d.V) ζ) =
      modulePushforwardCounitApp B S hS (i ≫ f) N
        (ChartDiagram.comp B S hS i f
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).g
          (smallBaseChangeDiagram f hf d.V).g
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).comm
          (smallBaseChangeDiagram f hf d.V).comm) ζ :=
  modulePushforwardCounitApp_congr B S hS comm N
    (baseChangeChartSquareMap_snd B S hS i f' f g hf hf' d comm) _ _ ζ

/-- **The left-hand side of the chartwise identification, read on a unit section.**  The chart
component along `f'` at the base-changed chart of `d.U`, applied to the value of the base change
map on the unit section of `s`, is the chart component along `f' ≫ g` at the left composite
chart diagram, applied to the section the two upper factors produce from `s`.

The two upper factors `a` and `e` of the morphism the base change map is built from are
variables and the factorisation is the hypothesis `hfac`; the assembly below supplies them at
the comparison of Stacks 03LU and at the transport of the two composite direct images. -/
theorem counitApp_val_app_moduleBaseChangeMap_of_eq_comp (comm : i ≫ f = f' ≫ g)
    (a : (modulePushforward B S hS f).obj K ⟶
      (modulePushforward B S hS (i ≫ f)).obj ((modulePullback B S hS i).obj K))
    (e : (modulePushforward B S hS (i ≫ f)).obj ((modulePullback B S hS i).obj K) ⟶
      (modulePushforward B S hS (f' ≫ g)).obj ((modulePullback B S hS i).obj K))
    (hfac : (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
          (modulePushforwardSquareComparison B S hS i f' f g comm).app
            ((modulePullback B S hS i).obj K) =
        a ≫ (e ≫ (modulePushforwardCompIso B S hS f' g).inv.app
          ((modulePullback B S hS i).obj K)))
    (s : ((modulePushforward B S hS f).obj K).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
        (smallBaseChangeDiagram f' hf' d.U)
        (((moduleBaseChangeMap f g f' i comm).app K).val.app (op d.U)
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj K) d s)) =
      modulePushforwardCounitApp B S hS (f' ≫ g) ((modulePullback B S hS i).obj K)
        (ChartDiagram.comp B S hS f' g (smallBaseChangeDiagram f' hf' d.U).g d.g
          (smallBaseChangeDiagram f' hf' d.U).comm d.comm)
        (e.val.app (op d.V) (a.val.app (op d.V) s)) := by
  rw [val_app_modulePullbackUnitSection_moduleBaseChangeMap B S hS i f' f g comm K d s,
    val_app_apply_of_eq_comp B S hS a
      (e ≫ (modulePushforwardCompIso B S hS f' g).inv.app ((modulePullback B S hS i).obj K))
      hfac d.V s,
    val_app_apply_of_eq_comp B S hS e
      ((modulePushforwardCompIso B S hS f' g).inv.app ((modulePullback B S hS i).obj K))
      rfl d.V (a.val.app (op d.V) s)]
  exact counitApp_smallBaseChangeDiagram_comp B S hS f' g hf' d
    ((modulePullback B S hS i).obj K) (e.val.app (op d.V) (a.val.app (op d.V) s))

/-- **The right-hand side of the chartwise identification, read on a unit section.**  The chart
component along `i ≫ f` at the right composite chart diagram, applied to the section the upper
factor produces from `s`, is the unit section along `i` at the chart square of the chart
component along `f` at the base-changed chart of `d.V`, applied to `s`.

The upper factor `a` is a variable and the factorisation it satisfies — that followed by the
inverse of the comparison of Stacks 03LU it is the direct image along `f` of the unit along
`i` — is the hypothesis `hfac`. -/
theorem counitApp_chartDiagramOfSquare_comp_of_eq_comp (comm : i ≫ f = f' ≫ g)
    (a : (modulePushforward B S hS f).obj K ⟶
      (modulePushforward B S hS (i ≫ f)).obj ((modulePullback B S hS i).obj K))
    (hfac : (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) =
      a ≫ (modulePushforwardCompIso B S hS i f).inv.app ((modulePullback B S hS i).obj K))
    (s : ((modulePushforward B S hS f).obj K).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS (i ≫ f) ((modulePullback B S hS i).obj K)
        (ChartDiagram.comp B S hS i f
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).g
          (smallBaseChangeDiagram f hf d.V).g
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm).comm
          (smallBaseChangeDiagram f hf d.V).comm) (a.val.app (op d.V) s) =
      modulePullbackUnitSection B S hS i K
        (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)
        (modulePushforwardCounitApp B S hS f K
          (smallBaseChangeDiagram f hf d.V) s) := by
  rw [counitApp_chartDiagramOfSquare_comp B S hS i f' f g K hf hf' d comm
      (a.val.app (op d.V) s),
    ← val_app_apply_of_eq_comp B S hS a
      ((modulePushforwardCompIso B S hS i f).inv.app ((modulePullback B S hS i).obj K))
      hfac d.V s]
  exact counitApp_chartDiagramOfSquare_unit B S hS i f' f g K hf hf' d comm s

/-- **The chartwise identification of the base change map of a commutative square.**  On the
chart of `Y'` of a commuting diagram `d` of étale scheme charts over `g`, the base change map
`g^*f_*K ⟶ f'_*(i^*K)` carries the unit section of a section `s` of `f_*K` over `d.V` to the
section of `f'_*(i^*K)` whose chart component along `f'` at the base-changed chart of `d.U` is
the unit section along `i`, at the diagram of the chart square, of the chart component along `f`
at the base-changed chart of `d.V` applied to `s`.

Nothing is assumed: the square is only required to commute, `K` carries no quasi-coherence
hypothesis, no morphism of the square carries one beyond the representability of `f` and `f'`
which the base-changed charts need, and the two charts are arbitrary.

Both sides are chart components of the two composite direct images around the square, by
`AlgebraicGeometry.Space.counitApp_val_app_moduleBaseChangeMap_of_eq_comp` and
`AlgebraicGeometry.Space.counitApp_chartDiagramOfSquare_comp_of_eq_comp`, and those two meet at
`Space.counitApp_smallBaseChangeDiagram_comp_eq_counitApp_chartDiagramOfSquare_comp`.
The two factorisations supplied are
`AlgebraicGeometry.Space.modulePushforward_map_unit_comp_compIso_hom_comp_compIso_inv`
reassociated, and the comparison of Stacks 03LU followed by its inverse. -/
theorem counitApp_val_app_moduleBaseChangeMap_modulePullbackUnitSection
    (comm : i ≫ f = f' ≫ g)
    (s : ((modulePushforward B S hS f).obj K).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
        (smallBaseChangeDiagram f' hf' d.U)
        (((moduleBaseChangeMap f g f' i comm).app K).val.app (op d.U)
          (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj K) d s)) =
      modulePullbackUnitSection B S hS i K
        (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)
        (modulePushforwardCounitApp B S hS f K
          (smallBaseChangeDiagram f hf d.V) s) := by
  have hL : (modulePushforward B S hS f).map
          ((modulePullbackAdjunction B S hS i).unit.app K) ≫
        (modulePushforwardSquareComparison B S hS i f' f g comm).app
          ((modulePullback B S hS i).obj K) =
      ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
          (modulePushforwardCompIso B S hS i f).hom.app ((modulePullback B S hS i).obj K)) ≫
        ((eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) comm)).app
            ((modulePullback B S hS i).obj K) ≫
          (modulePushforwardCompIso B S hS f' g).inv.app
            ((modulePullback B S hS i).obj K)) := by
    simpa only [Category.assoc] using
      (modulePushforward_map_unit_comp_compIso_hom_comp_compIso_inv B S hS i f' f g K comm).symm
  have hR : (modulePushforward B S hS f).map
          ((modulePullbackAdjunction B S hS i).unit.app K) =
      ((modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app K) ≫
          (modulePushforwardCompIso B S hS i f).hom.app ((modulePullback B S hS i).obj K)) ≫
        (modulePushforwardCompIso B S hS i f).inv.app ((modulePullback B S hS i).obj K) := by
    simp
  exact (counitApp_val_app_moduleBaseChangeMap_of_eq_comp B S hS i f' f g K hf' d comm _ _
      hL s).trans
    ((counitApp_smallBaseChangeDiagram_comp_eq_counitApp_chartDiagramOfSquare_comp B S hS i f' f g
        hf hf' d comm ((modulePullback B S hS i).obj K) _).trans
      (counitApp_chartDiagramOfSquare_comp_of_eq_comp B S hS i f' f g K hf hf' d comm _ hR s))

end AlgebraicGeometry.Space

end
