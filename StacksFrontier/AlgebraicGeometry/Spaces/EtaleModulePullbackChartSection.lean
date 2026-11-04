module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitChain
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpUnit

/-!
# The chart component of the unit, pushed across Stacks 03LW

Let `h : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Along `h` the pullback of modules of Stacks 03LU is étale restriction, by
Stacks 03LW (`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`), and the Stacks 03LU
adjunction read through that identification is
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction`.

`AlgebraicGeometry.Space.modulePullbackChartSection` is the chart component of the unit of
Stacks 03LU: the canonical section of `h^*G` over the chart `d.U` of `X` attached to a section of
`G` over the chart `d.V` of `Y` of a diagram `d` of étale scheme charts.  To read it as a section
of the étale restriction `G|_X` it is pushed across Stacks 03LW, and the step that needs no
computation of the comparison itself is: **pushing the chart section across Stacks 03LW
replaces the unit of Stacks 03LU by the unit of étale restriction, under the same chart
projection.**

## Main definitions

* `AlgebraicGeometry.Space.postcompChartDiagram`: the chart diagram of an étale morphism
  attached to a single chart `U` of the source — `U` above its own image
  `AlgebraicGeometry.Space.smallEtalePostcomp` under postcomposition, with identity vertical
  morphism.  This is the diagram at which the comparison is to be read, because the sections of
  the étale restriction over `U` are the sections of `G` over the composite chart.

## Main results

* `AlgebraicGeometry.Space.val_app_moduleChartProjection`: a morphism of modules on the source
  commutes with the chart projection of the direct image, against the direct image of that
  morphism.  This is the naturality of
  `AlgebraicGeometry.Space.moduleChartProjection`, which is a natural transformation of functors
  of sheaves of *sets*, read on a morphism of modules.
* `AlgebraicGeometry.Space.modulePullbackChartSection_eq_moduleChartProjection`: the chart
  section is the chart projection of the value of the unit in the *transported* spelling
  `AlgebraicGeometry.Space.modulePullbackAdjunction`.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection`:
  **Stacks 03LW on a chart section is the chart projection of the unit of étale restriction.**
* `AlgebraicGeometry.Space.moduleChartProjection_app_eq_counitIso`: **the chart projection of
  the direct image of sheaves of sets, in the equivalence-counit form.**  It is built from the
  right Kan extension form `AlgebraicGeometry.Space.smallEtaleComparisonRan` of the
  quasi-inverse of the comparison equivalence of Stacks 03G1; this reads it through the
  quasi-inverse of that equivalence instead, which is the form in which the unit of the
  sheaf-of-sets étale restriction adjunction is computed.
* `AlgebraicGeometry.Space.moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit`:
  **the chart projection of the unit of the sheaf-of-sets étale restriction adjunction is
  restriction of sections along the induced morphism of charts**, and
  `AlgebraicGeometry.Space.moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit_postcomp`:
  over `AlgebraicGeometry.Space.postcompChartDiagram` that morphism is an identity, so the chart
  projection of the unit is the identity on the sections over the composite chart.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection_postcomp`:
  **Stacks 03LW sends the chart section over a single chart of the source back to the section it
  came from.**

## Implementation notes

*What this does and does not do.*  The identity proved here is an exchange, not a computation: it
moves Stacks 03LW off the section and onto the adjunction, replacing the unit of
`AlgebraicGeometry.Space.modulePullbackAdjunction` by the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction`.  That exchange is exact — the two sides
are equal, with no hypothesis — and it is available because
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is
`CategoryTheory.Adjunction.ofNatIsoLeft` of Stacks 03LU along Stacks 03LW, whose unit is the old
unit followed by the direct image of the comparison *by `Eq.refl`*.

*The sheaf-of-sets half.*  The value of the
chart projection of the unit of étale restriction is computed here **for sheaves of sets**: it is
restriction of sections along the morphism of charts `h ∘ U ⟶ W` that the diagram induces, which
over `AlgebraicGeometry.Space.postcompChartDiagram` is an identity.  The input is
`AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit`, stated through the
quasi-inverse of the comparison equivalence of Stacks 03G1, and
`AlgebraicGeometry.Space.moduleChartProjection_app_eq_counitIso` below is the bridge to it:
`AlgebraicGeometry.Space.moduleChartProjection` is built from the right Kan extension form of
that quasi-inverse, and the two are identified by
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso`, whose compatibility with the two counits is
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`.  The morphism of charts is an
identity by `AlgebraicGeometry.Space.toOver_map_eq_chartBaseChangeMap` together with
`AlgebraicGeometry.Space.chartBaseChangeMap_indexOfChartDiagram`, the comparison functor being
full and `AlgebraicGeometry.Space.SmallEtale.toOver` faithful.

*The unit on sections.*  What stands between
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection` and a
value of Stacks 03LW on a chart section is one equation: for every `𝒪_Y`-module `G` and every
chart `W` of `Y`, the unit of Stacks 03LU read through Stacks 03LW agrees on sections with the
unit of the restriction adjunction of sheaves of sets.  It is *well posed* — the two sides have
the same type, the two direct images agreeing on underlying sheaves of sets — and it is **not**
definitional.  It is
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction`, whose
morphism-level form is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`.

*Identity charts.*  The value of Stacks 03LW for `AlgebraicGeometry.Space.chartToSpace` on the
sections over an identity chart of a chart space is a case of the above: the identity
chart of the algebraic space represented by a chart `V` of `Y` postcomposes to `V` itself, by
`Eq.refl`, so `AlgebraicGeometry.Space.postcompChartDiagram` at it is a diagram whose target
chart is `V`, and
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection`
instantiates there with no further work.  That value is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection_postcomp`:
over such a diagram Stacks 03LW returns the section it started from.

*Elaboration.*  Each step is a `congrArg` or an `Eq.trans` in term mode rather than a `rw`: the
two spellings of the direct image of a module have definitionally but not syntactically equal
underlying sheaves of sets, and a rewrite abstracting one of them produces a motive that is not
type-correct at `instances` transparency.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The chart diagram of a single chart of the source -/

/-- **The chart diagram attached to one étale scheme chart of the source of an étale
morphism**: the chart `U` of `X` above its image `h ∘ U` under postcomposition
(`AlgebraicGeometry.Space.smallEtalePostcomp`), with identity vertical morphism of schemes.

The sections of the étale restriction of a module to `X` over `U` are its sections over `h ∘ U`
(`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`), so this is the diagram at which a
comparison of the pullback with the étale restriction is read on sections. -/
def postcompChartDiagram (h : X ⟶ Y) (hh : IsEtale B S hS h.hom) (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 Y.1 h.hom where
  U := U
  V := (smallEtalePostcomp B S hS h hh).obj U
  g := 𝟙 ((SmallEtale.toOver B S hS X.1).obj U)
  comm := (Category.id_comp (U.1.hom ≫ h.hom)).symm.trans
    (congrArg (fun m ↦ m ≫ ((smallEtalePostcomp B S hS h hh).obj U).1.hom)
      (yoneda.map_id ((SmallEtale.toOver B S hS X.1).obj U)).symm)

/-! ### The chart projection against a morphism of modules -/

/-- **A morphism of modules on the source commutes with the chart projection of the direct
image.**  Evaluating a morphism `ψ` of `𝒪_X`-modules on the chart projection of a section of the
direct image is the chart projection of the section pushed forward along `ψ`.

`AlgebraicGeometry.Space.moduleChartProjection` is a natural transformation of functors of
sheaves of *sets*, and this is its naturality at the underlying morphism of sheaves of sets of
`ψ`; the direct images of the two developments have the same underlying sheaf of sets, which is
what lets one chart projection serve both. -/
theorem val_app_moduleChartProjection (f : X ⟶ Y)
    {N N' : Modules.{u, u} B S hS X.1 X.2} (ψ : N ⟶ N')
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj N).val.obj (op d.V)) :
    ψ.val.app (op d.U)
        ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
          (moduleSetSheaf B S hS X N) x)
      = (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
          (moduleSetSheaf B S hS X N')
          (((modulePushforward B S hS f).map ψ).val.app (op d.V) x) :=
  (Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map ψ) x).symm

/-! ### The chart section in the transported spelling of the unit -/

/-- **The chart section is the chart projection of the transported unit.**
`AlgebraicGeometry.Space.modulePullbackChartSection` is built from the untransported unit of the
Stacks 03D7 adjunction for the morphism of small étale ringed topoi; the two spellings of that
unit agree on sections, by
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app`, so the chart section is equally
the chart projection of the value of the unit of
`AlgebraicGeometry.Space.modulePullbackAdjunction`.  That is the spelling in which Stacks 03LW
can be moved onto the adjunction. -/
theorem modulePullbackChartSection_eq_moduleChartProjection (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : G.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f G d s
      = (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
          (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj G))
          (((modulePullbackAdjunction B S hS f).unit.app G).val.app (op d.V) s) :=
  congrArg
    ((moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
      (moduleSetSheaf B S hS X ((modulePullback B S hS f).obj G)))
    (modulePullbackAdjunction_unit_val_app B S hS f G (op d.V) s).symm

/-! ### Stacks 03LW on a chart section -/

variable (h : X ⟶ Y) (hh : IsEtale B S hS h.hom)

/-- **Stacks 03LW on a chart section of the pullback is the chart projection of the unit of
étale restriction.**  Pushing the chart component of the unit of Stacks 03LU across the
identification of the pullback of modules with étale restriction replaces that unit by the unit
of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction`, under the same chart projection.

Nothing about the comparison of Stacks 03LW is computed: the comparison is moved off the section
by the naturality of the chart projection
(`AlgebraicGeometry.Space.val_app_moduleChartProjection`), where it meets the unit of
Stacks 03LU and is absorbed into the étale unit by
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app`. -/
theorem modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection
    (G : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 h.hom)
    (s : G.val.obj (op d.V)) :
    ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app G).val.app (op d.U)
        (modulePullbackChartSection B S hS h G d s)
      = (moduleChartProjection B S hS h d.V (indexOfChartDiagram B S hS h d)).app
          (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G))
          (((etaleModulePullbackAdjunction B S hS h hh).unit.app G).val.app (op d.V) s) := by
  refine Eq.trans (congrArg
    (fun z ↦ ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app G).val.app (op d.U) z)
    (modulePullbackChartSection_eq_moduleChartProjection B S hS h G d s)) ?_
  refine Eq.trans (val_app_moduleChartProjection B S hS h
    ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app G) d
    (((modulePullbackAdjunction B S hS h).unit.app G).val.app (op d.V) s)) ?_
  exact congrArg
    ((moduleChartProjection B S hS h d.V (indexOfChartDiagram B S hS h d)).app
      (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G)))
    (congrArg (fun m : G ⟶ (modulePushforward B S hS h).obj
        ((etaleModulePullback B S hS h hh).obj G) ↦ m.val.app (op d.V) s)
      (etaleModulePullbackAdjunction_unit_app B S hS h hh G).symm)

/-! ### The chart projection of the direct image, in the equivalence-counit form -/

/-- **The chart projection of the direct image of sheaves of sets, read through the
quasi-inverse of the comparison equivalence of Stacks 03G1.**
`AlgebraicGeometry.Space.moduleChartProjection` is restriction of sections along the given
morphism of charts followed by the counit of the *right Kan extension* form
`AlgebraicGeometry.Space.smallEtaleComparisonRan` of that quasi-inverse; this reads it instead
through `asEquivalence.inverse` and the counit of the equivalence, which is the form in which
the unit of the étale restriction adjunction of sheaves of sets is computed
(`AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit`).

The two forms are identified by `AlgebraicGeometry.Space.smallEtaleComparisonRanIso`, which is a
`CategoryTheory.Adjunction.rightAdjointUniq` of the adjunction of the equivalence against the
cocontinuous sheaf adjunction, so the exchange of the two counits is
`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`; the restriction along the morphism
of charts is moved past the comparison by its naturality. -/
theorem moduleChartProjection_app_eq_counitIso (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (Q : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (y : ((smallEtaleDirectImage B S hS f).obj Q).obj.obj (op V)) :
    (moduleChartProjection B S hS f V j).app Q y =
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.counitIso.hom.app Q).hom.app
          j.right
        (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj Q).obj.map
          j.hom y) := by
  have hnat := NatTrans.naturality_apply
    ((smallEtaleComparisonRanIso B S hS X).hom.app Q).hom j.hom y
  have hc := Adjunction.rightAdjointUniq_hom_app_counit
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction
    ((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)) Q
  refine Eq.trans (congrArg (fun z ↦ (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous
      (Type u) (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X)).counit.app Q).hom.app j.right z) hnat.symm) ?_
  exact congrArg (fun m : (smallEtaleComparisonRestriction B S hS X).obj
      ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj Q) ⟶ Q ↦
    m.hom.app j.right
      (((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj Q).obj.map
        j.hom y)) hc

/-! ### The chart projection of the unit of étale restriction of sheaves of sets -/

/-- **The chart projection of the unit of the étale restriction adjunction of sheaves of sets is
restriction of sections along the induced morphism of charts.**  Let `W` be an étale scheme
chart of `Y` and `j` an étale scheme chart of `X` above `X ×_Y W`, and let `ν` be a morphism
`h ∘ j ⟶ W` of charts of `Y` whose comparison is the one `j` induces.  Then the chart projection
at `j` of the unit `P ⟶ h_*(P|_X)` over `W` is `P.map ν`.

This is `AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit` read through
`AlgebraicGeometry.Space.moduleChartProjection_app_eq_counitIso`. -/
theorem moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit
    (h : X ⟶ Y) (hh : IsEtale B S hS h.hom)
    (P : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) (W : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS h W)) (comparisonFunctor B S hS X).op)
    (x : P.obj.obj (op W))
    (nu : (smallEtalePostcomp B S hS h hh).obj j.right.unop ⟶ W)
    (hnu : (comparisonFunctor B S hS Y).map nu =
      (spacesEtalePostcomp B S hS h hh).map j.hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
          ((comparisonFunctor B S hS Y).obj W)) :
    (moduleChartProjection B S hS h W j).app ((smallEtaleSetRestriction B S hS h hh).obj P)
        (((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app P).hom.app (op W) x)
      = P.obj.map nu.op x :=
  (moduleChartProjection_app_eq_counitIso B S hS h W j
      ((smallEtaleSetRestriction B S hS h hh).obj P) _).trans
    (counitIso_hom_app_restrictionAdjunction_unit B S hS h hh P W j x nu hnu)

/-- **The morphism of charts induced by `AlgebraicGeometry.Space.postcompChartDiagram` is an
identity.**  Its underlying morphism of the big fppf site of `S` is the vertical morphism of
that diagram, which is an identity, by
`AlgebraicGeometry.Space.toOver_map_eq_chartBaseChangeMap` and
`AlgebraicGeometry.Space.chartBaseChangeMap_indexOfChartDiagram`; and
`AlgebraicGeometry.Space.SmallEtale.toOver` is faithful. -/
theorem eq_id_of_comparisonFunctor_map_eq_postcompChartDiagram (h : X ⟶ Y)
    (hh : IsEtale B S hS h.hom) (U : SmallEtale B S hS X.1)
    (nu : (smallEtalePostcomp B S hS h hh).obj U ⟶ (smallEtalePostcomp B S hS h hh).obj U)
    (hnu : (comparisonFunctor B S hS Y).map nu =
      (spacesEtalePostcomp B S hS h hh).map
          (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U)).hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
          ((comparisonFunctor B S hS Y).obj ((smallEtalePostcomp B S hS h hh).obj U))) :
    nu = 𝟙 ((smallEtalePostcomp B S hS h hh).obj U) := by
  refine (SmallEtale.toOver B S hS Y.1).map_injective ?_
  refine Eq.trans (toOver_map_eq_chartBaseChangeMap B S hS h hh
    ((smallEtalePostcomp B S hS h hh).obj U)
    (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U)) nu hnu) ?_
  refine Eq.trans (chartBaseChangeMap_indexOfChartDiagram B S hS h
    (postcompChartDiagram B S hS h hh U)) ?_
  exact ((SmallEtale.toOver B S hS Y.1).map_id
    ((smallEtalePostcomp B S hS h hh).obj U)).symm

/-- **Over the chart diagram of a single chart, the chart projection of the unit of the étale
restriction adjunction of sheaves of sets is the identity.**  The sections of `P|_X` over `U`
are the sections of `P` over the composite chart `h ∘ U`, and the chart projection of the unit
recovers the section it started from.

This is
`AlgebraicGeometry.Space.moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit` at the
morphism of charts of `AlgebraicGeometry.Space.postcompChartDiagram`, which
`AlgebraicGeometry.Space.eq_id_of_comparisonFunctor_map_eq_postcompChartDiagram` identifies as
an identity; the morphism itself is supplied by the fullness of the comparison functor of
Stacks 03G1, as in `AlgebraicGeometry.Space.structureSharpSet_eq_unit`. -/
theorem moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit_postcomp (h : X ⟶ Y)
    (hh : IsEtale B S hS h.hom) (P : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (U : SmallEtale B S hS X.1)
    (x : P.obj.obj (op ((smallEtalePostcomp B S hS h hh).obj U))) :
    (moduleChartProjection B S hS h ((smallEtalePostcomp B S hS h hh).obj U)
          (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U))).app
        ((smallEtaleSetRestriction B S hS h hh).obj P)
        (((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app P).hom.app
          (op ((smallEtalePostcomp B S hS h hh).obj U)) x)
      = x := by
  have := comparisonFunctor_full B S hS Y
  obtain ⟨nu, hnu⟩ : ∃ nu : (smallEtalePostcomp B S hS h hh).obj U ⟶
      (smallEtalePostcomp B S hS h hh).obj U,
      (comparisonFunctor B S hS Y).map nu =
        (spacesEtalePostcomp B S hS h hh).map
            (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U)).hom.unop ≫
          (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).counit.app
            ((comparisonFunctor B S hS Y).obj ((smallEtalePostcomp B S hS h hh).obj U)) :=
    ⟨(comparisonFunctor B S hS Y).preimage _, (comparisonFunctor B S hS Y).map_preimage _⟩
  refine Eq.trans (moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit B S hS h hh P
    ((smallEtalePostcomp B S hS h hh).obj U)
    (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U)) x nu hnu) ?_
  refine Eq.trans (congrArg (fun m ↦ P.obj.map (Quiver.Hom.op m) x)
    (eq_id_of_comparisonFunctor_map_eq_postcompChartDiagram B S hS h hh U nu hnu)) ?_
  exact Functor.map_id_apply P.obj _ x


/-! ### The unit of Stacks 03LU through Stacks 03LW, on sections

That the unit of Stacks 03LU read through Stacks 03LW agrees, on sections, with the unit of the
sheaf-of-sets étale restriction adjunction is
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction`; it is not
definitional, and its proof goes through the extension of scalars, whose unit is the identity on
sections only after Stacks 03LV is composed on. -/

/-- The chart projection of the two units, which agree on sections. -/
private theorem moduleChartProjection_etaleModulePullbackAdjunction_unit
    (G : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (s : G.val.obj (op ((smallEtalePostcomp B S hS h hh).obj U))) :
    (moduleChartProjection B S hS h ((smallEtalePostcomp B S hS h hh).obj U)
        (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U))).app
        (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G))
        (((etaleModulePullbackAdjunction B S hS h hh).unit.app G).val.app
          (op ((smallEtalePostcomp B S hS h hh).obj U)) s)
      = (moduleChartProjection B S hS h ((smallEtalePostcomp B S hS h hh).obj U)
            (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U))).app
            (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G))
            (((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
                  (moduleSetSheaf B S hS Y G)).hom.app
              (op ((smallEtalePostcomp B S hS h hh).obj U)) s) :=
  congrArg
    ((moduleChartProjection B S hS h ((smallEtalePostcomp B S hS h hh).obj U)
         (indexOfChartDiagram B S hS h (postcompChartDiagram B S hS h hh U))).app
         (moduleSetSheaf B S hS X ((etaleModulePullback B S hS h hh).obj G)))
    (etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction B S hS h hh G
      (op ((smallEtalePostcomp B S hS h hh).obj U)) s)

/-- **Stacks 03LW sends the chart section over a single chart of the source back to the
section it came from.**  Over `AlgebraicGeometry.Space.postcompChartDiagram` at a chart `U` of
`X` the sections of the étale restriction over `U` are the sections of `G` over the composite
chart `h ∘ U`, and the comparison of Stacks 03LW carries the chart component of the unit of
Stacks 03LU to the identity on them.

The proof composes three steps:
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection` moves
Stacks 03LW onto the adjunction,
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction` replaces
the unit of Stacks 03LU by the unit of the sheaf-of-sets restriction adjunction, and
`AlgebraicGeometry.Space.moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit_postcomp`
evaluates its chart projection. -/
theorem modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection_postcomp
    (G : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1)
    (s : G.val.obj (op ((smallEtalePostcomp B S hS h hh).obj U))) :
    ((modulePullbackIsoEtaleModulePullback B S hS h hh).hom.app G).val.app (op U)
        (modulePullbackChartSection B S hS h G
          (postcompChartDiagram B S hS h hh U) s)
      = s :=
  ((modulePullbackIsoEtaleModulePullback_hom_val_app_chartSection B S hS h hh G
        (postcompChartDiagram B S hS h hh U) s).trans
      (moduleChartProjection_etaleModulePullbackAdjunction_unit B S hS h hh G U s)).trans
    (moduleChartProjection_smallEtaleSetRestrictionAdjunction_unit_postcomp B S hS h hh
      (moduleSetSheaf B S hS Y G) U s)

end AlgebraicGeometry.Space

end
