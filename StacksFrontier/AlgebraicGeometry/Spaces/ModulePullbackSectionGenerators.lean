module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Sections of a module pullback coming from the chartwise transpose

Let `g : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `M` be a sheaf of `𝒪_{X'}`-modules and `N` a sheaf of `𝒪_X`-modules, both on the
small étale sites.  A morphism `u : g^*M ⟶ N` of `𝒪_X`-modules is the same thing, by the
Stacks 03D7 adjunction `g^* ⊣ g_*` followed by the Stacks 03LU chartwise universal property of
the direct image, as a linear map of sections `ξ : M ⟶ N` along `g`; that is how
`AlgebraicGeometry.Space.idealSheafMap` and every other morphism out of a module pullback in
this development is built.

This file relates the two descriptions on sections.  Over a commutative diagram `d` of étale
scheme charts, a section `s` of `M` over the chart of `X'` has a canonical image in `g^*M` over
the chart of `X` — the chart component of the unit of the adjunction — and `u` carries it to
`ξ.app d s`.  So the values of the chartwise transpose are literally values of `u`, and a
section of `N` lying locally in the `𝒪_X`-span of such values lies locally in the image of `u`.
That gives a criterion for `u` to be an epimorphism phrased entirely in terms of `ξ`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackUnitSection` is the section of `g^*M` over the chart
  of `X` of a chart diagram attached to a section of `M` over the chart of `X'`.
* `AlgebraicGeometry.Space.modulePullbackHomFMap` is the chartwise transpose `ξ` of a morphism
  out of a module pullback.
* `AlgebraicGeometry.Space.moduleFMapSpanningSet` is the family of all restrictions of the values
  of a linear map of sections along `g`, as a family of local sections of `N`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackHomFMap_app`: the values of the chartwise transpose
  are the values of `u` on the unit sections.  This is the identification the chartwise
  description was missing.
* `AlgebraicGeometry.Space.mem_range_of_mem_spanSubmodule_moduleFMapSpanningSet`: the span of the
  values of the chartwise transpose over a chart lies in the image of `u` on that chart.
* `AlgebraicGeometry.Space.epi_of_spanSieve_moduleFMapSpanningSet_mem`: if every local section of
  `N` restricts, along a covering sieve, into the span of the values of the chartwise
  transpose, then `u` is an epimorphism.

## Implementation notes

The only available characterisation of a morphism out of a module pullback built by transposing
twice is `AlgebraicGeometry.Space.idealSheafMap_transpose`, which describes it after *both*
transposes and therefore says nothing about its values on sections.  The identification proved
here is what converts that description into a statement about sections: the two inputs are
`CategoryTheory.Adjunction.homEquiv_unit`, which writes the first transpose as the unit followed
by the direct image of `u`, and
`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`, the naturality of the chart component
of the direct image in the module, which moves `u` back out of the chart component.

The spanning family is taken to be all *restrictions* of the values `ξ.app d s`, following
`Stacks.SheafOfModules.spanSubmodule`, so that no equality of charts has to be transported: a
value over the chart of `d` is the restriction of itself along the identity.

The epimorphism criterion is the local-surjectivity criterion
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective` with the image sieve bounded below by
the span sieve; the covering sieve is the hypothesis, and the bound is the inclusion of the span
in the image.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `g^* ⊣ g_*` and the chartwise universal property of the direct image.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH), epimorphisms of
  sheaves of modules are the locally surjective morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (M : Modules.{u, u} B S hS X'.1 X'.2) (N : Modules.{u, u} B S hS X.1 X.2)

/-! ### The unit section of a module pullback on a chart diagram -/

/-- The canonical section of `g^*M` over the chart of `X` of a commutative diagram `d` of étale
scheme charts attached to a section `s` of `M` over the chart of `X'`: the chart component of
the unit of the adjunction `g^* ⊣ g_*` evaluated at `s`. -/
def modulePullbackUnitSection (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : M.val.obj (op d.V)) : ((modulePullback B S hS g).obj M).val.obj (op d.U) :=
  modulePushforwardCounitApp B S hS g ((modulePullback B S hS g).obj M) d
    (((modulePullbackAdjunction B S hS g).unit.app M).val.app (op d.V) s)

/-- The unit section, unfolded.  This is the definition, stated so that it can be rewritten
with rather than unfolded by unification. -/
private theorem modulePullbackUnitSection_eq (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : M.val.obj (op d.V)) :
    modulePullbackUnitSection B S hS g M d s =
      modulePushforwardCounitApp B S hS g ((modulePullback B S hS g).obj M) d
        (((modulePullbackAdjunction B S hS g).unit.app M).val.app (op d.V) s) :=
  rfl

/-! ### The chartwise transpose of a morphism out of a module pullback -/

/-- The linear map of sections along `g` attached to a morphism `u : g^*M ⟶ N` of
`𝒪_X`-modules: the transpose along the Stacks 03D7 adjunction, read through the chartwise
universal property of the direct image of Stacks 03LU. -/
def modulePullbackHomFMap (u : (modulePullback B S hS g).obj M ⟶ N) :
    ModuleFMap B S hS g N M :=
  modulePushforwardHomEquiv B S hS g N M
    ((modulePullbackAdjunction B S hS g).homEquiv M N u)

/-- The chartwise transpose, unfolded: its value is the chart component of the direct image
applied to the first transpose.  This is the definition, stated so that unification with it
happens at the transparency of `exact`. -/
private theorem modulePullbackHomFMap_app_eq (u : (modulePullback B S hS g).obj M ⟶ N)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (s : M.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS g M N u).app d s =
      modulePushforwardCounitApp B S hS g N d
        (((modulePullbackAdjunction B S hS g).homEquiv M N u).val.app (op d.V) s) :=
  rfl

/-- The first transpose of `u` evaluated on a section is the direct image of `u` evaluated on
the unit.  This is `CategoryTheory.Adjunction.homEquiv_unit` read on sections. -/
private theorem homEquiv_val_app_apply (u : (modulePullback B S hS g).obj M ⟶ N)
    (W : (SmallEtale B S hS X'.1)ᵒᵖ) (s : M.val.obj W) :
    ((modulePullbackAdjunction B S hS g).homEquiv M N u).val.app W s =
      ((modulePushforward B S hS g).map u).val.app W
        (((modulePullbackAdjunction B S hS g).unit.app M).val.app W s) :=
  have hψ : (modulePullbackAdjunction B S hS g).homEquiv M N u =
      (modulePullbackAdjunction B S hS g).unit.app M ≫
        (modulePushforward B S hS g).map u :=
    Adjunction.homEquiv_unit (modulePullbackAdjunction B S hS g) M N u
  (congrArg (fun a : M ⟶ (modulePushforward B S hS g).obj N ↦ a.val.app W s) hψ).trans
    (comp_val_app_apply B S hS ((modulePullbackAdjunction B S hS g).unit.app M)
      ((modulePushforward B S hS g).map u) W s)

/-- **The values of the chartwise transpose are values of the morphism.**  On a commutative
diagram of étale scheme charts, the linear map of sections attached to `u : g^*M ⟶ N` sends a
section `s` of `M` to the value of `u` on the unit section of `s`. -/
theorem modulePullbackHomFMap_app (u : (modulePullback B S hS g).obj M ⟶ N)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (s : M.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS g M N u).app d s =
      u.val.app (op d.U) (modulePullbackUnitSection B S hS g M d s) := by
  rw [modulePullbackUnitSection_eq B S hS g M d s]
  refine (modulePullbackHomFMap_app_eq B S hS g M N u d s).trans
    (Eq.trans ?_ (modulePushforwardCounitApp_map B S hS g u d
      (((modulePullbackAdjunction B S hS g).unit.app M).val.app (op d.V) s)))
  exact congrArg (modulePushforwardCounitApp B S hS g N d)
    (homEquiv_val_app_apply B S hS g M N u (op d.V) s)

/-- **A morphism out of an inverse image, evaluated on a unit section, is the chart component of
the direct image evaluated on its adjoint transpose.**  This is
`AlgebraicGeometry.Space.modulePullbackHomFMap_app` read through the definition of the chartwise
transpose, so that a consumer gets both steps at once.

It is stated because the two steps are not interchangeable by unification at a concrete
algebraic space: identifying a component of the chartwise transpose with a chart component of
the direct image means unfolding `AlgebraicGeometry.Space.modulePullbackHomFMap`, and a consumer
that leaves that to `Eq.trans` pays it inside its own elaboration budget. -/
theorem val_app_modulePullbackUnitSection (u : (modulePullback B S hS g).obj M ⟶ N)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (s : M.val.obj (op d.V)) :
    u.val.app (op d.U) (modulePullbackUnitSection B S hS g M d s) =
      modulePushforwardCounitApp B S hS g N d
        (((modulePullbackAdjunction B S hS g).homEquiv M N u).val.app (op d.V) s) :=
  (modulePullbackHomFMap_app B S hS g M N u d s).symm.trans
    (modulePullbackHomFMap_app_eq B S hS g M N u d s)

/-! ### The family of sections spanned by the chartwise transpose -/

/-- The family of local sections of `N` consisting of all restrictions of the values of a
linear map of sections `ξ` along `g`: over a chart `W` of `X`, the sections obtained from a
section of `M` on a chart diagram by applying `ξ` and restricting to `W`. -/
def moduleFMapSpanningSet (ξ : ModuleFMap B S hS g N M)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) : Set (N.val.obj W) :=
  {y | ∃ (d : ChartDiagram B S hS X.1 X'.1 g.hom) (i : W.unop ⟶ d.U)
    (s : M.val.obj (op d.V)), N.val.map i.op (ξ.app d s) = y}

/-- **The span of the values of the chartwise transpose lies in the image of the morphism.**
Over a chart `W` of `X`, every `𝒪_X(W)`-combination of restrictions of values of the chartwise
transpose of `u` is a value of `u` on a section of `g^*M` over `W`. -/
theorem mem_range_of_mem_spanSubmodule_moduleFMapSpanningSet
    (u : (modulePullback B S hS g).obj M ⟶ N) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    {y : N.val.obj W}
    (hy : y ∈ (Stacks.SheafOfModules.spanSubmodule N
      (moduleFMapSpanningSet B S hS g M N (modulePullbackHomFMap B S hS g M N u))).obj W) :
    y ∈ LinearMap.range (u.val.app W).hom := by
  refine Submodule.span_induction ?_ (zero_mem _) (fun _ _ _ _ ha hb ↦ add_mem ha hb)
    (fun r _ _ hz ↦ Submodule.smul_mem _ r hz) hy
  rintro z ⟨Z, j, w, ⟨d, i, s, rfl⟩, rfl⟩
  refine ⟨((modulePullback B S hS g).obj M).val.map (i.op ≫ j)
    (modulePullbackUnitSection B S hS g M d s), ?_⟩
  refine (PresheafOfModules.naturality_apply u.val (i.op ≫ j)
    (modulePullbackUnitSection B S hS g M d s)).trans ?_
  rw [modulePullbackHomFMap_app B S hS g M N u d s,
    PresheafOfModules.map_comp_apply N.val i.op j]
  rfl

/-! ### The epimorphism criterion -/

/-- **A morphism out of a module pullback is an epimorphism as soon as the values of its
chartwise transpose locally span the target.**  If every local section of `N` restricts, along
a covering sieve of the small étale site of `X`, into the span of the restrictions of the values
of the chartwise transpose of `u`, then `u` is an epimorphism.

Epimorphisms of sheaves of modules are the locally surjective morphisms, and the span sieve of
the hypothesis is contained in the image sieve of `u` by
`AlgebraicGeometry.Space.mem_range_of_mem_spanSubmodule_moduleFMapSpanningSet`. -/
theorem epi_of_spanSieve_moduleFMapSpanningSet_mem
    (u : (modulePullback B S hS g).obj M ⟶ N)
    (h : ∀ (W : SmallEtale B S hS X.1) (x : N.val.obj (op W)),
      Stacks.SheafOfModules.spanSieve N
          (moduleFMapSpanningSet B S hS g M N (modulePullbackHomFMap B S hS g M N u)) x ∈
        SmallEtale.topology B S hS X.1 W) :
    Epi u := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective u ⟨fun {W} x ↦ ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (h W x)
  intro V i hi
  obtain ⟨t, ht⟩ := mem_range_of_mem_spanSubmodule_moduleFMapSpanningSet B S hS g M N u (op V) hi
  exact ⟨t, ht⟩

end AlgebraicGeometry.Space

end
