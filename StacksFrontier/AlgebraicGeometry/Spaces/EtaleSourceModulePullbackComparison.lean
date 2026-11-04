module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnit

/-!
# The comparison of a pullback along a composite with an étale first factor

Let `pU : X' ⟶ X` be an **étale** morphism of algebraic spaces over a scheme `S` of a big fppf
site `B`, let `f : X ⟶ Y` be arbitrary and let `k = pU ≫ f`.  For an `𝒪_Y`-module `M` there is a
canonical morphism

`k^*M ⟶ (f^*M)|_{X'}`

of `𝒪_{X'}`-modules, the restriction on the right being
`AlgebraicGeometry.Space.etaleModulePullback`: its chartwise transpose is the chart component of
the unit of the Stacks 03D7 adjunction at `f`, read on the chart diagrams over `k` whose chart of
`X'` has been postcomposed with `pU`.  This is the **mixed** form of the compatibility of
Stacks 03LU with Stacks 03LW — one factor étale, the other arbitrary — and it is constructed here
with no reference to either comparison.

The use made of it is to **remove the square** from the blocker of the chart bijectivity of
Stacks 083K.  For a diagram `d` of affine étale charts over `f`, the chart-space square of `d`
has étale verticals `p_U : chartSpace X d.U ⟶ X` and `p_V : chartSpace Y d.V ⟶ Y`, and
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_comparison` reduces
the bijectivity of the canonical base-change comparison at `(f, d)` to the bijectivity of one
component of the comparison
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison` of that square.  This file factors
that comparison as

`Θ_square = Θ_target ≫ Θ_source`

with `Θ_target = AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison`, which is an
**isomorphism** (`AlgebraicGeometry.Space.isIso_modulePullbackEtaleTargetComparison`), and
`Θ_source` the mixed comparison of this file.  So what the chart bijectivity of Stacks 083K needs
is exactly that the mixed comparison be bijective on the sections over one chart; the square, its
upper-left morphism and the relative representability of its right vertical are all discharged.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.postcompSource`: a chart diagram over `k`, with its chart
  of `X'` postcomposed with the étale `pU`, is a chart diagram over `f`.
* `AlgebraicGeometry.Space.modulePullbackEtaleSourceFMap`: the chart sections of `f`, read as a
  linear map of sections along `k`.
* `AlgebraicGeometry.Space.modulePullbackEtaleSourceComparison`: **the mixed comparison**
  `k^*M ⟶ (f^*M)|_{X'}`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackEtaleSourceComparison_chartSection`: **the defining
  property** — the comparison carries the chart section of `k` at a diagram `e` to the chart
  section of `f` at the diagram with the chart of `X'` postcomposed with `pU`.
* `AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_eq`: **the factorization.**  The
  comparison of a commuting square with étale verticals is the comparison of its étale target
  followed by the mixed comparison of its étale source.
* `AlgebraicGeometry.Space.bijective_modulePullbackEtaleSquareComparison_val_app_iff`: so the two
  are bijective on the same sections.
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_etaleSource`:
  **the chart bijectivity of Stacks 083K, reduced to the mixed comparison alone.**
* `AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence`: the two equations between
  sections over a chart which make the mixed comparison the comparison of Stacks 03LU followed
  by the identification of Stacks 03LW, hence an isomorphism
  (`AlgebraicGeometry.Space.isIso_modulePullbackEtaleSourceComparison_of_coherence`).
* `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_coherence`: **the chart
  bijectivity of Stacks 083K holds for every diagram of affine étale charts as soon as those two
  equations do**, with no presentation hypothesis.

## What is not proved

**That the mixed comparison is an isomorphism.**  All three bijections that would compose to the
statement are already in the development:

* `AlgebraicGeometry.Space.modulePullbackFMapEquiv` at `k`, identifying `k^*M ⟶ N` with
  `AlgebraicGeometry.Space.ModuleFMap` along `k` from `N` to `M`;
* the hom-set bijection of the adjunction between étale restriction along `pU` and the direct
  image, identifying `(f^*M)|_{X'} ⟶ N` with `f^*M ⟶ p_{U*}N`, and
  `AlgebraicGeometry.Space.modulePullbackFMapEquiv` at `f` again, identifying that with a linear
  map of sections along `f` from `p_{U*}N` to `M`;
* `AlgebraicGeometry.Space.modulePushforwardCounitCompEquiv`, which is exactly the bijection
  between those two kinds of linear map of sections.

What was missing is that the composite of the three *is* composition with the mixed comparison,
and that is one statement: the **chart formula** for
`AlgebraicGeometry.Space.ModuleFMap.comp`, i.e. that composition with the counit of the direct
image along `pU` sends a linear map of sections along `f` to the one along `k` whose value at `e`
is the counit at the identity-vertical diagram applied to the value at
`AlgebraicGeometry.Space.ChartDiagram.postcompSource`.  **It is now proved**, and so is the
conclusion: `AlgebraicGeometry.Space.ModuleFMap.compOfIso_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleFMapCompChartFormula.lean` is the chart formula
relative to a comparison of direct images,
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean` is the one
hypothesis it carries, and
`AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSourceModuleFMapCompDischarge.lean` puts the two
together — unconditionally, giving
`AlgebraicGeometry.Space.isIso_modulePullbackEtaleSourceComparison` and
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`, the
chart bijectivity of Stacks 083K with no coherence hypothesis at all.  As this section predicted,
`AlgebraicGeometry.Space.FMap.comp_app` applies at *every* chart diagram over `k`, because `pU`
is étale and so every such diagram factors through an étale chart of `X` — namely the
postcomposition of its own chart of `X'`.

**So the hypotheses below are superseded, and what is still open about them is narrow.**  This
file also records a second route, `AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence`:
the mixed comparison is the inverse of the comparison of Stacks 03LU followed by the
identification of Stacks 03LW as soon as *two* equations between sections over a chart hold.
Nothing constructs that structure, and nothing needs to any more — the route above reaches the
same conclusion, and `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence` replaced
the pair by a single hypothesis that mentions neither Stacks 03LW nor the comparison of inverse
images.  Of the two fields:

* `comp` is Stacks 03LU carrying a chart section of a chart section to the chart section of the
  composite.  That statement **is** proved, at arbitrary `f` and `g` and with no étaleness, as
  `AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection` in
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackCompIsoChartSection.lean`; it is stated
  there at a composed chart diagram `AlgebraicGeometry.Space.ChartDiagram.comp`, where this field
  wants the identity-vertical diagram of `e.U` over the source-postcomposed diagram of `e`, so
  what separates the two is the transport of chart diagrams along
  `AlgebraicGeometry.Space.ChartDiagram.ext` and not the comparison.
* `restrict` is the Stacks 03LW half, and its input is
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`.

The first still does not suffice on its own, for the reason recorded: the target of the mixed
comparison is étale restriction, so the passage from `p_U^*` to `p_U^*_{ét}` has to be described
on the very same sections, which is the second.

## Implementation notes

The comparison is stated for a morphism `k` together with an equality `pU ≫ f = k` rather than
for `pU ≫ f` itself.  That is what lets the factorization below be an equation between morphisms
out of `a^*(M|_{Y'})` with no `eqToHom` anywhere: the square supplies `a ≫ p_V = p_U ≫ f`, so the
mixed comparison is taken at `k = a ≫ p_V`, which is the target of
`AlgebraicGeometry.Space.modulePullbackEtaleTargetComparison` on the nose.

`AlgebraicGeometry.Space.ChartDiagram.postcompSource` is reducible, for the reason recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleTargetModuleFMapRestriction.lean`: a statement
mentioning the vertical morphism of a constructed chart diagram is type-correct at `implicit`
transparency only once the chart it is built from is seen through.

The one definitional identification the factorization needs — that postcomposing the chart of
`X'` of a target-postcomposed diagram is postcomposing both charts — is isolated as
`AlgebraicGeometry.Space.ChartDiagram.postcompSource_postcompTarget`, a lemma of its own.  A
chain of such identifications inside one term exhausts the heartbeat budget; one at a time they
are immediate.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

section Source

variable {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y)
    (hU : IsEtale B S hS pU.hom) (k : X' ⟶ Y) (hk : pU ≫ f = k)
    (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **A chart diagram over `k = p_U ≫ f`, with its chart of `X'` postcomposed with the étale
`p_U`, is a chart diagram over `f`.**

Postcomposition `AlgebraicGeometry.Space.smallEtalePostcomp` leaves the underlying object of the
big fppf site of a chart unchanged, so the vertical scheme morphism and the chart of `Y` are
carried over unchanged, and the commutation is the commutation of the given diagram with the
composite read through `hk`. -/
@[reducible] def ChartDiagram.postcompSource (e : ChartDiagram B S hS X'.1 Y.1 k.hom) :
    ChartDiagram B S hS X.1 Y.1 f.hom where
  U := (smallEtalePostcomp B S hS pU hU).obj e.U
  V := e.V
  g := e.g
  comm := by
    subst hk
    change (e.U.1.hom ≫ pU.hom) ≫ f.hom = yoneda.map e.g ≫ e.V.1.hom
    exact (Category.assoc _ _ _).trans e.comm

/-- **The chart sections of `f`, read as a linear map of sections along `k`.**  The sections of
`(f^*M)|_{X'}` over a chart of `X'` are the sections of `f^*M` over the postcomposed chart of
`X`, so the chart component `AlgebraicGeometry.Space.modulePullbackChartFMap` of the unit of
Stacks 03D7 at the source-postcomposed diagram is a map of sections of the shape a linear map of
sections along `k` demands, and its four fields are the four fields of that chart component.

The pullback of regular functions along a chart diagram depends only on its vertical morphism,
which `AlgebraicGeometry.Space.ChartDiagram.postcompSource` does not change, so the
semilinearity field needs no transport. -/
noncomputable def modulePullbackEtaleSourceFMap :
    ModuleFMap B S hS k
      ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M)) M where
  app e := (modulePullbackChartFMap B S hS f M).app
    (ChartDiagram.postcompSource B S hS pU f hU k hk e)
  naturality e e' i j h s := (modulePullbackChartFMap B S hS f M).naturality
    (ChartDiagram.postcompSource B S hS pU f hU k hk e)
    (ChartDiagram.postcompSource B S hS pU f hU k hk e')
    ((smallEtalePostcomp B S hS pU hU).map i) j h s
  map_add e := (modulePullbackChartFMap B S hS f M).map_add
    (ChartDiagram.postcompSource B S hS pU f hU k hk e)
  map_smul e := (modulePullbackChartFMap B S hS f M).map_smul
    (ChartDiagram.postcompSource B S hS pU f hU k hk e)

/-- The values of that linear map of sections are the chart sections of `f` at the
source-postcomposed chart diagrams. -/
theorem modulePullbackEtaleSourceFMap_app (e : ChartDiagram B S hS X'.1 Y.1 k.hom)
    (s : M.val.obj (op e.V)) :
    (modulePullbackEtaleSourceFMap B S hS pU f hU k hk M).app e s =
      modulePullbackChartSection B S hS f M
        (ChartDiagram.postcompSource B S hS pU f hU k hk e) s :=
  modulePullbackChartFMap_app B S hS f M
    (ChartDiagram.postcompSource B S hS pU f hU k hk e) s

/-- **The comparison of a pullback along a composite with an étale first factor**: the morphism

`k^*M ⟶ (f^*M)|_{X'}`

of `𝒪_{X'}`-modules whose chartwise transpose is
`AlgebraicGeometry.Space.modulePullbackEtaleSourceFMap`, that is, the morphism which carries the
chart section of `k` to the chart section of `f`.

It is defined by the chartwise universal property of the pullback of modules alone, so nothing
about the comparisons of Stacks 03LU or 03LW enters its construction; whether it is an
isomorphism is the statement this file does not prove. -/
noncomputable def modulePullbackEtaleSourceComparison :
    (modulePullback B S hS k).obj M ⟶
      (etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M) :=
  (modulePullbackFMapEquiv B S hS k
      ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M)) M).symm
    (modulePullbackEtaleSourceFMap B S hS pU f hU k hk M)

/-- The chartwise transpose of the mixed comparison is the linear map of sections it was built
from. -/
theorem modulePullbackHomFMap_modulePullbackEtaleSourceComparison :
    modulePullbackHomFMap B S hS k M
        ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
        (modulePullbackEtaleSourceComparison B S hS pU f hU k hk M) =
      modulePullbackEtaleSourceFMap B S hS pU f hU k hk M :=
  (modulePullbackFMapEquiv B S hS k _ _).apply_symm_apply _

/-- The value of a morphism out of a pullback of modules on a chart section is the value of its
chartwise transpose. -/
private theorem modulePullback_hom_val_app_chartSection {X'' Y'' : AlgebraicSpaces B S hS}
    (g : X'' ⟶ Y'') (M' : Modules.{u, u} B S hS Y''.1 Y''.2)
    (N : Modules.{u, u} B S hS X''.1 X''.2) (u : (modulePullback B S hS g).obj M' ⟶ N)
    (e : ChartDiagram B S hS X''.1 Y''.1 g.hom) (s : M'.val.obj (op e.V)) :
    u.val.app (op e.U) (modulePullbackChartSection B S hS g M' e s) =
      (modulePullbackHomFMap B S hS g M' N u).app e s :=
  (congrArg (fun w ↦ u.val.app (op e.U) w)
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M' e s).symm).trans
    (modulePullbackHomFMap_app B S hS g M' N u e s).symm

/-- **The defining property of the mixed comparison: it carries the chart section of `k` to the
chart section of `f`.**

The values of the chartwise transpose of a morphism out of a pullback are its values on the
chart sections (`AlgebraicGeometry.Space.modulePullbackHomFMap_app`, through
`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection`), and the
chartwise transpose of the mixed comparison is the chart section of `f` at the
source-postcomposed diagram. -/
theorem modulePullbackEtaleSourceComparison_chartSection
    (e : ChartDiagram B S hS X'.1 Y.1 k.hom) (s : M.val.obj (op e.V)) :
    (modulePullbackEtaleSourceComparison B S hS pU f hU k hk M).val.app (op e.U)
        (modulePullbackChartSection B S hS k M e s) =
      modulePullbackChartSection B S hS f M
        (ChartDiagram.postcompSource B S hS pU f hU k hk e) s := by
  refine (modulePullback_hom_val_app_chartSection B S hS k _ _ _ e s).trans ?_
  refine Eq.trans (congrArg (fun ξ ↦ ModuleFMap.app ξ e s)
    (modulePullbackHomFMap_modulePullbackEtaleSourceComparison B S hS pU f hU k hk M)) ?_
  exact modulePullbackEtaleSourceFMap_app B S hS pU f hU k hk M e s

end Source

/-! ### The two coherences that make the mixed comparison an isomorphism -/

section Coherence

variable {X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (f : X ⟶ Y)
    (hU : IsEtale B S hS pU.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **The chart diagram over an étale `p_U` with identity vertical morphism at a chart `W` of
`X'`**: the chart `W` of `X'` above its own postcomposition, which is a chart of `X`.

This is the diagram at which the chart section of `p_U^*` is the canonical image of a section of
a module on `X` over the composite chart. -/
@[reducible] def ChartDiagram.etaleUnit (W : SmallEtale B S hS X'.1) :
    ChartDiagram B S hS X'.1 X.1 pU.hom where
  U := W
  V := (smallEtalePostcomp B S hS pU hU).obj W
  g := 𝟙 _
  comm := by
    change W.1.hom ≫ pU.hom =
      yoneda.map (𝟙 ((SmallEtale.toOver B S hS X'.1).obj W)) ≫ W.1.hom ≫ pU.hom
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The two coherences of the comparisons of Stacks 03LU and Stacks 03LW with the chart
component of the unit of Stacks 03D7, in the mixed form.**

Both are equations between sections over a chart.  **This structure is superseded and nothing
constructs it**: `AlgebraicGeometry.Space.ModuleFMapEtaleSourceCompCorrespondence` replaced the
pair by a single hypothesis, and that hypothesis is proved unconditionally by
`AlgebraicGeometry.Space.moduleFMapEtaleSourceCompCorrespondence`, so the conclusions reached
below from it are reached without it.  The first field's general form is proved —
`AlgebraicGeometry.Space.modulePullbackCompIso_hom_val_app_modulePullbackUnitSection`, at a
composed chart diagram — and the second field's input is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`.  The analogous pair for
*iterated étale restriction*,
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`, is also
proved, by `AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction`.  What this structure
adds is that these two, and nothing else, make the mixed comparison of this file an isomorphism,
hence the chart bijectivity of Stacks 083K hold.

Granted the first alone, nothing follows: the target of the mixed comparison is étale
restriction, which is what makes the comparison of a square land where
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_postcomp` needs it, so the
passage from `p_U^*` to `p_U^*_{ét}` has to be described on the very same sections, and that is
the second. -/
structure ModulePullbackEtaleSourceCoherence : Prop where
  /-- **The comparison of Stacks 03LU carries a chart section of a chart section to the chart
  section of the composite.**  The chart section of `p_U^*` at the identity-vertical diagram of
  `e.U`, applied to the chart section of `f^*` at the source-postcomposed diagram of `e`, is
  carried to the chart section of `(p_U ≫ f)^*` at `e`.

  **This field is the composite coherence of
  `AlgebraicGeometry.Space.modulePullbackChartSection` specialized, and not a second
  statement.**  That coherence says, for `f' : X ⟶ Y` and `g' : Y ⟶ Z` and a chart diagram over
  `f'` and one over `g'` sharing their middle chart, that the comparison of Stacks 03LU carries
  the chart section of `f'^*` of the chart section of `g'^*` to the chart section of
  `(f' ≫ g')^*` at the composed chart diagram.  At `f' = p_U` and `g' = f` the two chart
  diagrams are `AlgebraicGeometry.Space.ChartDiagram.etaleUnit` at `e.U` and
  `AlgebraicGeometry.Space.ChartDiagram.postcompSource` of `e`, whose composite is `e` up to the
  one identity `𝟙 _ ≫ e.g = e.g` of vertical morphisms; `AlgebraicGeometry.Space.ChartDiagram.ext`
  transports along it.  So this field holds as soon as that coherence does, and the two must not
  be proved separately: what the general coherence still needs is isolated as
  `AlgebraicGeometry.Space.ModulePushforwardChartComponentCompResidue`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackChartSectionCoherence.lean`), whose
  docstring records both halves.  The field is kept here, rather than replaced by that
  residue, because the step from the residue to the general coherence is not proved; once it
  is, this field follows from it. -/
  comp : ∀ (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)),
    ((modulePullbackCompIso B S hS pU f).hom.app M).val.app (op e.U)
        (modulePullbackChartSection B S hS pU ((modulePullback B S hS f).obj M)
          (ChartDiagram.etaleUnit B S hS pU hU e.U)
          (modulePullbackChartSection B S hS f M
            (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s)) =
      modulePullbackChartSection B S hS (pU ≫ f) M e s
  /-- **The identification of Stacks 03LW carries the chart section at the identity-vertical
  diagram back to the section it came from.**  In the notation of
  `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect` this says
  `etaleSect p_U (chartSection p_U N (etaleUnit W) t) = t`. -/
  restrict : ∀ (W : SmallEtale B S hS X'.1)
      (t : ((modulePullback B S hS f).obj M).val.obj
        (op ((smallEtalePostcomp B S hS pU hU).obj W))),
    ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app
          ((modulePullback B S hS f).obj M)).val.app (op W)
        (modulePullbackChartSection B S hS pU ((modulePullback B S hS f).obj M)
          (ChartDiagram.etaleUnit B S hS pU hU W) t) = t

/-! ### The second coherence, proved

The `restrict` field above holds for every étale `p_U`, with no representability assumed.  The
proof runs through the identification of the unit of étale restriction of `𝒪`-modules with the
unit of étale restriction of sheaves of *sets*
(`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction`), after
which nothing of the module structure is left and the statement is the index-general chart
formula for the set-level unit
(`AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit`) at the one index whose
chart morphism is the identity. -/

/-- The chart projection of a direct image of sheaves of sets, read through the counit of the
comparison equivalence of Stacks 03G1 rather than through the right Kan extension.  This is
`AlgebraicGeometry.Space.moduleChartProjection_app` followed by
`AlgebraicGeometry.Space.ranChartCone_π_ranIso_hom`, and it is the spelling in which the chart
formula for the unit of étale restriction of sheaves of sets is stated.  Neither étaleness nor
representability enters. -/
private theorem moduleChartProjection_app_counitIso_hom (V : SmallEtale B S hS X.1)
    (j : StructuredArrow (op (chartBaseChange B S hS pU V)) (comparisonFunctor B S hS X').op)
    (P : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (x : ((smallEtaleDirectImage B S hS pU).obj P).obj.obj (op V)) :
    (moduleChartProjection B S hS pU V j).app P x =
      ((smallEtaleComparisonRestriction B S hS X').asEquivalence.counitIso.hom.app P).hom.app
          j.right
        (((smallEtaleComparisonRestriction B S hS X').asEquivalence.inverse.obj P).obj.map
          j.hom x) :=
  (moduleChartProjection_app B S hS pU V j P x).trans
    (ranChartCone_π_ranIso_hom B S hS X' P (chartBaseChange B S hS pU V) j x)

/-- **At the identity-vertical diagram the chart morphism of the adjunction of small étale sites
is the identity.**  The morphism `ν` of the small étale site of `X` whose comparison is the
chart morphism of the index of `AlgebraicGeometry.Space.ChartDiagram.etaleUnit` is forced to be
`𝟙`: its image under `AlgebraicGeometry.Space.SmallEtale.toOver` is the vertical morphism of
that diagram, which is the identity by construction, and a morphism of étale charts is
determined by its underlying morphism of the big fppf site. -/
private theorem eq_id_of_etaleUnit_index (W : SmallEtale B S hS X'.1)
    (nu : (smallEtalePostcomp B S hS pU hU).obj
        (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W)).right.unop ⟶
      (smallEtalePostcomp B S hS pU hU).obj W)
    (hnu : (comparisonFunctor B S hS X).map nu =
      (spacesEtalePostcomp B S hS pU hU).map
          (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W)).hom.unop ≫
        (spacesEtalePostcompBaseChangeAdjunction B S hS pU hU).counit.app
          ((comparisonFunctor B S hS X).obj ((smallEtalePostcomp B S hS pU hU).obj W))) :
    nu = 𝟙 ((smallEtalePostcomp B S hS pU hU).obj W) :=
  have h : (SmallEtale.toOver B S hS X.1).map nu =
      𝟙 ((SmallEtale.toOver B S hS X'.1).obj W) :=
    (toOver_map_eq_chartBaseChangeMap B S hS pU hU
        ((smallEtalePostcomp B S hS pU hU).obj W)
        (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W)) nu hnu).trans
      (chartBaseChangeMap_indexOfChartDiagram B S hS pU
        (ChartDiagram.etaleUnit B S hS pU hU W))
  postcompLeft_injective B S hS pU hU W ((smallEtalePostcomp B S hS pU hU).obj W)
    (h.trans ((SmallEtale.toOver B S hS X.1).map_id
      ((smallEtalePostcomp B S hS pU hU).obj W)).symm)

/-- **The chart projection at the identity-vertical diagram of the unit of étale restriction of
sheaves of sets is the identity.**  This is the whole content of the second coherence, with no
module structure left in it: the index-general chart formula
`AlgebraicGeometry.Space.counitIso_hom_app_restrictionAdjunction_unit` gives restriction of
sections along a morphism `ν` of charts, and at this index `ν = 𝟙`.

The morphism `ν` exists because the comparison functor of Stacks 03G1 is full
(`AlgebraicGeometry.Space.comparisonFunctor_full`). -/
theorem moduleChartProjection_etaleUnit_setRestrictionAdjunction_unit
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (W : SmallEtale B S hS X'.1)
    (t : P.obj.obj (op ((smallEtalePostcomp B S hS pU hU).obj W))) :
    (moduleChartProjection B S hS pU ((smallEtalePostcomp B S hS pU hU).obj W)
          (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W))).app
        ((smallEtaleSetRestriction B S hS pU hU).obj P)
      (((smallEtaleSetRestrictionAdjunction B S hS pU hU).unit.app P).hom.app
        (op ((smallEtalePostcomp B S hS pU hU).obj W)) t) = t := by
  have hfull := comparisonFunctor_full B S hS X
  obtain ⟨nu, hnu⟩ : ∃ nu : (smallEtalePostcomp B S hS pU hU).obj
        (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W)).right.unop ⟶
      (smallEtalePostcomp B S hS pU hU).obj W,
      (comparisonFunctor B S hS X).map nu =
        (spacesEtalePostcomp B S hS pU hU).map
            (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W)).hom.unop ≫
          (spacesEtalePostcompBaseChangeAdjunction B S hS pU hU).counit.app
            ((comparisonFunctor B S hS X).obj ((smallEtalePostcomp B S hS pU hU).obj W)) :=
    ⟨(comparisonFunctor B S hS X).preimage _, (comparisonFunctor B S hS X).map_preimage _⟩
  refine Eq.trans (moduleChartProjection_app_counitIso_hom B S hS pU
    ((smallEtalePostcomp B S hS pU hU).obj W)
    (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W))
    ((smallEtaleSetRestriction B S hS pU hU).obj P) _) ?_
  refine Eq.trans (counitIso_hom_app_restrictionAdjunction_unit B S hS pU hU
    P ((smallEtalePostcomp B S hS pU hU).obj W)
    (indexOfChartDiagram B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W)) t nu hnu) ?_
  refine Eq.trans (congrArg
    (fun m ↦ P.obj.map (Quiver.Hom.op m) t)
    (eq_id_of_etaleUnit_index B S hS pU hU W nu hnu)) ?_
  exact congrArg (fun k ↦ k t)
    (P.obj.map_id (op ((smallEtalePostcomp B S hS pU hU).obj W)))

/-- The previous theorem at the underlying sheaf of sets of a module, with the projection in its
module spelling.  This is a declaration of its own only so that the identification of
`AlgebraicGeometry.Space.moduleSetSheaf` of an étale restriction with the étale restriction of
`moduleSetSheaf` is spent once; a declaration that also crosses the unit exhausts the heartbeat
budget at `whnf`. -/
private theorem modulePushforwardCounitApp_etaleUnit_setRestrictionAdjunction_unit
    (N : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS X'.1)
    (t : N.val.obj (op ((smallEtalePostcomp B S hS pU hU).obj W))) :
    modulePushforwardCounitApp B S hS pU
        ((etaleModulePullback.{u, u} B S hS pU hU).obj N)
        (ChartDiagram.etaleUnit B S hS pU hU W)
        (((smallEtaleSetRestrictionAdjunction B S hS pU hU).unit.app
            (moduleSetSheaf B S hS X N)).hom.app
          (op ((smallEtalePostcomp B S hS pU hU).obj W)) t) = t :=
  moduleChartProjection_etaleUnit_setRestrictionAdjunction_unit B S hS pU hU
    (moduleSetSheaf B S hS X N) W t

/-- **The chart projection at the identity-vertical diagram of the unit of étale restriction of
`𝒪`-modules is the identity.**  The unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is, on sections, the unit of étale
restriction of sheaves of sets, and for that the previous theorem applies. -/
theorem modulePushforwardCounitApp_etaleUnit_unit
    (N : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS X'.1)
    (t : N.val.obj (op ((smallEtalePostcomp B S hS pU hU).obj W))) :
    modulePushforwardCounitApp B S hS pU
        ((etaleModulePullback.{u, u} B S hS pU hU).obj N)
        (ChartDiagram.etaleUnit B S hS pU hU W)
        (((etaleModulePullbackAdjunction B S hS pU hU).unit.app N).val.app
          (op ((smallEtalePostcomp B S hS pU hU).obj W)) t) = t :=
  (congrArg
      (fun y ↦ modulePushforwardCounitApp B S hS pU
        ((etaleModulePullback.{u, u} B S hS pU hU).obj N)
        (ChartDiagram.etaleUnit B S hS pU hU W) y)
      (etaleModulePullbackAdjunction_unit_val_app_eq_setRestriction B S hS pU hU N
        (op ((smallEtalePostcomp B S hS pU hU).obj W)) t)).trans
    (modulePushforwardCounitApp_etaleUnit_setRestrictionAdjunction_unit B S hS pU hU N W t)

/-- **The comparison of Stacks 03LW carries the chart section at the identity-vertical diagram
back to the section it came from.**  This is the `restrict` field of
`AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence`, stated for an arbitrary
`𝒪_X`-module and proved for every étale `p_U`.

The chart section is the chart projection of the unit of Stacks 03D7
(`AlgebraicGeometry.Space.modulePullbackUnitSection_eq_modulePullbackChartSection`), and the
comparison of Stacks 03LW moves across that projection by its naturality in the module
(`AlgebraicGeometry.Space.modulePushforwardCounitApp_map`); the unit of Stacks 03D7 followed by
the direct image of the comparison is the unit of the transported adjunction
(`CategoryTheory.Adjunction.ofNatIsoLeft_unit_app`).  What is left is
`AlgebraicGeometry.Space.modulePushforwardCounitApp_etaleUnit_unit`. -/
theorem modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit
    (N : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS X'.1)
    (t : N.val.obj (op ((smallEtalePostcomp B S hS pU hU).obj W))) :
    ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N).val.app (op W)
        (modulePullbackChartSection B S hS pU N
          (ChartDiagram.etaleUnit B S hS pU hU W) t) = t :=
  have hbridge : ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N).val.app (op W)
        (modulePullbackChartSection B S hS pU N
          (ChartDiagram.etaleUnit B S hS pU hU W) t) =
      ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N).val.app (op W)
        (modulePullbackUnitSection B S hS pU N
          (ChartDiagram.etaleUnit B S hS pU hU W) t) :=
    congrArg
      (fun x ↦ ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N).val.app (op W) x)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS pU N
        (ChartDiagram.etaleUnit B S hS pU hU W) t).symm
  have hdef : modulePullbackUnitSection B S hS pU N
        (ChartDiagram.etaleUnit B S hS pU hU W) t =
      modulePushforwardCounitApp B S hS pU ((modulePullback B S hS pU).obj N)
        (ChartDiagram.etaleUnit B S hS pU hU W)
        (((modulePullbackAdjunction B S hS pU).unit.app N).val.app
          (op ((smallEtalePostcomp B S hS pU hU).obj W)) t) :=
    rfl
  have hunit : ((etaleModulePullbackAdjunction B S hS pU hU).unit.app N).val.app
        (op ((smallEtalePostcomp B S hS pU hU).obj W)) t =
      ((modulePushforward B S hS pU).map
          ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N)).val.app
        (op ((smallEtalePostcomp B S hS pU hU).obj W))
        (((modulePullbackAdjunction B S hS pU).unit.app N).val.app
          (op ((smallEtalePostcomp B S hS pU hU).obj W)) t) :=
    (congrArg
        (fun m : N ⟶ (modulePushforward B S hS pU).obj
            ((etaleModulePullback.{u, u} B S hS pU hU).obj N) ↦
          m.val.app (op ((smallEtalePostcomp B S hS pU hU).obj W)) t)
        (Adjunction.ofNatIsoLeft_unit_app (modulePullbackAdjunction B S hS pU)
          (modulePullbackIsoEtaleModulePullback B S hS pU hU) N)).trans
      (comp_val_app_apply B S hS ((modulePullbackAdjunction B S hS pU).unit.app N)
        ((modulePushforward B S hS pU).map
          ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N))
        (op ((smallEtalePostcomp B S hS pU hU).obj W)) t)
  hbridge.trans ((congrArg
      (fun x ↦ ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N).val.app (op W) x)
      hdef).trans
    ((modulePushforwardCounitApp_map B S hS pU
        ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app N)
        (ChartDiagram.etaleUnit B S hS pU hU W)
        (((modulePullbackAdjunction B S hS pU).unit.app N).val.app
          (op ((smallEtalePostcomp B S hS pU hU).obj W)) t)).symm.trans
      ((congrArg
        (fun y ↦ modulePushforwardCounitApp B S hS pU
          ((etaleModulePullback.{u, u} B S hS pU hU).obj N)
          (ChartDiagram.etaleUnit B S hS pU hU W) y) hunit.symm).trans
        (modulePushforwardCounitApp_etaleUnit_unit B S hS pU hU N W t))))

/-- **The second coherence is automatic: only the first has to be supplied.**  The `restrict`
field holds for every étale `p_U` by
`modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit`,
so a consumer of `AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` need only produce
the comparison of Stacks 03LU on chart sections. -/
theorem ModulePullbackEtaleSourceCoherence.of_comp
    (hcomp : ∀ (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)),
      ((modulePullbackCompIso B S hS pU f).hom.app M).val.app (op e.U)
          (modulePullbackChartSection B S hS pU ((modulePullback B S hS f).obj M)
            (ChartDiagram.etaleUnit B S hS pU hU e.U)
            (modulePullbackChartSection B S hS f M
              (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s)) =
        modulePullbackChartSection B S hS (pU ≫ f) M e s) :
    ModulePullbackEtaleSourceCoherence B S hS pU f hU M where
  comp := hcomp
  restrict W t :=
    modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit B S hS pU hU
      ((modulePullback B S hS f).obj M) W t

/-- A natural isomorphism of functors of modules, read on sections, undoes itself. -/
private theorem natIso_inv_hom_apply {C D : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS C.1 C.2 ⥤ Modules.{u, u} B S hS D.1 D.2} (e : F ≅ G)
    (N : Modules.{u, u} B S hS C.1 C.2) (W : SmallEtale B S hS D.1)
    (m : (F.obj N).val.obj (op W)) :
    (e.inv.app N).val.app (op W) ((e.hom.app N).val.app (op W) m) = m :=
  CategoryTheory.congr_fun
    (congrArg (fun t : F.obj N ⟶ F.obj N ↦ t.val.app (op W)) (e.hom_inv_id_app N)) m

/-- The first coherence, read through the inverse of the comparison of Stacks 03LU. -/
private theorem modulePullbackCompIso_inv_chartSection
    (hco : ModulePullbackEtaleSourceCoherence B S hS pU f hU M)
    (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)) :
    ((modulePullbackCompIso B S hS pU f).inv.app M).val.app (op e.U)
        (modulePullbackChartSection B S hS (pU ≫ f) M e s) =
      modulePullbackChartSection B S hS pU ((modulePullback B S hS f).obj M)
        (ChartDiagram.etaleUnit B S hS pU hU e.U)
        (modulePullbackChartSection B S hS f M
          (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s) := by
  refine Eq.trans (congrArg
    (fun w ↦ ((modulePullbackCompIso B S hS pU f).inv.app M).val.app (op e.U) w)
    (hco.comp e s).symm) ?_
  exact natIso_inv_hom_apply B S hS (modulePullbackCompIso B S hS pU f) M e.U _

/-- **Two morphisms out of a pullback of modules which agree on the chart sections are equal.**
The chartwise transpose is injective and its values are the values on the chart sections. -/
private theorem modulePullback_hom_ext_chartSection {X'' Y'' : AlgebraicSpaces B S hS}
    (g : X'' ⟶ Y'') (M' : Modules.{u, u} B S hS Y''.1 Y''.2)
    (N : Modules.{u, u} B S hS X''.1 X''.2)
    (u v : (modulePullback B S hS g).obj M' ⟶ N)
    (h : ∀ (e : ChartDiagram B S hS X''.1 Y''.1 g.hom) (s : M'.val.obj (op e.V)),
      u.val.app (op e.U) (modulePullbackChartSection B S hS g M' e s) =
        v.val.app (op e.U) (modulePullbackChartSection B S hS g M' e s)) :
    u = v := by
  refine (modulePullbackFMapEquiv B S hS g N M').injective ?_
  refine ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_)
  exact (modulePullback_hom_val_app_chartSection B S hS g M' N u e s).symm.trans
    ((h e s).trans (modulePullback_hom_val_app_chartSection B S hS g M' N v e s))

/-- **The value of a composite on a chart section, in two named steps.**  Stated for variable
factors so that the two concrete morphisms are matched first-order against it; applying
`AlgebraicGeometry.Space.comp_val_app_apply` to them directly exhausts the recursion depth, the
middle module having to be unified through the composite of the two pullback functors. -/
private theorem comp_chartSection_eq {X'' Y'' : AlgebraicSpaces B S hS} (g : X'' ⟶ Y'')
    (M' : Modules.{u, u} B S hS Y''.1 Y''.2)
    {N P : Modules.{u, u} B S hS X''.1 X''.2} (u : (modulePullback B S hS g).obj M' ⟶ N)
    (v : N ⟶ P) (e : ChartDiagram B S hS X''.1 Y''.1 g.hom) (s : M'.val.obj (op e.V))
    (y : N.val.obj (op e.U)) (z : P.val.obj (op e.U))
    (hu : u.val.app (op e.U) (modulePullbackChartSection B S hS g M' e s) = y)
    (hv : v.val.app (op e.U) y = z) :
    (u ≫ v).val.app (op e.U) (modulePullbackChartSection B S hS g M' e s) = z :=
  (comp_val_app_apply B S hS u v (op e.U)
      (modulePullbackChartSection B S hS g M' e s)).trans
    ((congrArg (fun w ↦ v.val.app (op e.U) w) hu).trans hv)

/-- Granted the two coherences, the inverse of the comparison of Stacks 03LU followed by the
identification of Stacks 03LW carries the chart section of `p_U ≫ f` to the chart section of
`f` — which is the defining property of the mixed comparison. -/
private theorem modulePullbackCompIso_inv_comp_etale_chartSection
    (hco : ModulePullbackEtaleSourceCoherence B S hS pU f hU M)
    (e : ChartDiagram B S hS X'.1 Y.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)) :
    ((modulePullbackCompIso B S hS pU f).inv.app M ≫
          (modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app
            ((modulePullback B S hS f).obj M)).val.app (op e.U)
        (modulePullbackChartSection B S hS (pU ≫ f) M e s) =
      modulePullbackChartSection B S hS f M
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s :=
  comp_chartSection_eq B S hS (pU ≫ f) M
    ((modulePullbackCompIso B S hS pU f).inv.app M)
    ((modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app
      ((modulePullback B S hS f).obj M)) e s _ _
    (modulePullbackCompIso_inv_chartSection B S hS pU f hU M hco e s)
    (hco.restrict e.U (modulePullbackChartSection B S hS f M
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s))

/-- **Granted the two coherences, the mixed comparison is the inverse of the comparison of
Stacks 03LU followed by the identification of Stacks 03LW.**

Both sides are morphisms out of the pullback `(p_U ≫ f)^*M`, so by
`AlgebraicGeometry.Space.modulePullback_hom_ext_chartSection` it is enough that they agree on the
chart sections; the left-hand side carries the chart section of `p_U ≫ f` to the chart section of
`f` by construction, and the right-hand side does so by the two coherences in turn. -/
theorem modulePullbackEtaleSourceComparison_eq_of_coherence
    (hco : ModulePullbackEtaleSourceCoherence B S hS pU f hU M) :
    modulePullbackEtaleSourceComparison B S hS pU f hU (pU ≫ f) rfl M =
      (modulePullbackCompIso B S hS pU f).inv.app M ≫
        (modulePullbackIsoEtaleModulePullback B S hS pU hU).hom.app
          ((modulePullback B S hS f).obj M) :=
  modulePullback_hom_ext_chartSection B S hS (pU ≫ f) M
    ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M)) _ _
    fun e s ↦ (modulePullbackEtaleSourceComparison_chartSection B S hS pU f hU (pU ≫ f) rfl
      M e s).trans
      (modulePullbackCompIso_inv_comp_etale_chartSection B S hS pU f hU M hco e s).symm
/-- **Granted the two coherences, the mixed comparison is an isomorphism.** -/
theorem isIso_modulePullbackEtaleSourceComparison_of_coherence (k : X' ⟶ Y)
    (hk : pU ≫ f = k) (hco : ModulePullbackEtaleSourceCoherence B S hS pU f hU M) :
    IsIso (modulePullbackEtaleSourceComparison B S hS pU f hU k hk M) := by
  subst hk
  rw [modulePullbackEtaleSourceComparison_eq_of_coherence B S hS pU f hU M hco]
  infer_instance

/-- **Granted the two coherences, the mixed comparison is bijective on the sections over every
chart.** -/
theorem bijective_modulePullbackEtaleSourceComparison_val_app_of_coherence (k : X' ⟶ Y)
    (hk : pU ≫ f = k) (hco : ModulePullbackEtaleSourceCoherence B S hS pU f hU M)
    (W : SmallEtale B S hS X'.1) :
    Function.Bijective
      ((modulePullbackEtaleSourceComparison B S hS pU f hU k hk M).val.app (op W)) :=
  have := isIso_modulePullbackEtaleSourceComparison_of_coherence B S hS pU f hU M k hk hco
  SheafOfModules.bijective_iso_hom_val_app
    (asIso (modulePullbackEtaleSourceComparison B S hS pU f hU k hk M)) (op W)

end Coherence

/-! ### The factorization of the comparison of a square with étale verticals -/

section Square

variable {X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (a : X' ⟶ Y') (pU : X' ⟶ X)
    (pV : Y' ⟶ Y) (hU : IsEtale B S hS pU.hom) (hV : IsEtale B S hS pV.hom)
    (hsq : a ≫ pV = pU ≫ f) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **Postcomposing the chart of `X'` of a target-postcomposed diagram postcomposes both
charts.**  Both sides have `AlgebraicGeometry.Space.smallEtalePostcomp` of the chart of `X'` as
their chart of `X`, that of the chart of `Y'` as their chart of `Y`, and the vertical morphism of
the given diagram.

This is the one definitional identification the factorization below needs, isolated so that it is
performed once. -/
theorem ChartDiagram.postcompSource_postcompTarget
    (e : ChartDiagram B S hS X'.1 Y'.1 a.hom) :
    ChartDiagram.postcompSource B S hS pU f hU (a ≫ pV) hsq.symm
        (e.postcompTarget B S hS a pV hV) =
      ChartDiagram.postcomp B S hS f a pU pV hU hV hsq e :=
  rfl

/-- **The comparison of a commuting square with étale verticals is the comparison of its étale
target followed by the mixed comparison of its étale source.**

Both sides are morphisms out of the pullback `a^*(M|_{Y'})`, so it is enough to compare their
chartwise transposes.  That of the left-hand side is the chart sections of `f` at the
postcomposed diagrams, by construction; that of the right-hand side is the restriction
`AlgebraicGeometry.Space.moduleFMapEtaleRestrict` of the chart sections of `f` at the
source-postcomposed diagrams over `a ≫ p_V`
(`AlgebraicGeometry.Space.modulePullbackFMapEquiv_comp_modulePullbackEtaleTargetComparison`), and
the two agree because postcomposing one chart and then the other postcomposes both. -/
theorem modulePullbackEtaleSquareComparison_eq :
    modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M =
      modulePullbackEtaleTargetComparison B S hS a pV hV M ≫
        modulePullbackEtaleSourceComparison B S hS pU f hU (a ≫ pV) hsq.symm M := by
  refine (modulePullbackFMapEquiv B S hS a
    ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
    ((etaleModulePullback B S hS pV hV).obj M)).injective ?_
  refine Eq.trans
    (modulePullbackHomFMap_modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M) ?_
  refine Eq.trans ?_ (modulePullbackFMapEquiv_comp_modulePullbackEtaleTargetComparison
    B S hS a pV hV M
    ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M))
    (modulePullbackEtaleSourceComparison B S hS pU f hU (a ≫ pV) hsq.symm M)).symm
  refine Eq.trans ?_ (congrArg (moduleFMapEtaleRestrict B S hS a pV hV
    ((etaleModulePullback B S hS pU hU).obj ((modulePullback B S hS f).obj M)) M)
    (modulePullbackHomFMap_modulePullbackEtaleSourceComparison
      B S hS pU f hU (a ≫ pV) hsq.symm M).symm)
  refine ModuleFMap.ext B S hS (funext fun e ↦ funext fun s ↦ ?_)
  rfl

include hV in
/-- **The comparison of the square and the mixed comparison of its étale source are bijective on
the same sections.**  The comparison of the étale target is an isomorphism, so it is bijective on
the sections over every chart, and the factorization identifies the one map with the other
composed with it. -/
theorem bijective_modulePullbackEtaleSquareComparison_val_app_iff
    (hrep : yoneda.relativelyRepresentable pV.hom) (W : SmallEtale B S hS X'.1) :
    Function.Bijective
        ((modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app (op W)) ↔
      Function.Bijective
        ((modulePullbackEtaleSourceComparison B S hS pU f hU (a ≫ pV) hsq.symm M).val.app
          (op W)) := by
  have htarget := bijective_modulePullbackEtaleTargetComparison_val_app B S hS a pV hV hrep M W
  have hfac : ∀ x : ((modulePullback B S hS a).obj
        ((etaleModulePullback B S hS pV hV).obj M)).val.obj (op W),
      (modulePullbackEtaleSquareComparison B S hS f a pU pV hU hV hsq M).val.app (op W) x =
        (modulePullbackEtaleSourceComparison B S hS pU f hU (a ≫ pV) hsq.symm M).val.app
          (op W) ((modulePullbackEtaleTargetComparison B S hS a pV hV M).val.app (op W) x) :=
    fun x ↦ congrArg (fun m ↦ m.val.app (op W) x)
      (modulePullbackEtaleSquareComparison_eq B S hS f a pU pV hU hV hsq M)
  exact (iff_of_eq (congrArg Function.Bijective (funext hfac))).trans
    (Function.Bijective.of_comp_iff _ htarget)

end Square

/-! ### The chart bijectivity of Stacks 083K, reduced to the mixed comparison -/

/-- **The canonical base-change comparison at a quasi-coherent module over a diagram of affine
étale charts is bijective as soon as the mixed comparison of the structure morphism of its chart
of `X` with `f` is bijective on the sections over the identity chart.**

This is
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_comparison` with
the comparison of the chart-space square replaced, by
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_eq`, by the mixed comparison of
this file.  No presentation of `M` is assumed, and neither the upper-left morphism of the square
nor the relative representability of its right vertical appears in the hypothesis: the latter
holds because `AlgebraicGeometry.Space.chartToSpace` is relatively representable over an
algebraic space, and the former is absorbed into the morphism the mixed comparison is taken
at. -/
theorem bijective_modulePullbackChartBaseChange_of_bijective_etaleSource (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (hcomp : Function.Bijective
      ((modulePullbackEtaleSourceComparison B S hS (chartToSpace B S hS X d.U) f
        (isEtale_chartToSpace B S hS X d.U)
        (chartSpaceMapOver B S hS d.g ≫ chartToSpace B S hS Y d.V)
        (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm).symm M).val.app
        (op (chartSpaceIdChartDiagram B S hS f d).U))) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Bijective (modulePullbackChartBaseChange B S hS f M d) :=
  bijective_modulePullbackChartBaseChange_of_bijective_comparison B S hS f M hM d hU hV
    ((bijective_modulePullbackEtaleSquareComparison_val_app_iff B S hS f
      (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
      (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M
      (Functor.relativelyRepresentable.of_diag Y.2.diagonal_representable
        (chartToSpace B S hS Y d.V).hom)
      (chartSpaceIdChartDiagram B S hS f d).U).2 hcomp)

/-- **The chart bijectivity of Stacks 083K, for every diagram of affine étale charts, granted the
two coherences.**

This is the whole of what the chart bijectivity still needs, stated as compactly as the
development can state it: for a quasi-coherent `M` and a diagram `d` of affine étale charts over
`f`, the canonical base-change comparison
`AlgebraicGeometry.Space.modulePullbackChartBaseChange B S hS f M d` is bijective as soon as the
two equations of `AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence` hold for the
structure morphism of `d.U` and `f`.  No presentation of `M` is assumed, no square appears, and
the only unproved input is a pair of equations between sections over a chart. -/
theorem bijective_modulePullbackChartBaseChange_of_coherence (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (hco : ModulePullbackEtaleSourceCoherence B S hS (chartToSpace B S hS X d.U) f
      (isEtale_chartToSpace B S hS X d.U) M) :
    letI := chartDiagramAlgebra B S hS f d
    Function.Bijective (modulePullbackChartBaseChange B S hS f M d) :=
  bijective_modulePullbackChartBaseChange_of_bijective_etaleSource B S hS f M hM d hU hV
    (bijective_modulePullbackEtaleSourceComparison_val_app_of_coherence B S hS
      (chartToSpace B S hS X d.U) f (isEtale_chartToSpace B S hS X d.U) M
      (chartSpaceMapOver B S hS d.g ≫ chartToSpace B S hS Y d.V)
      (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm).symm hco
      (chartSpaceIdChartDiagram B S hS f d).U)

end AlgebraicGeometry.Space

end
