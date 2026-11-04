module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent

/-!
# The chart restriction of a sheaf of algebras on an algebraic space

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`, let `A` be a sheaf of
commutative `𝒪_X`-algebras on the small étale site of `X`, and let `V` be an étale scheme chart
of `X`.  This file carries `A` to a sheaf of commutative algebras **on the Zariski site of the
chart's scheme**, i.e. to a `Stacks.RelativeSpec.AlgebraSheaf (chartScheme V)`, the input the
scheme-level relative spectrum of Stacks 01LM/01LP takes, and shows that the restriction of a
quasi-coherent algebra is quasi-coherent.

The construction mirrors `AlgebraicGeometry.Space.restrictToChartScheme`, the restriction of an
`𝒪_X`-module to the chart's scheme, but needs none of the module-level comparison machinery.
Both notions of algebra involved are *sheaves of commutative rings over a structure sheaf* —
`AlgebraicGeometry.Space.AlgebraSheaf` is one by
`AlgebraicGeometry.Space.AlgebraSheaf.toUnder` and `Stacks.RelativeSpec.AlgebraSheaf X` is
`CategoryTheory.Under X.sheaf` by definition — so restricting one to the other is restriction of
sheaves of commutative rings along the index functor
`AlgebraicGeometry.Space.openChartFunctor`, which reads a Zariski open of the chart's scheme as
an étale chart of `X`.  That functor is continuous
(`AlgebraicGeometry.Space.isContinuous_openChartFunctor`), so the restriction of a sheaf is a
sheaf and no sheafification is involved; the structure morphism is the one the module-level
restriction already extends scalars along, with commutativity kept rather than forgotten.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeCommRingRestriction`: restriction of sheaves of
  commutative rings from the small étale site of `X` to the Zariski site of a chart's scheme.
* `AlgebraicGeometry.Space.chartSchemeStructureSheafHom`: the structure morphism the restriction
  is taken over, `𝒪_{chartScheme V} ⟶ (𝒪_X)|_{chartScheme V}`.
* `AlgebraicGeometry.Space.chartSchemeAlgebra`: **a sheaf of commutative `𝒪_X`-algebras on the
  small étale site of `X`, restricted to a sheaf of commutative algebras on the Zariski site of
  an étale chart's scheme**, and `AlgebraicGeometry.Space.chartSchemeAlgebraFunctor` the same
  functorially.
* `AlgebraicGeometry.Space.chartSchemeQuasicoherentAlgebra` and
  `AlgebraicGeometry.Space.chartSchemeQuasicoherentAlgebraFunctor`: the restriction read in the
  category of quasi-coherent algebras on the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.chartSchemeAlgebra_sections` and
  `AlgebraicGeometry.Space.chartSchemeAlgebraFunctor_map_app`: the sections of the restriction
  over a Zariski open, and the restricted morphism's component there, are those of `A` over the
  étale chart that open cuts out.
* `AlgebraicGeometry.Space.underlyingModule_chartSchemeAlgebra`: the module underlying the
  restricted algebra is the chart restriction of the module underlying `A`, on the nose.
* `AlgebraicGeometry.Space.isQuasicoherent_chartSchemeAlgebra`: **the chart restriction of a
  quasi-coherent algebra is quasi-coherent.**

## Implementation notes

No `stacks` attribute is carried.  Descent, Proposition 03DX (2) is an *equivalence* between the
quasi-coherent modules on the small Zariski and small étale sites of one *scheme*; what is built
here is the restriction functor, in one direction only, for *algebras*, and between the small
étale site of an algebraic space and the Zariski site of a chart.  It is the algebra-level
counterpart of `AlgebraicGeometry.Space.restrictToChartScheme`, which carries no tag either for
the same reason.

The quasi-coherence statement is where the module-level work is reused rather than redone.
`AlgebraicGeometry.Space.underlyingModule_chartSchemeAlgebra` holds by `rfl`: both sides are the
sections of `A` over the charts cut out by Zariski opens, read as a module over the regular
functions of the chart's scheme through the structure-algebra map, so the restricted algebra's
underlying module *is* the direct image of
`AlgebraicGeometry.Space.chartSchemeRestrictionSheafHom` presented by
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward`.  Quasi-coherence is then
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme` transported along that
isomorphism.

The functor is assembled from `CategoryTheory.Under.post` and `CategoryTheory.Under.map` rather
than written out with an explicit action on morphisms: the restriction of sheaves of commutative
rings is a functor and the structure morphism is a fixed morphism, so functoriality in the
algebra is exactly the composite of those two standard functors on under-categories, and the
compatibility of a morphism of algebras with the two structure-algebra maps is
`AlgebraicGeometry.Space.AlgebraSheaf.toUnder`.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Restriction of sheaves of commutative rings to the Zariski site of a chart -/

/-- Restriction of sheaves of commutative rings from the small étale site of the algebraic space
`X` to the Zariski site of the scheme of an étale chart `V`: the direct image along the
continuous index functor `AlgebraicGeometry.Space.openChartFunctor`, whose sections over a
Zariski open of `chartScheme V` are the sections over the étale chart of `X` that open cuts out.

This is the algebra-level counterpart of the module-level restriction
`AlgebraicGeometry.Space.restrictToChartScheme`; no sheafification occurs, the index functor
being continuous. -/
abbrev chartSchemeCommRingRestriction (V : SmallEtale B S hS X.1) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥(chartScheme V)) CommRingCat.{u} :=
  (openChartFunctor B S hS X.1 V).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology ↥(chartScheme V)) (SmallEtale.topology B S hS X.1)

/-- The structure morphism the chart restriction of algebras is taken over: over a Zariski open
of `chartScheme V` it is pullback of regular functions along the inclusion of that open, read as
an étale chart of `X`.

This is `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` with commutativity kept rather
than forgotten, and `AlgebraicGeometry.Space.chartSchemeRestrictionSheafHom` is its composite
with the forgetful functor to sheaves of rings. -/
def chartSchemeStructureSheafHom (V : SmallEtale B S hS X.1) :
    (chartScheme V).sheaf ⟶
      (chartSchemeCommRingRestriction B S hS X V).obj (structureSheaf B S hS X.1 X.2) :=
  ⟨(Scheme.restrictFunctorΓ (X := chartScheme V)).inv⟩

/-! ### The chart restriction of an algebra sheaf -/

/-- **A sheaf of commutative `𝒪_X`-algebras on the small étale site of an algebraic space
restricts, on each étale scheme chart, to a sheaf of commutative algebras on the Zariski site of
the chart's scheme.**

Its sheaf of commutative rings is the restriction of that of `A`, and its structure morphism is
the structure morphism of the chart followed by the restriction of the structure-algebra map of
`A`.  This is the form the scheme-level relative spectrum of Stacks 01LM/01LP consumes. -/
def chartSchemeAlgebra (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1) :
    Stacks.RelativeSpec.AlgebraSheaf (chartScheme V) :=
  Under.mk (chartSchemeStructureSheafHom B S hS X V ≫
    (chartSchemeCommRingRestriction B S hS X V).map A.hom)

/-- The sheaf of commutative rings underlying the chart restriction of an algebra sheaf is the
restriction of the sheaf of commutative rings underlying it. -/
@[simp]
theorem chartSchemeAlgebra_right (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    (chartSchemeAlgebra B S hS X A V).right =
      (chartSchemeCommRingRestriction B S hS X V).obj A.right :=
  rfl

/-- **The sections of the chart restriction over a Zariski open are the sections of `A` over the
étale chart that open cuts out.**  This is the computation that makes the restriction usable:
nothing is sheafified, so a section of the restricted algebra over a Zariski open `O` of
`chartScheme V` is literally a section of `A` over `AlgebraicGeometry.Space.openChart` at `O`. -/
theorem chartSchemeAlgebra_sections (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (O : (chartScheme V).Opens) :
    (chartSchemeAlgebra B S hS X A V).sections O =
      A.right.obj.obj (op ((openChartFunctor B S hS X.1 V).obj O)) :=
  rfl

/-- The structure morphism of the chart restriction, on sections over a Zariski open: restrict a
regular function on that open to the étale chart it cuts out, then push it into `A`. -/
theorem chartSchemeAlgebra_hom_app (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) (O : (chartScheme V).Opens) :
    (chartSchemeAlgebra B S hS X A V).hom.hom.app (op O) =
      (Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op O) ≫
        A.hom.hom.app (op ((openChartFunctor B S hS X.1 V).obj O)) :=
  rfl

/-- **The chart restriction of an algebra sheaf, functorially in the algebra.**

It is `AlgebraicGeometry.Space.AlgebraSheaf.toUnder` followed by the two standard functors on
under-categories attached to the restriction of sheaves of commutative rings and to the
structure morphism of the chart. -/
def chartSchemeAlgebraFunctor (V : SmallEtale B S hS X.1) :
    AlgebraSheaf.{u, u} B S hS X.1 X.2 ⥤ Stacks.RelativeSpec.AlgebraSheaf (chartScheme V) :=
  AlgebraSheaf.toUnder ⋙ Under.post (chartSchemeCommRingRestriction B S hS X V) ⋙
    Under.map (chartSchemeStructureSheafHom B S hS X V)

/-- `AlgebraicGeometry.Space.chartSchemeAlgebraFunctor` restricts the algebras of
`AlgebraicGeometry.Space.chartSchemeAlgebra`. -/
@[simp]
theorem chartSchemeAlgebraFunctor_obj (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    (chartSchemeAlgebraFunctor B S hS X V).obj A = chartSchemeAlgebra B S hS X A V :=
  rfl

/-- On morphisms the chart restriction of algebras is the restriction of the underlying morphism
of sheaves of commutative rings. -/
@[simp]
theorem chartSchemeAlgebraFunctor_map_right {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    (φ : A ⟶ C) (V : SmallEtale B S hS X.1) :
    ((chartSchemeAlgebraFunctor B S hS X V).map φ).right =
      (chartSchemeCommRingRestriction B S hS X V).map φ.right :=
  rfl

/-- **A morphism of algebra sheaves restricts, on sections over a Zariski open, to its own
component at the étale chart that open cuts out.**

Together with `AlgebraicGeometry.Space.chartSchemeAlgebra_sections` this is the whole content of
the restriction on morphisms: nothing is sheafified, so the restricted morphism *is* the
original one read at the charts coming from Zariski opens. -/
theorem chartSchemeAlgebraFunctor_map_app {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A ⟶ C)
    (V : SmallEtale B S hS X.1) (O : (chartScheme V).Opens) :
    ((chartSchemeAlgebraFunctor B S hS X V).map φ).right.hom.app (op O) =
      φ.right.hom.app (op (openChart B S hS X.1 V O)) :=
  rfl

/-! ### Quasi-coherence of the chart restriction -/

/-- **The module underlying the chart restriction of an algebra sheaf is the chart restriction of
the module underlying it**, in the direct-image presentation
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward` gives the module-level chart
restriction.

Both sides are the sections of `A` over the étale charts cut out by Zariski opens of
`chartScheme V`, read as a module over the regular functions of `chartScheme V` through the
structure-algebra map of `A`, so the equality needs no computation. -/
theorem underlyingModule_chartSchemeAlgebra (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS X.1) :
    (chartSchemeAlgebra B S hS X A V).underlyingModule =
      (SheafOfModules.pushforward.{u}
        (chartSchemeRestrictionSheafHom B S hS X.2 V)).obj A.underlyingModule :=
  rfl

/-- **The chart restriction of a quasi-coherent sheaf of `𝒪_X`-algebras is quasi-coherent** on
the Zariski site of the chart's scheme.

Quasi-coherence of an algebra sheaf is quasi-coherence of its underlying module, and by
`AlgebraicGeometry.Space.underlyingModule_chartSchemeAlgebra` the underlying module of the
restriction is the module-level chart restriction of the underlying module of `A`, which is
quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme`. -/
theorem isQuasicoherent_chartSchemeAlgebra (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) (V : SmallEtale B S hS X.1) :
    (chartSchemeAlgebra B S hS X A V).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (chartScheme V).ringCatSheaf).prop_of_iso
    (restrictToChartSchemeIsoPushforward B S hS X.2 V A.underlyingModule)
    (isQuasicoherent_restrictToChartScheme B S hS X A.underlyingModule hA V)

/-- The chart restriction of a quasi-coherent algebra, read as an object of the category of
quasi-coherent sheaves of commutative algebras on the chart's scheme. -/
def chartSchemeQuasicoherentAlgebra (A : QuasicoherentAlgebra B S hS X)
    (V : SmallEtale B S hS X.1) :
    Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra (chartScheme V) :=
  ⟨chartSchemeAlgebra B S hS X A.obj V,
    isQuasicoherent_chartSchemeAlgebra B S hS X A.obj A.property V⟩

/-- **The chart restriction as a functor from the quasi-coherent `𝒪_X`-algebras to the
quasi-coherent algebras on the chart's scheme.** -/
def chartSchemeQuasicoherentAlgebraFunctor (V : SmallEtale B S hS X.1) :
    QuasicoherentAlgebra B S hS X ⥤
      Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra (chartScheme V) :=
  ObjectProperty.lift _
    (quasicoherentAlgebraInclusion B S hS X ⋙ chartSchemeAlgebraFunctor B S hS X V)
    fun A ↦ isQuasicoherent_chartSchemeAlgebra B S hS X A.obj A.property V

/-- The functor into the quasi-coherent algebras restricts the algebras of
`AlgebraicGeometry.Space.chartSchemeQuasicoherentAlgebra`. -/
@[simp]
theorem chartSchemeQuasicoherentAlgebraFunctor_obj (A : QuasicoherentAlgebra B S hS X)
    (V : SmallEtale B S hS X.1) :
    (chartSchemeQuasicoherentAlgebraFunctor B S hS X V).obj A =
      chartSchemeQuasicoherentAlgebra B S hS X A V :=
  rfl

/-- Forgetting quasi-coherence after restricting to a chart is restricting the underlying algebra
sheaf. -/
theorem chartSchemeQuasicoherentAlgebraFunctor_comp_inclusion (V : SmallEtale B S hS X.1) :
    chartSchemeQuasicoherentAlgebraFunctor B S hS X V ⋙
        ObjectProperty.ι (Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebra
          (chartScheme V)) =
      quasicoherentAlgebraInclusion B S hS X ⋙ chartSchemeAlgebraFunctor B S hS X V :=
  rfl

end AlgebraicGeometry.Space

end
