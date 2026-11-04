module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeDirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenInterchange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison

/-!
# The chart restriction of a direct-image algebra is the direct image along the projection

Let `p : Z ⟶ Y` be a *representable* morphism of algebraic spaces over `S` and let `V` be an
étale scheme chart of `Y`.  `AlgebraicGeometry.Space.pushforwardAlgebraChartIso` identifies the
direct-image algebra `p_*𝒪_Z` of Stacks 03G8 with the restriction of `𝒪_Z` along base change of
étale scheme charts, and `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraChartIso`
restricts that identification to the Zariski site of `chartScheme V`, where by
`AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraChartIso_sections` the sections over a
Zariski open `O` are the regular functions on `(openChart V O) ×_Y Z`.  What
`AlgebraicGeometry.Space.chartRelativeSpecLift` consumes, on the other hand, is the *scheme-level*
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra` of the cartesian projection
`q : chartScheme (V ×_Y Z) ⟶ chartScheme V`, whose sections over `O` are the regular functions on
`q^{-1}O`.

This file identifies the two **as sheaves of algebras**:

`chartSchemeDirectImageAlgebra Y (Over.mk p) V ≅ pushforwardAlgebra q`.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardPresheafIso` and
  `AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardRingIso`: the comparison of the
  underlying presheaves, respectively sheaves, of commutative rings on the Zariski site of
  `chartScheme V`.
* `AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardIso`: the comparison as an
  isomorphism of sheaves of algebras.
* `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraPushforwardIso`: **the chart restriction
  of `p_*𝒪_Z` is the direct image of `𝒪_{V ×_Y Z}` along the cartesian projection, as an
  algebra.**

## Main results

* `AlgebraicGeometry.Space.hom_comp_chartBaseChangeAlgebraPushforwardRingIso`: **the comparison
  carries the structure-algebra map of the chart restriction to the comorphism `q.c` of the
  cartesian projection.**  This is the `CategoryTheory.Under` half, which the implementation notes
  of `StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeDirectImageAlgebra` record as the one
  thing the interchange was still missing.

## Implementation notes

**The sheaf-of-rings half is three identifications and no geometry.**  The presheaf underlying
the chart restriction is `(openChartFunctor V ⋙ smallBaseChange p hp).op ⋙ structurePresheaf Z`,
which `AlgebraicGeometry.Space.smallBaseChangeOpenChartFunctorIso` — the interchange of chart base
change with Zariski opens — carries to
`(Opens.map q.base ⋙ openChartFunctor (V ×_Y Z)).op ⋙ structurePresheaf Z`;
`AlgebraicGeometry.Space.openChartFunctor_comp_toScheme`, an *equality* of functors, turns the
second factor into `((chartScheme (V ×_Y Z)).restrictFunctor ⋙ Over.forget _).op ⋙ Scheme.Γ`,
which `AlgebraicGeometry.Scheme.restrictFunctorΓ` identifies with the structure presheaf of
`chartScheme (V ×_Y Z)`; and the direct image along `q` is that presheaf restricted along
`Opens.map q.base`.  The sheaf-level comparison is the presheaf one pulled back along the fully
faithful `CategoryTheory.sheafToPresheaf`.

**The `CategoryTheory.Under` half is one scheme-level lemma.**  Over a Zariski open `O` the
structure-algebra map of the chart restriction is pullback of regular functions along the
cartesian projection of the smaller chart, which
`AlgebraicGeometry.Space.smallBaseChangeOpenChartLeftIso_hom_comp_projection` identifies with
`AlgebraicGeometry.Space.openChartSmallBaseChangeProjection`, whose underlying morphism of schemes
is the restriction `q ∣_ O`; and
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` says exactly that
`q ∣_ O` read through the two restriction comparisons is `q.app O`, which is the comorphism the
scheme-level direct-image algebra carries.

**The final step is written in term mode rather than with `rw`.**
`AlgebraicGeometry.Space.openChart` and `AlgebraicGeometry.Space.smallBaseChange` are semireducible
and the two spellings of the sections over a Zariski open — `Γ(chartScheme (openChart V O))` and
`Γ((chartScheme V).restrictFunctor.obj O)` — are definitionally but not syntactically equal, so a
goal mixing them is not type-correct at reducible transparency and `rw` stops seeing inside it.
`CategoryTheory.Category.assoc` and `congrArg` are applied as terms instead, which needs no such
correctness; the pointwise equalities that *are* stated in one spelling are proved with `rw` as
usual.

**No `stacks` attribute is carried.**  Stacks 03G8 is registered on
`AlgebraicGeometry.Space.structureSharp_comp_chartProjectionSharpDirectImage` and Stacks 03G2
part (4) on `AlgebraicGeometry.Space.smallBaseChange`; the comparison of two readings of the
sections of one direct image over the Zariski opens of a chart is a clause of no tag.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Y : AlgebraicSpaces B S hS} (p : Z ⟶ Y)
    (hp : yoneda.relativelyRepresentable p.hom) (V : SmallEtale B S hS Y.1)

/-- **The comparison of the two readings of the sections, as presheaves of commutative rings on
the Zariski site of the chart's scheme.**  The sections of the chart restriction of `p_*𝒪_Z` over
a Zariski open `O` of `chartScheme V` are the regular functions on `(openChart V O) ×_Y Z`, and
the sections of the direct image along the cartesian projection `q` are the regular functions on
`q^{-1}O`; the interchange of chart base change with Zariski opens identifies the two.

It is `AlgebraicGeometry.Space.smallBaseChangeOpenChartFunctorIso` read through global regular
functions, followed by `AlgebraicGeometry.Scheme.restrictFunctorΓ`; see the implementation
notes. -/
def chartBaseChangeAlgebraPushforwardPresheafIso :
    (chartSchemeAlgebra B S hS Y (chartBaseChangeAlgebra B S hS p hp) V).right.obj ≅
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V)).right.obj :=
  Functor.isoWhiskerRight (NatIso.op (smallBaseChangeOpenChartFunctorIso B S hS p hp V)).symm
      (structurePresheaf B S hS Z.1) ≪≫
    Functor.isoWhiskerLeft
      (Opens.map (smallBaseChangeSchemeProjection B S hS p hp V).base).op
      (Scheme.restrictFunctorΓ (X := chartScheme ((smallBaseChange B S hS p hp).obj V)))

/-- **The comparison, as sheaves of commutative rings.**  The presheaf comparison pulled back
along the fully faithful `CategoryTheory.sheafToPresheaf`. -/
def chartBaseChangeAlgebraPushforwardRingIso :
    (chartSchemeAlgebra B S hS Y (chartBaseChangeAlgebra B S hS p hp) V).right ≅
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V)).right :=
  (fullyFaithfulSheafToPresheaf _ CommRingCat.{u}).preimageIso
    (chartBaseChangeAlgebraPushforwardPresheafIso B S hS p hp V)

/-- **The comparison carries the structure-algebra map of the chart restriction to the comorphism
of the cartesian projection.**  This is the `CategoryTheory.Under` half of the comparison, and
with it the identification is one of sheaves of *algebras* rather than only of sheaves of rings.

Over a Zariski open `O` the structure-algebra map of the chart restriction is pullback of regular
functions along the cartesian projection of the chart that `O` cuts out, which
`AlgebraicGeometry.Space.smallBaseChangeOpenChartLeftIso_hom_comp_projection` identifies with the
restriction `q ∣_ O` of the projection; and
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` reads that as
`q.app O`. -/
theorem hom_comp_chartBaseChangeAlgebraPushforwardRingIso :
    (chartSchemeAlgebra B S hS Y (chartBaseChangeAlgebra B S hS p hp) V).hom ≫
        (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V).hom =
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V)).hom := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun O => ?_))
  have h1 : (SmallEtale.toOver B S hS Z.1).map
        (smallBaseChangeOpenChartIso B S hS p hp V O.unop).hom =
      (smallBaseChangeOpenChartLeftIso B S hS p hp V O.unop).hom := rfl
  have hproj : (SmallEtale.toOver B S hS Z.1).map
          (smallBaseChangeOpenChartIso B S hS p hp V O.unop).inv ≫
        (smallBaseChangeProjection B S hS p hp).app (openChart B S hS Y.1 V O.unop) =
      openChartSmallBaseChangeProjection B S hS p hp V O.unop := by
    rw [← smallBaseChangeOpenChartLeftIso_hom_comp_projection, ← h1, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hmid : (smallBaseChangeSharpCommRingCat B S hS p hp).hom.app
          (op ((openChartFunctor B S hS Y.1 V).obj O.unop)) ≫
        (structurePresheaf B S hS Z.1).map
          (smallBaseChangeOpenChartIso B S hS p hp V O.unop).inv.op =
      Scheme.Γ.map (smallBaseChangeSchemeProjection B S hS p hp V ∣_ O.unop).op := by
    refine Eq.trans ?_ (congrArg
      (fun m => Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op) hproj)
    rw [Functor.map_comp, op_comp, Functor.map_comp]
    rfl
  refine (congrArg (fun m => (Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app O ≫ m)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫
      (Scheme.restrictFunctorΓ
          (X := chartScheme ((smallBaseChange B S hS p hp).obj V))).hom.app
        (op (smallBaseChangeSchemeProjection B S hS p hp V ⁻¹ᵁ O.unop))) hmid))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫
      (Scheme.restrictFunctorΓ
          (X := chartScheme ((smallBaseChange B S hS p hp).obj V))).hom.app
        (op (smallBaseChangeSchemeProjection B S hS p hp V ⁻¹ᵁ O.unop)))
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict
      (smallBaseChangeSchemeProjection B S hS p hp V) O.unop)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun m => (smallBaseChangeSchemeProjection B S hS p hp V).app O.unop ≫ m)
    (Iso.inv_hom_id_app
      (Scheme.restrictFunctorΓ (X := chartScheme ((smallBaseChange B S hS p hp).obj V)))
      (op (smallBaseChangeSchemeProjection B S hS p hp V ⁻¹ᵁ O.unop)))).trans
    (Category.comp_id _))

/-- **The chart restriction of the restricted structure sheaf is the direct image along the
cartesian projection, as a sheaf of algebras.** -/
def chartBaseChangeAlgebraPushforwardIso :
    chartSchemeAlgebra B S hS Y (chartBaseChangeAlgebra B S hS p hp) V ≅
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V) :=
  Under.isoMk (chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V)
    (hom_comp_chartBaseChangeAlgebraPushforwardRingIso B S hS p hp V)

/-- **The chart restriction of the direct-image algebra of a representable morphism is the
direct image along the cartesian projection of charts, as a sheaf of algebras on the Zariski site
of the chart's scheme.**

For a representable `p : Z ⟶ Y` and an étale scheme chart `V` of `Y` the restriction of `p_*𝒪_Z`
to the Zariski site of `chartScheme V` is `q_* 𝒪_{chartScheme (V ×_Y Z)}` for the cartesian
projection `q`.  This is the shape `AlgebraicGeometry.Space.chartRelativeSpecLift` consumes, so
with it a map of algebras into a chart restriction of a direct image becomes a morphism of schemes
into the relative spectrum over the chart.

It is `AlgebraicGeometry.Space.chartSchemeDirectImageAlgebraChartIso` — Stacks 03G8 for a
representable morphism, restricted to the chart — followed by
`AlgebraicGeometry.Space.chartBaseChangeAlgebraPushforwardIso`. -/
def chartSchemeDirectImageAlgebraPushforwardIso :
    chartSchemeDirectImageAlgebra B S hS Y (Over.mk p) V ≅
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
        (smallBaseChangeSchemeProjection B S hS p hp V) :=
  chartSchemeDirectImageAlgebraChartIso B S hS p hp V ≪≫
    chartBaseChangeAlgebraPushforwardIso B S hS p hp V

end AlgebraicGeometry.Space

end
