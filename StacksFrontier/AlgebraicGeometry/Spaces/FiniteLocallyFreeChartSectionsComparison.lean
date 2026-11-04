module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# The chart comparison of Stacks 03ZU, on sections over an affine chart

Let `f : X ⟶ Y` be a *representable* morphism of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and let `V` be an étale scheme chart of `Y`.  Stacks 03ZU compares two
readings of finite local freeness of `f`: the definition of Stacks 03ZV, which asks that
`f_*𝒪_X` be a finite locally free module on the small étale site of `Y`, and condition (1) of
Stacks 03ZW, which asks that every represented base change of `f` be a finite locally free
morphism of schemes.  What separates them is a comparison *at a chart*, carried in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentable` and in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankEtaleLocal` as the named hypothesis
`hcross`.

This file proves that comparison **on sections over an affine chart**, with no hypothesis beyond
affineness of the chart: the sections of `f_*𝒪_X` over an affine étale chart `V` of `Y` form a
finite locally free module of rank `r` over the regular functions on `V` exactly when the base
change `V ×_Y X ⟶ V` — a morphism of *schemes*, because `f` is representable — is a finite
locally free morphism of rank `r`.

Both inputs are already in the tree, and the comparison is their composite.  On the side of
algebraic spaces, `AlgebraicGeometry.Space.modulePushforwardChartIso` identifies the direct
image of Stacks 03LU along a representable morphism with the concrete direct image taken along
base change of étale scheme charts, whose sections over `V` are by construction the sections
over `V ×_Y X`; on the side of schemes,
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine` reads finite local freeness
of a morphism to an affine scheme on global sections.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeBaseChangeProjection` is the cartesian projection
  `V ×_Y X ⟶ V` as a morphism of schemes.
* `AlgebraicGeometry.Space.pushforwardStructureModuleChartLinearEquiv`: **the sections of
  `f_*𝒪_X` over an étale chart `V` of `Y` are the regular functions on `V ×_Y X`**, linearly
  over the regular functions on `V`.

## Main results

* `AlgebraicGeometry.Space.module_isFiniteLocallyFreeOfRank_sections_iff_chartBaseChange`: the
  sections condition transported across that linear equivalence.
* `AlgebraicGeometry.Space.module_isFiniteLocallyFreeOfRank_sections_iff`: **the chart
  comparison of Stacks 03ZU on sections over an affine chart.**
* `AlgebraicGeometry.Space.module_isFiniteLocallyFreeOfRank_sections_of_presheaf`: condition (1)
  of Stacks 03ZW, with a fixed rank, gives the sections condition at *every* affine chart.

## Implementation notes

The scalar action is the one the two sides already carry, and no transport of it is needed.  The
sections of `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` of the unit module over a
chart `V` are the regular functions on `V ×_Y X` *on the nose*, with the action of the regular
functions on `V` given by multiplication after pullback along the cartesian projection, also on
the nose; so the `Algebra` instance that
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine` asks for is
`RingHom.toAlgebra` of the pullback map, and its compatibility hypothesis holds by `rfl`.  The
only comparison that is not definitional is
`AlgebraicGeometry.Space.modulePushforwardChartIso` itself, which is applied through
`CategoryTheory.Functor.mapIso` of the evaluation of the underlying presheaf of modules at `V`.

Affineness of the base change is *not* an extra hypothesis of
`AlgebraicGeometry.Space.module_isFiniteLocallyFreeOfRank_sections_of_presheaf`: it is part of
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, which extends `AlgebraicGeometry.IsAffineHom`.  It
is a hypothesis of the biconditional, because the sections condition alone does not bound the
morphism — the same phenomenon that the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison` record with
`𝐏¹_k` over `Spec k`.

Only the rank form is proved.  The unranked form would need the companion of
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine` at an arbitrary affine
target, and the tree has the unranked criterion only for a target which is literally a spectrum
(`Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget`), in terms of finiteness, flatness and
finite presentation rather than of the module of global sections.

*What Stacks 03ZU still owes, after this file.*  The chart comparison `hcross` is stated for the
restriction of `f_*𝒪_X` to the slice of the small étale site of `Y` at `V`, not for its sections
over `V`.  Passing between them is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_freeRankPresieve`, the rank form of
Descent, Proposition 03DX (2), which reads the rank clause of Stacks 0409 as the sections
condition over a covering family of affine charts; its forward direction
(`AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`) is
unconditional, and its converse needs the direct image to be cartesian on affine charts, that is
Stacks 03M9 for `f_*𝒪_X`.  What remains beyond that is to promote the sections condition from a
*covering family* of affine charts of `Y` to one surjective étale chart, which is descent of
finite local freeness along a covering family of affine étale charts — the fpqc locality of
Tag 02VO, available in the tree as
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc` but only granted the fpqc
locality of affineness, Tag 02L5.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The sections of the direct image over a chart -/

/-- The direct image of the structure sheaf of `X` taken along base change of étale scheme
charts: the `𝒪_Y`-module whose sections over a chart `V` of `Y` are, on the nose, the regular
functions on the base-changed chart `V ×_Y X`.

It is `AlgebraicGeometry.Space.pushforwardStructureModule` by
`AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
noncomputable abbrev chartBaseChangeStructureModule (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) : Modules.{u, u} B S hS Y.1 Y.2 :=
  (smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- The cartesian projection `V ×_Y X ⟶ V` of Stacks 03G2, part (4), as a morphism of schemes.
This is the represented base change of `f` along the chart `V`, and it is the morphism of which
condition (1) of Stacks 03ZW asserts finite local freeness. -/
noncomputable abbrev chartSchemeBaseChangeProjection (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    chartScheme ((smallBaseChange B S hS f hf).obj V) ⟶ chartScheme V :=
  (BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)

/-- **The sections of `f_*𝒪_X` over an étale chart of `Y` are the regular functions on the
base-changed chart.**  For a representable `f : X ⟶ Y` and an étale scheme chart `V` of `Y`, the
sections of the direct image of Stacks 03LU over `V` are the global regular functions on
`V ×_Y X`, linearly over the regular functions on `V`.

This is `AlgebraicGeometry.Space.modulePushforwardChartIso` evaluated at the unit module and at
`V`; the target is `AlgebraicGeometry.Space.chartBaseChangeStructureModule`, whose sections are
those regular functions definitionally. -/
noncomputable def pushforwardStructureModuleChartLinearEquiv (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    ((pushforwardStructureModule B S hS f).val.obj (op V)) ≃ₗ[chartRing B S hS Y.1 Y.2 V]
      ((chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :=
  ((SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj
        (op V)).mapIso
      ((modulePushforwardChartIso B S hS f hf).app _)).toLinearEquiv

/-- The scalar action on the sections of
`AlgebraicGeometry.Space.chartBaseChangeStructureModule` over a chart `V` is multiplication
after pullback of regular functions along the cartesian projection. -/
theorem chartBaseChangeStructureModule_smul (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (a : chartRing B S hS Y.1 Y.2 V)
    (x : (chartBaseChangeStructureModule B S hS f hf).val.obj (op V)) :
    a • x =
      (show chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj V) from
          (chartSchemeBaseChangeProjection B S hS f hf V).appTop.hom a) *
        (show chartRing B S hS X.1 X.2 ((smallBaseChange B S hS f hf).obj V) from x) :=
  rfl

/-! ### The chart comparison on sections -/

/-- The sections condition of the rank clause of Stacks 03ZV at a chart `V`, read on the regular
functions of the base-changed chart through
`AlgebraicGeometry.Space.pushforwardStructureModuleChartLinearEquiv`. -/
theorem module_isFiniteLocallyFreeOfRank_sections_iff_chartBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) (r : ℕ) :
    letI := ((chartSchemeBaseChangeProjection B S hS f hf V).appTop).hom.toAlgebra
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS Y.1 Y.2 V)
        ((pushforwardStructureModule B S hS f).val.obj (op V)) r ↔
      Module.IsFiniteLocallyFreeOfRank (Γ(chartScheme V, ⊤) : Type u)
        (Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), ⊤) : Type u) r := by
  let := ((chartSchemeBaseChangeProjection B S hS f hf V).appTop).hom.toAlgebra
  exact ⟨fun h => Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
      (pushforwardStructureModuleChartLinearEquiv B S hS f hf V) h,
    fun h => Module.IsFiniteLocallyFreeOfRank.of_linearEquiv
      (pushforwardStructureModuleChartLinearEquiv B S hS f hf V).symm h⟩

/-- **The chart comparison of Stacks 03ZU, on sections over an affine chart.**  For a
representable morphism `f : X ⟶ Y` of algebraic spaces over `S` and an *affine* étale scheme
chart `V` of `Y` over which the base change of `f` is affine, the sections of `f_*𝒪_X` over `V`
form a finite locally free module of rank `r` over the regular functions on `V` exactly when the
base change `V ×_Y X ⟶ V` is a finite locally free morphism of schemes of rank `r`.

This carries no `@[stacks 03ZU]` attribute.  Stacks 03ZU is the comparison of the *definition* of
Stacks 03ZV with condition (1) of Stacks 03ZW, and what is proved here is the comparison at one
affine chart and on sections; see the implementation notes for what separates the two.

Affineness of the base change cannot be dropped from the biconditional: the sections condition
does not bound the morphism, whereas `Stacks.Morphisms.IsFiniteLocallyFreeOfRank` extends
`AlgebraicGeometry.IsAffineHom`. -/
theorem module_isFiniteLocallyFreeOfRank_sections_iff (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine (chartScheme V))
    (hbc : _root_.AlgebraicGeometry.IsAffineHom (chartSchemeBaseChangeProjection B S hS f hf V))
    (r : ℕ) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS Y.1 Y.2 V)
        ((pushforwardStructureModule B S hS f).val.obj (op V)) r ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (chartSchemeBaseChangeProjection B S hS f hf V) r := by
  let := hV
  let := hbc
  let : Algebra (Γ(chartScheme V, ⊤) : Type u)
      (Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), ⊤) : Type u) :=
    ((chartSchemeBaseChangeProjection B S hS f hf V).appTop).hom.toAlgebra
  exact (module_isFiniteLocallyFreeOfRank_sections_iff_chartBaseChange B S hS f hf V r).trans
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine
      (chartSchemeBaseChangeProjection B S hS f hf V) r rfl).symm

/-! ### Condition (1) of Stacks 03ZW gives the sections condition at every affine chart -/

/-- **Condition (1) of Stacks 03ZW, with a fixed rank, gives the sections condition at every
affine chart.**  If every represented base change of a representable `f : X ⟶ Y` is a finite
locally free morphism of schemes of rank `r`, then the sections of `f_*𝒪_X` over every affine
étale chart `V` of `Y` form a finite locally free module of rank `r` over the regular functions
on `V`.

No affineness hypothesis on the base change is needed: it is carried by
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, which extends `AlgebraicGeometry.IsAffineHom`. -/
theorem module_isFiniteLocallyFreeOfRank_sections_of_presheaf (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ)
    (h : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V)) :
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS Y.1 Y.2 V)
      ((pushforwardStructureModule B S hS f).val.obj (op V)) r := by
  have hbc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (chartSchemeBaseChangeProjection B S hS f hf V) r :=
    h.property V.1.hom (hf.fst V.1.hom) (hf.snd V.1.hom) (hf.isPullback V.1.hom)
  exact (module_isFiniteLocallyFreeOfRank_sections_iff B S hS f hf V hV
    hbc.toIsAffineHom r).2 hbc

/-! ### The direction of Stacks 03ZU that the affine-chart comparison already gives -/

/-- The affine étale charts over which the sections of `f_*𝒪_X` are finite locally free of
rank `r` generate a covering sieve of every étale chart of `Y`, as soon as every represented base
change of `f` is a finite locally free morphism of schemes of rank `r`.

The covering is the family of Zariski-open charts cut out by the affine opens of the chart's
scheme, each of which is an affine chart and so satisfies the sections condition by
`AlgebraicGeometry.Space.module_isFiniteLocallyFreeOfRank_sections_of_presheaf`. -/
theorem freeRankPresieve_mem_topology_of_presheaf (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ)
    (h : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f.hom)
    (U : SmallEtale B S hS Y.1) :
    Sieve.generate (fun (V : SmallEtale B S hS Y.1) (_ : V ⟶ U) =>
      IsAffine (chartScheme V) ∧
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS Y.1 Y.2 V)
          ((pushforwardStructureModule B S hS f).val.obj (op V)) r) ∈
      SmallEtale.topology B S hS Y.1 U := by
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_
    (ofArrows_openChartInclusion_mem_topology B S hS Y.1 U
      (fun O : (chartScheme U).affineOpens => (O : (chartScheme U).Opens))
      (iSup_affineOpens_eq_top (chartScheme U)))
  have key : ∀ O : (chartScheme U).affineOpens,
      IsAffine (chartScheme (openChart B S hS Y.1 U (O : (chartScheme U).Opens))) :=
    fun O => inferInstanceAs (IsAffine ((O : (chartScheme U).Opens) : Scheme.{u}))
  have step : ∀ O : (chartScheme U).affineOpens,
      Module.IsFiniteLocallyFreeOfRank
        (chartRing B S hS Y.1 Y.2 (openChart B S hS Y.1 U (O : (chartScheme U).Opens)))
        ((pushforwardStructureModule B S hS f).val.obj
          (op (openChart B S hS Y.1 U (O : (chartScheme U).Opens)))) r :=
    fun O => module_isFiniteLocallyFreeOfRank_sections_of_presheaf B S hS f hf r h _ (key O)
  rintro Z k ⟨T, l, a, ha, rfl⟩
  obtain ⟨O⟩ := ha
  exact ⟨_, l, _, ⟨key O, step O⟩, rfl⟩

/-- **Stacks 03ZU, the direction from condition (1) of Stacks 03ZW to the definition of
Stacks 03ZV, with a fixed rank, granted only that `f_*𝒪_X` is cartesian on affine charts.**  If
every represented base change of a representable `f : X ⟶ Y` is a finite locally free morphism of
schemes of rank `r`, then `f` is affine and `f_*𝒪_X` has rank `r` on the small étale ringed site
of `Y` — that is, `f` is finite locally free of rank `r` in the sense of Stacks 03ZV.

The single hypothesis `hcart` is quasi-coherence of the direct image, read through Descent,
Proposition 03DX (2) as `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`; for `f` affine —
which the other hypothesis supplies — that is Stacks 03M9 for `f_*𝒪_X`.  Everything else is
proved: affineness is `AlgebraicGeometry.Space.isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank`,
the sections condition at an affine chart is
`AlgebraicGeometry.Space.module_isFiniteLocallyFreeOfRank_sections_of_presheaf`, and the passage
from the sections condition to the rank clause of Stacks 0409 is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_freeRankPresieve`.

It carries no `@[stacks 03ZU]` attribute: only one direction is proved, and that one carries a
hypothesis. -/
theorem isFiniteLocallyFreeOfRank_of_presheaf_of_isCartesianOnAffineCharts (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (r : ℕ)
    (hcart : IsCartesianOnAffineCharts (pushforwardStructureModule B S hS f))
    (h : (MorphismProperty.inverseImage
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
      (BigFppfOver.toScheme B S hS)).presheaf f.hom) :
    IsFiniteLocallyFreeOfRank B S hS f r :=
  (isFiniteLocallyFreeOfRank_iff B S hS f r).2
    ⟨isAffineHom_of_presheaf_isFiniteLocallyFreeOfRank B S hS r h,
      isFiniteLocallyFreeOfRank_of_freeRankPresieve B S hS Y.1 Y.2
        (pushforwardStructureModule B S hS f) hcart r
        (freeRankPresieve_mem_topology_of_presheaf B S hS f hf r h)⟩

end AlgebraicGeometry.Space

end
