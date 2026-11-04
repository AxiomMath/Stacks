module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IntegralRefinement
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfFiniteDomination

/-!
# The refinement of an étale covering may be taken finite and of finite presentation

[Stacks, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0) refines a surjective étale
`p : U ⟶ X` over a quasi-compact and quasi-separated base by a surjective morphism `f : Y ⟶ X`
which factors through `p` Zariski-locally on `Y`, and says that `f` may be taken **finite and of
finite presentation**. `StacksFrontier.AlgebraicGeometry.MoreMorphisms.IntegralRefinement` produces
such an `f` that is integral; this file upgrades it to a finite one of finite presentation, which
is the tag's closing sentence.

The upgrade is the source's: present the integral `f : Y ⟶ X` as the limit of a directed inverse
system of morphisms to `X` that are finite and of finite presentation
([Stacks, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)), descend a finite affine open
covering of `Y` refining the Zariski covering on which `f` factors through `p` to a single stage
of that system, descend the factorisations through `p` to a further stage, and take that stage.

Both halves are already in the library and neither is reproved here.

* Tag 09YZ over a base that is merely quasi-compact and quasi-separated is
  `Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, which is part (2)
  of [Stacks, Tag 0817](https://stacks.math.columbia.edu/tag/0817) fed into
  `Stacks.IntegralLimit.nonempty_integralLimitPresentation_of_algebraColimit`.
* The descent of the covering and of the factorisations is
  `AlgebraicGeometry.exists_finite_surjective_refinement_of_isLimit`, the core of
  [Stacks, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0).

What this file supplies is the translation between the two presentations of the Zariski-local
factorisation property: `Stacks.MoreMorphisms.ZariskiLocallyFactors`, a neighbourhood with a
section at every point, and the jointly surjective family of open immersions with factorisations
that the descent lemma consumes and returns. The covering is indexed by the points of the source
and the open neighbourhood at a point is used as the member at that index; coming back, a member
of the returned family is replaced by its open image and the factorisation transported along
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`.

The étale covering `p` enters the descent lemma as the one-member family indexed by `PUnit`; the
local finite presentation of its members that the lemma asks for is the local finite presentation
of an étale morphism.

## Main results

* `Stacks.MoreMorphisms.exists_isFinite_finitePresentation_surjective_zariskiLocallyFactors` —
  the closing sentence of [Stacks, Tag 09Z0]: a surjective étale covering of a quasi-compact and
  quasi-separated scheme is refined by a surjective morphism that is finite and of finite
  presentation and factors through it Zariski-locally.
* `Stacks.MoreMorphisms.exists_ofArrows_mem_zariskiPrecoverage_of_zariskiLocallyFactors` and
  `Stacks.MoreMorphisms.zariskiLocallyFactors_of_ofArrows_mem_zariskiPrecoverage` — the two
  directions of the translation between the Zariski-local factorisation property and a jointly
  surjective family of open immersions whose members factor through the covering.

## References

* [Stacks Project, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.MoreMorphisms

variable {U X : Scheme.{u}}

/-- A morphism with the Zariski-local factorisation property carries a jointly surjective family
of open immersions into its source, indexed by the points of that source, each member of which
factors through the covering.

This is the presentation of `Stacks.MoreMorphisms.ZariskiLocallyFactors` that
`AlgebraicGeometry.exists_finite_surjective_refinement_of_isLimit` consumes. -/
public theorem exists_ofArrows_mem_zariskiPrecoverage_of_zariskiLocallyFactors
    {Y : Scheme.{u}} (f : Y ⟶ X) (p : U ⟶ X) (h : ZariskiLocallyFactors f p) :
    ∃ (J : Type u) (W : J → Scheme.{u}) (w : ∀ a, W a ⟶ Y),
      Presieve.ofArrows W w ∈ Scheme.zariskiPrecoverage Y ∧
        ∀ a, ∃ t : W a ⟶ U, w a ≫ f = t ≫ p := by
  classical
  choose V hV s hs using h
  refine ⟨Y, fun y => (V y).toScheme, fun y => (V y).ι, ?_, fun y => ⟨s y, hs y⟩⟩
  rw [Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun y => ⟨y, ?_⟩, fun y => inferInstance⟩
  have hy : y ∈ ((V y : Y.Opens) : Set Y) := hV y
  rwa [← Scheme.Opens.range_ι] at hy

/-- A jointly surjective family of open immersions into `Y` whose members factor through
`p : U ⟶ X` over `f : Y ⟶ X` gives `f` the Zariski-local factorisation property: the member
through which a point is hit is replaced by its open image in `Y`, which is a neighbourhood of
that point carrying a section.

This is the inverse translation to
`Stacks.MoreMorphisms.exists_ofArrows_mem_zariskiPrecoverage_of_zariskiLocallyFactors`. -/
public theorem zariskiLocallyFactors_of_ofArrows_mem_zariskiPrecoverage {Y : Scheme.{u}}
    (f : Y ⟶ X) (p : U ⟶ X) {J : Type u} {W : J → Scheme.{u}} {w : ∀ a, W a ⟶ Y}
    (hcover : Presieve.ofArrows W w ∈ Scheme.zariskiPrecoverage Y)
    (hfac : ∀ a, ∃ t : W a ⟶ U, w a ≫ f = t ≫ p) :
    ZariskiLocallyFactors f p := by
  obtain ⟨hsurj, hopen⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).mp hcover
  intro y
  obtain ⟨a, hy⟩ := hsurj y
  have _ : IsOpenImmersion (w a) := hopen a
  obtain ⟨t, ht⟩ := hfac a
  have hinv : (w a).isoOpensRange.inv ≫ w a = (w a).opensRange.ι :=
    (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι (w a)).symm
  refine ⟨(w a).opensRange, ?_, (w a).isoOpensRange.inv ≫ t, ?_⟩
  · exact Scheme.Hom.mem_opensRange.mpr hy
  · calc (w a).opensRange.ι ≫ f
        = ((w a).isoOpensRange.inv ≫ w a) ≫ f := by rw [hinv]
      _ = (w a).isoOpensRange.inv ≫ t ≫ p := by rw [Category.assoc, ht]
      _ = ((w a).isoOpensRange.inv ≫ t) ≫ p := (Category.assoc _ _ _).symm

/-- **Stacks, Tag 09Z0: the refinement may be taken finite and of finite presentation.** Let
`p : U ⟶ X` be a surjective étale morphism of schemes with `X` quasi-compact and quasi-separated.
Then there exist a scheme `Y` and a surjective morphism `f : Y ⟶ X` which is finite and of finite
presentation — hence in particular integral — such that every point of `Y` has an open
neighbourhood `V` for which `V ⟶ X` factors through `p`.

This is the whole of the tag: the first assertion asks only that `f` be integral, which finiteness
gives, and the closing sentence asks for exactly the finiteness and the finite presentation. No
hypothesis beyond the source's is used; in particular `p` is not assumed separated and nothing is
assumed about the degrees of its fibres.

The integral refinement is
`Stacks.MoreMorphisms.exists_isIntegralHom_surjective_zariskiLocallyFactors`; it is presented as
a limit of morphisms finite and of finite presentation by
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, which is
[Stacks, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ) over a quasi-compact and
quasi-separated base; and one stage of that limit already carries the covering and the
factorisations, by
`AlgebraicGeometry.exists_finite_surjective_refinement_of_isLimit`. -/
@[stacks 09Z0 "the whole statement: the surjective refinement factoring through the covering
Zariski-locally, and the closing sentence that it may be taken finite and of finite presentation"]
public theorem exists_isFinite_finitePresentation_surjective_zariskiLocallyFactors (p : U ⟶ X)
    [Etale p] [Surjective p] [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsIntegralHom f ∧ Surjective f ∧ IsFinite f ∧
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
      ZariskiLocallyFactors f p := by
  obtain ⟨Y, g, hgint, hgsurj, hzl⟩ := exists_isIntegralHom_surjective_zariskiLocallyFactors p
  obtain ⟨J, W, w, hwcover, hwfac⟩ :=
    exists_ofArrows_mem_zariskiPrecoverage_of_zariskiLocallyFactors g p hzl
  obtain ⟨P⟩ :=
    @_root_.Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation
      Y X g hgint ‹_› ‹_›
  obtain ⟨Y', g', hfin, hsurj, hfp, K, W', w', hcover', hfac'⟩ :=
    @exists_finite_surjective_refinement_of_isLimit PUnit.{1} X inferInstance inferInstance
      (fun _ => U) (fun _ => p) (fun _ => inferInstance) Y g hgint hgsurj J W w hwcover
      (fun a => ⟨PUnit.unit, (hwfac a).choose, (hwfac a).choose_spec⟩)
      P.indexType P.indexPreorder P.indexNonempty P.indexDirected P.diagram P.structureMap
      P.limitCone P.compatible P.isLimit P.stageFinite P.stageFinitePresentation
  have _ : IsFinite g' := hfin
  refine ⟨Y', g', inferInstance, hsurj, hfin, hfp.1, hfp.2.1, hfp.2.2,
    zariskiLocallyFactors_of_ofArrows_mem_zariskiPrecoverage g' p hcover' fun a => ?_⟩
  obtain ⟨⟨⟩, t, ht⟩ := hfac' a
  exact ⟨t, ht⟩

end Stacks.MoreMorphisms

end
