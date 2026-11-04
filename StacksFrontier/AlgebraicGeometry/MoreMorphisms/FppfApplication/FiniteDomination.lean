module

public import StacksFrontier.AlgebraicGeometry.Limits.IntegralAffineLimit09YZ
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSlices
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfIntegralDomination
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite domination of an fppf covering

[Stacks, Tag 0CP0] says that for every fppf covering `{S_i ⟶ S}` of a quasi-compact and
quasi-separated scheme there are a surjective finite morphism `S' ⟶ S` of finite presentation
and an open covering `S' = ⋃ U'_α` such that each `U'_α ⟶ S` factors through `S_i ⟶ S` for some
`i`. This file states that, with the open covering presented as a family of opens of `S'` whose
supremum is the whole space — the shape in which the neighbouring
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.FppfApplication.IntegralDomination` states
[Stacks, Tag 0CNZ] — and proves it, at the hypotheses of the source and with nothing carried.

The source proof is exactly the one carried out here. Its two inputs are [Stacks, Tag 0CNZ],
the same statement with the dominating morphism merely *integral*, and [Stacks, Tag 09YZ], the
presentation of an integral morphism over a quasi-compact quasi-separated base as a directed
inverse limit of finite morphisms of finite presentation; given those, a finite affine open
covering of the integral dominating scheme is descended to a stage of the inverse system
([Stacks, Tag 01Z4]), the factorizations through the members of the fppf covering are descended
to a further stage ([Stacks, Proposition 01ZC]), and that stage is the required `S'`.

All four steps are already in the library. The descent of the covering and of the
factorizations, which is the whole of the middle of the argument, is
`AlgebraicGeometry.exists_finite_surjective_refinement_of_isLimit`; fed with [Stacks, Tag 0CNZ]
in the form `AlgebraicGeometry.exists_integral_surjective_refinement_of_mem_fppfPrecoverage`
and with [Stacks, Tag 0570] discharged by `AlgebraicGeometry.hasQuasiFiniteSlices`, it becomes
`AlgebraicGeometry.exists_finite_surjective_refinement_of_hasQuasiFiniteSlices`. Nothing of
that is reproved here; this file converts its Zariski covering into the family of opens in
which the source states the conclusion.

[Stacks, Tag 09YZ] itself is in the library at the hypotheses the source gives it, as
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`: an integral
morphism over a quasi-compact and quasi-separated base is the limit of a directed inverse
system of schemes finite and of finite presentation over that base. That is what supplies the
second input here, so the tag below carries no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage`
  is [Stacks, Tag 0CP0]: the dominating finite morphism of finite presentation, the open
  covering of its source and the factorizations through the members of the given covering.
* `AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_isAffine` is the same
  statement for an affine base, reached by the short ring-theoretic route of
  `AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine` instead of the sheaf-
  theoretic [Stacks, Tag 09YZ].
* `AlgebraicGeometry.Scheme.Cover.exists_finite_surjective_openCover_factorization` is the
  general statement for a covering presented as an `AlgebraicGeometry.Scheme.Cover` for
  `AlgebraicGeometry.Scheme.fppfPrecoverage`.

The affine case is not degenerate: `S'` is a genuine stage of the inverse system presenting the
integral dominating scheme of [Stacks, Tag 0CNZ], and that scheme is in general an infinite
product of normalizations, not `S` and not isomorphic to it.

## Implementation notes

`AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_integralLimitPresentation`
takes [Stacks, Tag 09YZ] as a hypothesis only *at the given base* `S`, which is all the argument
uses and is weaker than the global
`AlgebraicGeometry.IntegralHasFinitePresentationLimit`; the two results above are both one-line
consequences of it, the first discharging that hypothesis with [Stacks, Tag 09YZ] and the second
with its affine-base case.

The conversion of a Zariski covering — a jointly surjective family of open immersions into `S'`
— into a family of opens of `S'` with supremum `⊤` is isolated as
`AlgebraicGeometry.exists_opens_iSup_eq_top_factorization_of_zariskiPrecoverage`. Each member is
replaced by its image and the factorization is transported along
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`.

The index type of the given covering is left in an arbitrary universe and no smallness
hypothesis is imposed on it: no coproduct is taken over it, and the open covering produced is
indexed by a type in the universe of the schemes.

## References

* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Proposition 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A Zariski covering of `S'` whose members factor through a family `f` of morphisms to `S`
over `g : S' ⟶ S` gives a family of *opens* of `S'` with supremum `⊤` whose inclusions factor
through `f` over `g`.

This is the change of presentation between the Zariski covering produced by the limit argument
and the open covering `S' = ⋃ U'_α` in which [Stacks, Tag 0CP0] and [Stacks, Tag 0CNZ] are
stated. -/
theorem exists_opens_iSup_eq_top_factorization_of_zariskiPrecoverage {I : Type v}
    {S S' : Scheme.{u}} (g : S' ⟶ S) {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    {J : Type u} {U : J → Scheme.{u}} {ι : ∀ c, U c ⟶ S'}
    (hcover : Presieve.ofArrows U ι ∈ Scheme.zariskiPrecoverage S')
    (hfac : ∀ c, ∃ i, ∃ t : U c ⟶ X i, ι c ≫ g = t ≫ f i) :
    ∃ (K : Type u) (V : K → S'.Opens), (⨆ c, V c) = ⊤ ∧
      ∀ c, ∃ i, ∃ t : (V c).toScheme ⟶ X i, (V c).ι ≫ g = t ≫ f i := by
  obtain ⟨hsurj, hopen⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).mp hcover
  refine ⟨J, fun c => (ι c).opensRange, ?_, ?_⟩
  · refine Opens.ext (Set.eq_univ_of_forall fun z => ?_)
    rw [Opens.coe_iSup]
    obtain ⟨c, hc⟩ := hsurj z
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  · intro c
    have : IsOpenImmersion (ι c) := hopen c
    obtain ⟨i, t, ht⟩ := hfac c
    have hinv : (ι c).isoOpensRange.inv ≫ ι c = (ι c).opensRange.ι :=
      (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι (ι c)).symm
    refine ⟨i, (ι c).isoOpensRange.inv ≫ t, ?_⟩
    rw [← hinv, Category.assoc, ht, Category.assoc]

/-- **[Stacks, Tag 0CP0]** for a quasi-compact quasi-separated base over which every integral
morphism has a presentation as a directed inverse limit of finite morphisms of finite
presentation. For every fppf covering `{X i ⟶ S}` of such a base there are a surjective finite
morphism `g : S' ⟶ S` of finite presentation and an open covering of `S'` such that each member
`U c` of the covering maps to `S` through some member `X i` of the given covering.

The hypothesis `H` is [Stacks, Tag 09YZ] restricted to the base `S` at hand, which is all the
argument uses. -/
theorem exists_finite_surjective_openCover_factorization_of_integralLimitPresentation
    {I : Type v} {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S)
    (H : ∀ (Y : Scheme.{u}) (p : Y ⟶ S), IsIntegralHom p →
      Nonempty (IntegralLimitPresentation p)) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
      ∃ (J : Type u) (U : J → S'.Opens), (⨆ c, U c) = ⊤ ∧
        ∀ c, ∃ i, ∃ t : (U c).toScheme ⟶ X i, (U c).ι ≫ g = t ≫ f i := by
  have hfp : ∀ i, LocallyOfFinitePresentation (f i) := fun i =>
    (((Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hf).2 i).2
  obtain ⟨Y, q, hqint, hqsurj, J, W, w, hwcover, hwfac⟩ :=
    exists_integral_surjective_refinement_of_mem_fppfPrecoverage hasQuasiFiniteSlices X f hf
  obtain ⟨p⟩ := H Y q hqint
  obtain ⟨S', g, hgfin, hgsurj, hgfp, K, U, ι, hιcover, hιfac⟩ :=
    @exists_finite_surjective_refinement_of_isLimit I S inferInstance inferInstance X f hfp
      Y q hqint hqsurj J W w hwcover hwfac p.indexType p.indexPreorder p.indexNonempty
      p.indexDirected p.diagram p.structureMap p.limitCone p.compatible p.isLimit p.stageFinite
      p.stageFinitePresentation
  exact ⟨S', g, hgfin, hgsurj, hgfp,
    exists_opens_iSup_eq_top_factorization_of_zariskiPrecoverage g f hιcover hιfac⟩

/-- **[Stacks, Tag 0CP0].** For every fppf covering `{X i ⟶ S}` of a quasi-compact and
quasi-separated scheme `S` there are a surjective finite morphism `g : S' ⟶ S` of finite
presentation and an open covering of `S'` such that each member `U c` of the covering maps to
`S` through some member `X i` of the given covering.

The second input of the source proof, [Stacks, Tag 09YZ], is supplied by
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, which proves it
at exactly the quasi-compactness and quasi-separatedness assumed here. -/
@[stacks 0CP0]
theorem exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage
    {I : Type v} {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
      ∃ (J : Type u) (U : J → S'.Opens), (⨆ c, U c) = ⊤ ∧
        ∀ c, ∃ i, ∃ t : (U c).toScheme ⟶ X i, (U c).ι ≫ g = t ≫ f i :=
  exists_finite_surjective_openCover_factorization_of_integralLimitPresentation X f hf
    fun Y p hp => @_root_.Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation
      Y S p hp inferInstance inferInstance

/-- **[Stacks, Tag 0CP0] for an affine base.** For every fppf covering `{X i ⟶ S}` of an affine
scheme `S` there are a surjective finite morphism `g : S' ⟶ S` of finite presentation and an
open covering of `S'` such that each member `U c` of the covering maps to `S` through some
member `X i` of the given covering.

The affineness of `S` is strictly stronger than the quasi-compactness and quasi-separatedness
of the source statement, so the tag sits on
`AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage` and
not here. What this special case offers is the route through the affine-base form of
[Stacks, Tag 09YZ], `AlgebraicGeometry.nonempty_integralLimitPresentation_of_isAffine`, which
is purely ring-theoretic. -/
theorem exists_finite_surjective_openCover_factorization_of_isAffine {I : Type v}
    {S : Scheme.{u}} [IsAffine S] (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
      ∃ (J : Type u) (U : J → S'.Opens), (⨆ c, U c) = ⊤ ∧
        ∀ c, ∃ i, ∃ t : (U c).toScheme ⟶ X i, (U c).ι ≫ g = t ≫ f i :=
  exists_finite_surjective_openCover_factorization_of_integralLimitPresentation X f hf
    fun _ p hp => @nonempty_integralLimitPresentation_of_isAffine _ _ p hp ‹_›

/-- **[Stacks, Tag 0CP0]** for a covering presented as an `AlgebraicGeometry.Scheme.Cover` for
`AlgebraicGeometry.Scheme.fppfPrecoverage`: the fppf covering `𝒮` of a quasi-compact and
quasi-separated scheme `S` is dominated by a surjective finite morphism `g : S' ⟶ S` of finite
presentation whose source carries an open covering each member of which maps to `S` through
some member of `𝒮`.

The tag sits on
`AlgebraicGeometry.exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage`, of
which this is a restatement. -/
theorem Scheme.Cover.exists_finite_surjective_openCover_factorization {S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (𝒮 : S.Cover.{v} Scheme.fppfPrecoverage) :
    ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsFinite g ∧ Surjective g ∧ FinitePresentation g ∧
      ∃ (J : Type u) (U : J → S'.Opens), (⨆ c, U c) = ⊤ ∧
        ∀ c, ∃ i, ∃ t : (U c).toScheme ⟶ 𝒮.X i, (U c).ι ≫ g = t ≫ 𝒮.f i :=
  exists_finite_surjective_openCover_factorization_of_mem_fppfPrecoverage 𝒮.X 𝒮.f 𝒮.mem₀

end AlgebraicGeometry

end
