module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# A reduced étale chart on which global regular functions are determined

A reduced algebraic space admits a surjective étale scheme chart which is itself reduced and on
which a global regular function is determined by its restriction: evaluation of a compatible
family of regular functions at that one chart is injective.

## Main results

* `AlgebraicGeometry.Space.exists_reduced_etale_chart_injective_globalSections`.

## Implementation notes

Reducedness of an algebraic space is the étale-local property of schemes of Tag 03E6, so it
hands over a surjective étale chart `A ⟶ F` with `A` reduced; that chart is the witness. For
injectivity, take any chart `c` of the small étale site and base-change `A ⟶ F` along it
(Tag 03EC): the projection `α : P ⟶ c` is surjective étale and the projection `P ⟶ A` makes `P`
an étale chart again, so a compatible family's value at `c` pulls back to its value at `P`,
which is already determined by its value at `A`. Injectivity of pullback of global regular
functions along a surjective étale morphism of schemes over the site
(`gamma_injective_of_etale_surjection`) then determines the value at `c`.

This is the sheaf-separatedness argument of the source, but run through the descent lemma the
library already has rather than through the small étale topology: no covering of `c` has to be
replaced by a chosen representative, because the one-arrow family `{α}` is used only through
the injectivity it yields.

Running it that way makes the statement sharper than the source's: there is no hypothesis that
`F` is an algebraic space. `HasEtaleLocalProperty` already hands over the chart, and nothing
below uses the sheaf condition on the small étale site — which is the one place the algebraic
space hypothesis would have been needed.

This file carries NO `@[stacks]` attribute: it is an auxiliary statement, a step towards
Tag 0741 rather than any part of a tag's own content, and Tag 03G6 — the tag its source
paragraph belongs to — is already formalized as
`AlgebraicGeometry.Space.structurePresheaf_isSheaf`.

## References

* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A reduced algebraic space has a reduced surjective étale chart at which evaluation of
compatible families of regular functions on its small étale site is injective. -/
theorem exists_reduced_etale_chart_injective_globalSections
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hred : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsReduced X)) :
    ∃ V : SmallEtale B S hS F,
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) V.1.hom ∧
      IsReduced ((BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj V)) ∧
      Function.Injective (fun s : (structurePresheaf B S hS F ⋙
        forget CommRingCat.{u}).sections => s.1 (op V)) := by
  classical
  obtain ⟨A, q, hqSurj, hqEtale, hredA⟩ := hred
  let Tscheme := BigFppfOver.toScheme B S hS
  let AChart : SmallEtale B S hS F := ⟨CostructuredArrow.mk q, hqEtale⟩
  refine ⟨AChart, hqSurj, hredA, ?_⟩
  intro s t hst
  refine Functor.sections_ext_iff.mpr ?_
  intro cop
  obtain ⟨P, α, p, hpb⟩ := hqEtale.1 cop.unop.1.hom
  let pHom : P ⟶ A := Yoneda.fullyFaithful.preimage p
  have hpHom : yoneda.map pHom = p := Yoneda.fullyFaithful.map_preimage p
  have hpb' : IsPullback (yoneda.map pHom) (yoneda.map α) q cop.unop.1.hom := by
    rw [hpHom]; exact hpb
  have hαEtale : Etale (Tscheme.map α) := hqEtale.2 cop.unop.1.hom p α hpb
  have hαSurj : Surjective (Tscheme.map α) := hqSurj.2 cop.unop.1.hom p α hpb
  have hpEtale : Etale (Tscheme.map pHom) :=
    cop.unop.property.2 q (yoneda.map α) pHom hpb'.flip
  let PChart : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map pHom ≫ q),
      etale_comp_of_scheme B S hS pHom q hpEtale hqEtale⟩
  let gα : PChart ⟶ cop.unop := ObjectProperty.homMk <|
    CostructuredArrow.homMk α (by
      change yoneda.map α ≫ cop.unop.1.hom = yoneda.map pHom ≫ q
      rw [hpHom]; exact hpb.w.symm)
  let gp : PChart ⟶ AChart := ObjectProperty.homMk <| CostructuredArrow.homMk pHom rfl
  refine gamma_injective_of_etale_surjection B S hS α hαSurj hαEtale ?_
  have key : ∀ u : (structurePresheaf B S hS F ⋙ forget CommRingCat.{u}).sections,
      (Scheme.Γ.map (Tscheme.map α).op).hom (u.1 cop) =
        (Scheme.Γ.map (Tscheme.map pHom).op).hom (u.1 (op AChart)) :=
    fun u => (u.property gα.op).trans (u.property gp.op).symm
  rw [key s, key t, show s.1 (op AChart) = t.1 (op AChart) from hst]

end AlgebraicGeometry.Space

end
