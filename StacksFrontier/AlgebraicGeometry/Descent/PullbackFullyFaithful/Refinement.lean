module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackCompatibility
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.SourceFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DisjointUnion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fully faithful pullback along a refinement of coverings

Let `S` be a scheme and let `U` and `V` be two families of schemes over `S`, with a morphism of
families `α : U ⟶ V` over the identity of `S` — that is, `U` refines `V`. If `U` is an fpqc
covering of `S`, then the pullback functor from descent data relative to `V` to descent data
relative to `U` is fully faithful. Consequently the category of schemes over `S` is a full
subcategory of the category of descent data relative to any fpqc covering of `S`.

## Main results

* `AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_refinement`: **Stacks 02W0.** Pullback
  of descent data along a refinement whose source family is an fpqc covering is fully faithful.
* `AlgebraicGeometry.fullyFaithful_canonicalFunctor_comp_familyCoproduct_inverse`: the schemes
  over `S` form a full subcategory of the descent data relative to an fpqc covering of `S`.

## Implementation notes

The hypothesis is weaker than in the source, which assumes that `U` and `V` are *both* fpqc
coverings of `S`: only the refining family `U` is required to cover. Nothing in the argument
uses a covering property of `V`, and the source does not use one either — its appeal to the
covering property of `V` is through the auxiliary family `{U_i ×_S V_j}`, which refines `U` and
whose fibres over the members of `U` are the base changes of `V`. Passing to the coproducts of
the two families removes the need for that auxiliary family altogether: the refinement becomes
a single morphism `∐ U_i ⟶ ∐ V_j` over `S` whose source covers `S`, which is exactly the
hypothesis of Stacks 040K,
`AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_source_fpqc`.

Three facts assemble the statement for the families out of that one. A family is an fpqc
covering exactly when the single morphism out of its coproduct is
(`AlgebraicGeometry.ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem`); descent data
for a family are the same thing as descent data for that single morphism
(`AlgebraicGeometry.DescentData.familyCoproductEquivalence`); and that identification commutes
with pullback (`AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackCompatibility`). Full
faithfulness of the composite with a faithful functor gives full faithfulness of the first
factor, which is how the second equivalence is discarded again.

The final sentence of the source, that the schemes over `S` form a full subcategory of the
descent data relative to an fpqc covering `U`, is obtained from the single-morphism statement
`AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful` at the coproduct morphism of
`U`, transported along the same family–coproduct equivalence. The composite is the canonical
descent datum of the coproduct morphism read as a datum for the family; it is isomorphic to,
but not syntactically equal to, the componentwise canonical datum `i ↦ U_i ×_S W`.

## References

* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 02VZ](https://stacks.math.columbia.edu/tag/02VZ)
* [Stacks Project, Tag 040K](https://stacks.math.columbia.edu/tag/040K)
* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 02W0.** Let `U` and `V` be families of schemes over `S` and let `α` exhibit `U` as
a refinement of `V` over the identity of `S`. If `U` is an fpqc covering of `S`, then the
pullback functor from descent data relative to `V` to descent data relative to `U` is fully
faithful. -/
@[stacks 02W0]
theorem pullbackFunctor_fullyFaithful_of_refinement
    {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S))
    (hU : Presieve.ofArrows U.X U.f ∈ Scheme.fpqcPrecoverage S) :
    Nonempty ((MorphismOfSchemeFamilies.pullbackFunctor
      { sourceBase := S, targetBase := S,
        sourceFamily := U, targetFamily := V,
        baseHom := 𝟙 S, familyHom := α }).functor.FullyFaithful) := by
  let F : MorphismOfSchemeFamilies.{u} :=
    { sourceBase := S, targetBase := S,
      sourceFamily := U, targetFamily := V,
      baseHom := 𝟙 S, familyHom := α }
  let a := Sigma.desc V.f
  let a' := Sigma.desc U.f
  let P := DescentData.pullbackFunctor a a' (𝟙 S) F.coproductHom F.coproductHom_comp
  obtain ⟨hP⟩ : Nonempty P.functor.FullyFaithful :=
    pullbackFunctor_fullyFaithful_of_source_fpqc a' a F.coproductHom
      (by simpa [F, a, a'] using F.coproductHom_comp)
      ((ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem U.X U.f).1 hU)
  let E₁ := DescentData.familyCoproductEquivalence V.f
  let E₂ := DescentData.familyCoproductEquivalence U.f
  have hcomp : (E₁.equivalence.functor ⋙ P.functor).FullyFaithful :=
    E₁.equivalence.fullyFaithfulFunctor.comp hP
  have : E₂.equivalence.functor.Faithful := E₂.equivalence.fullyFaithfulFunctor.faithful
  exact ⟨(hcomp.ofIso (MorphismOfSchemeFamilies.pullbackCompatibility F).iso).ofCompFaithful⟩

/-- **Stacks 02W0**, final sentence: the schemes over `S` form a full subcategory of the
category of descent data relative to an fpqc covering `U` of `S`. The embedding is the
canonical descent datum of the coproduct morphism of `U`, read as a descent datum for the
family through the family–coproduct equivalence. -/
@[stacks 02W0 "the schemes over the base as a full subcategory of the descent data",
  sga "1 VIII 5.2" "more general"]
theorem fullyFaithful_canonicalFunctor_comp_familyCoproduct_inverse
    {S : Scheme.{u}} (U : PreZeroHypercover.{u} S)
    (hU : Presieve.ofArrows U.X U.f ∈ Scheme.fpqcPrecoverage S) :
    Nonempty ((DescentData.canonicalFunctor (Sigma.desc U.f) ⋙
      (DescentData.familyCoproductEquivalence U.f).equivalence.inverse).FullyFaithful) := by
  obtain ⟨hC⟩ := DescentData.canonicalFunctor_fullyFaithful (Sigma.desc U.f)
    ((ofArrows_mem_fpqcPrecoverage_iff_singleton_sigmaDesc_mem U.X U.f).1 hU)
  exact ⟨hC.comp
    (DescentData.familyCoproductEquivalence U.f).equivalence.symm.fullyFaithfulFunctor⟩

end AlgebraicGeometry
