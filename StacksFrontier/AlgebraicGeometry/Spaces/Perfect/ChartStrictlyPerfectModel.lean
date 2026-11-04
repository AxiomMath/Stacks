module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocalSliceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.TerminalStrictlyPerfectModel

/-!
# A strictly perfect local model over an étale chart is a global model on the chart

Let `X` be an algebraic space and `V` an étale chart of `X`, that is an object of the small étale
site of `X`, with underlying scheme `U` and étale morphism `h_U ⟶ X`. The slice of the small
étale site of `X` at `V` is the small étale site of `h_U` (Stacks 04M0), in which the identity
chart of `U` is a terminal object. Hence a strictly perfect complex on the slice at `V`
quasi-isomorphic to the restriction of a complex `K` becomes a strictly perfect complex of
`𝒪_{h_U}`-modules representing `K|_{h_U}` in `D(𝒪_{h_U})`.

This is the passage from the local data of Stacks 08G5 to complexes on the algebraic spaces
represented by the members of a covering, used to compare perfectness on the small étale site of
an affine scheme with perfectness on the scheme (the converse half of Stacks 08HG).

## Main results

* `AlgebraicGeometry.Space.exists_isStrictlyPerfect_iso_chartRestriction`: a strictly perfect
  local model over an étale chart `V` gives a strictly perfect complex on the chart space of `V`
  representing the restriction.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of étale charts of `X` from the image of the identity chart of the chart space
of `V` under postcomposition with the chart morphism, to `V`: both have underlying scheme the
scheme of `V`, and the morphism is its identity. -/
def chartPostcompIdHom {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1) :
    (smallEtaleRingedSitePostcomp B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj
      (idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) (by
    change yoneda.map (𝟙 _) ≫ V.1.hom = 𝟙 _ ≫ V.1.hom
    simp))

/-- **A strictly perfect local model over an étale chart is a global model on the chart.** Let
`K` be a complex of `𝒪_X`-modules and `V` an étale chart of `X` over which `K` has a strictly
perfect local model (the datum of Stacks 08G5). Then the restriction of `K` to the algebraic space
`h_U` represented by `V` is represented in `D(𝒪_{h_U})` by a strictly perfect complex of
`𝒪_{h_U}`-modules. -/
theorem exists_isStrictlyPerfect_iso_chartRestriction {X : AlgebraicSpaces B S hS}
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (V : SmallEtale B S hS X.1)
    (h : (smallEtaleRingedSite B S hS X.1 X.2).HasStrictlyPerfectQuasiIso K V) :
    ∃ P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS X V).1
        (chartSpace B S hS X V).2) ℤ,
      IsStrictlyPerfect _ P ∧ Nonempty (DerivedCategory.Q.obj P ≅
        (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
          (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  let f := chartToSpace B S hS X V
  let hf := isEtale_chartToSpace B S hS X V
  let t := idEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)
  have h' := RingedSite.hasStrictlyPerfectQuasiIso_of_hom _ K (chartPostcompIdHom B S hS V) h
  have := etaleSliceRestriction_additive B S hS f hf t
  have := etaleSliceRestriction_preservesFiniteLimits B S hS f hf t
  have := etaleSliceRestriction_preservesFiniteColimits B S hS f hf t
  have h'' := RingedSite.hasStrictlyPerfectQuasiIso_map_of_square_of_sliceFunctors
    (smallEtaleRingedSitePostcomp B S hS f hf) (etaleModulePullback.{u, u} B S hS f hf)
    (etaleSliceRestriction B S hS f hf) t (etaleSliceRestrictionUnitIso B S hS f hf t)
    (etaleSliceRestrictionSquare B S hS f hf t) K h'
  obtain ⟨P, hP, q, hq⟩ := RingedSite.exists_isStrictlyPerfect_quasiIso_of_isTerminal _
    (isTerminalIdEtaleChart B S hS ((SmallEtale.toOver B S hS X.1).obj V)) _ h''
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := q)).2 hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryFactors.app K).symm⟩⟩

end AlgebraicGeometry.Space
