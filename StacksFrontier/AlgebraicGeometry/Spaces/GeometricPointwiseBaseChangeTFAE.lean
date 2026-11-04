module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartQuadrupleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDiagramChartwiseBaseChange

/-!
# Stacks 0DKG

For a cartesian square of algebraic spaces, `K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'`, the following are equivalent: the map of Equation 0DKF is invertible at every
geometric point of `X'` in every degree; the conditions of Stacks 0DJ8 hold on every étale diagram
of schemes over the square; they hold on one such diagram with `U' ⟶ X'` surjective.

## Main results

* `AlgebraicGeometry.Space.tfae_geometricPointwiseBaseChange`
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] BaseChangeChart.isOpenImmersion_incU BaseChangeChart.isOpenImmersion_incV
  BaseChangeChart.isOpenImmersion_incV'
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

/-- **Stacks 0DKG.** For a cartesian square of algebraic spaces, `K ∈ D_QCoh(𝒪_X)`,
`K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, the following are equivalent:
(1) the map of Equation 0DKF is an isomorphism at every geometric point of `X'` in every degree;
(2) for every diagram of schemes `U ⟶ V ⟵ V'` étale over `X ⟶ Y ⟵ Y'` with `U' = V' ×_V U`, the
conditions of Stacks 0DJ8 hold for `La^*K` and `L(a')^*K'`;
(3) they hold for some such diagram with `U' ⟶ X'` surjective. -/
@[stacks 0DKG]
theorem tfae_geometricPointwiseBaseChange {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    List.TFAE [GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ,
      EtaleDiagramChartwiseBaseChange f g f' g' K hK K' hK' φ,
      SurjectiveDiagramChartwiseBaseChange f g f' g' K hK K' hK' φ] := by
  tfae_have 1 → 2 := fun h1 => ⟨fun U V V' U' a b c a' f₀ g₀ f₀' g₀' ha hb hc hpb hfa hgb hfc ha' =>
    ⟨fun ch => (isIso_comparison_iff_chartQuadruple g' hpb ch K hK K' hK' φ a a' ha').mpr
      ((isIso_affineQuadrupleChart_comparison_iff_forall_isIso_geometricStalkBaseChangeCohomologyMap
        sq K hK K' hK' φ (representedSpaceMap B S hS (chartSiteObjectι ch.incU) ≫ a)
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV) ≫ b)
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV') ≫ c)
        (representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ a')
        (chartQuadrupleF ch) (chartQuadrupleG ch) (pullback.snd _ _) (pullback.fst _ _)
        pullback.condition
        (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incU a ha)
        (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incV b hb)
        (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incV' c hc)
        (IsPullback.of_hasPullback _ _) (chartQuadruple_hfa ch f a b hfa)
        (chartQuadruple_hgb ch g b c hgb) (chartQuadruple_hfc ch hpb f' c a' hfc)
        (chartQuadruple_ha' ch g' hpb a a' ha')).mpr fun x n => h1 _ n)⟩⟩
  tfae_have 2 → 3 := surjectiveDiagramChartwiseBaseChange_of_etaleDiagramChartwiseBaseChange sq
  tfae_have 3 → 1 := by
    rintro ⟨U, V, V', U', a, b, c, a', f₀, g₀, f₀', g₀', ha, hb, hc, hpb, hfa, hgb, hfc, ha', hs,
      hD⟩
    intro x' n
    obtain ⟨ch, x, rfl⟩ := exists_baseChangeChart_geometricPoint_lift sq a b c a' ha hb hc hpb hfa
      hgb hfc ha' hs x'
    exact
      (isIso_affineQuadrupleChart_comparison_iff_forall_isIso_geometricStalkBaseChangeCohomologyMap
        sq K hK K' hK' φ (representedSpaceMap B S hS (chartSiteObjectι ch.incU) ≫ a)
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV) ≫ b)
        (representedSpaceMap B S hS (chartSiteObjectι ch.incV') ≫ c)
        (representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ a')
        (chartQuadrupleF ch) (chartQuadrupleG ch) (pullback.snd _ _) (pullback.fst _ _)
        pullback.condition
        (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incU a ha)
        (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incV b hb)
        (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incV' c hc)
        (IsPullback.of_hasPullback _ _) (chartQuadruple_hfa ch f a b hfa)
        (chartQuadruple_hgb ch g b c hgb) (chartQuadruple_hfc ch hpb f' c a' hfc)
        (chartQuadruple_ha' ch g' hpb a a' ha')).mp
      ((isIso_comparison_iff_chartQuadruple g' hpb ch K hK K' hK' φ a a' ha').mp (hD.isIso ch)) x n
  tfae_finish

end AlgebraicGeometry.Space

end
