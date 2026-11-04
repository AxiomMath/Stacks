module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebraRelativeSpecSize
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs

/-!
# The chart objects of the normalization of `X` in `Y` are objects of the site

Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces and let `𝒪'`
be the integral closure of `𝒪_X` in `f_* 𝒪_Y`. Over an étale scheme chart `V` of `X` the
relative spectrum of `𝒪'` is the scheme `AlgebraicGeometry.Space.chartRelativeSpec`; this file
proves that it is an object of the ambient big fppf site. The key input is a bound on the
sections of `f_* 𝒪_Y` over the étale charts `openChart V O` by one cardinal `2 ^ T.size`,
uniform in the Zariski open `O` of `chartScheme V`.

## Main results

* `AlgebraicGeometry.Space.exists_contains_mk_sections_pushforwardAlgebra_openChart_le`: the
  sections of `f_* 𝒪_Y` over the Zariski opens of a chart of `X` are bounded uniformly in the
  open, by `2 ^ T.size` for a single object `T` of the site.
* `AlgebraicGeometry.Space.exists_contains_mk_sections_integralClosureSheaf_openChart_le`: the
  same bound for the integral closure of `𝒪_X` in `f_* 𝒪_Y`.
* `AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`:
  for `f` quasi-compact and quasi-separated, the relative spectrum of `𝒪'` over a chart of `X` is
  an object of the site.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 0821](https://stacks.math.columbia.edu/tag/0821)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sections of a direct-image algebra over the Zariski opens of a chart are bounded
uniformly in the open: there is an object `T` of the site with
`#(f_* 𝒪_Y)(openChart V O) ≤ 2 ^ T.size` for every Zariski open `O` of `chartScheme V`. -/
theorem exists_contains_mk_sections_pushforwardAlgebra_openChart_le
    {X : AlgebraicSpaces B S hS} (Z : Over X) (V : SmallEtale B S hS X.1) :
    ∃ T : Scheme.{u}, B.Contains T ∧ ∀ O : (chartScheme V).Opens,
      #(ToType ((pushforwardAlgebra B S hS Z).right.obj.obj
        (op (openChart B S hS X.1 V O)))) ≤ 2 ^ T.size := by
  obtain ⟨W, hW⟩ :=
    exists_openChart_isCovering_chartBaseChange_openChart B S hS Z.hom V
  refine ⟨chartScheme W, SmallEtale.contains_chartScheme B S hS Z.left.1 W, fun O => ?_⟩
  obtain ⟨Q, gO, hgO⟩ := hW O
  obtain ⟨W', a, b, ⟨e⟩⟩ := exists_smallEtaleDirectImageChartEqualizerEquiv_of_presentation
    B S hS Z.hom ((sheafCompose (SmallEtale.topology B S hS Z.left.1)
      (CategoryTheory.forget RingCat.{u})).obj (structureRingSheaf B S hS Z.left))
    (openChart B S hS X.1 V O) gO hgO
  refine ((Cardinal.mk_congr e).trans_le
    (Cardinal.mk_le_of_injective Subtype.val_injective)).trans ?_
  refine (mk_sections_structureRingSheaf_le_two_pow_size B S hS Z.left
    (openChart B S hS Z.left.1 W Q)).trans ?_
  exact Cardinal.power_le_power_left two_ne_zero (Scheme.size_coe_opens_le (chartScheme W) Q)

/-- The sections of the integral closure of `𝒪_X` in a direct-image algebra over the Zariski
opens of a chart are bounded uniformly in the open: there is an object `T` of the site with
`#𝒪'(openChart V O) ≤ 2 ^ T.size` for every Zariski open `O` of `chartScheme V`. -/
theorem exists_contains_mk_sections_integralClosureSheaf_openChart_le
    {X : AlgebraicSpaces B S hS} (Z : Over X) (V : SmallEtale B S hS X.1) :
    ∃ T : Scheme.{u}, B.Contains T ∧ ∀ O : (chartScheme V).Opens,
      #(ToType ((AlgebraSheaf.integralClosureSheaf
          (pushforwardAlgebra B S hS Z)).right.obj.obj
        (op (openChart B S hS X.1 V O)))) ≤ 2 ^ T.size := by
  obtain ⟨T, hT, hbound⟩ :=
    exists_contains_mk_sections_pushforwardAlgebra_openChart_le B S hS Z V
  exact ⟨T, hT, fun O => (Cardinal.mk_le_of_injective
    (AlgebraSheaf.integralClosureInclusion_app_injective (pushforwardAlgebra B S hS Z)
      (op (openChart B S hS X.1 V O)))).trans (hbound O)⟩

/-- For a quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces, the relative
spectrum of the integral closure `𝒪'` of `𝒪_X` in `f_* 𝒪_Y` over a chart of `X` is an object of
the site. -/
theorem contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (V : SmallEtale B S hS X.1) :
    B.Contains (chartRelativeSpec B S hS X
      (AlgebraSheaf.integralClosureSheaf (pushforwardAlgebra B S hS (Over.mk f)))
      (AlgebraSheaf.isQuasicoherent_integralClosureSheaf _
        (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs)) V) := by
  obtain ⟨T, hT, hbound⟩ :=
    exists_contains_mk_sections_integralClosureSheaf_openChart_le B S hS (Over.mk f) V
  refine contains_chartRelativeSpec_of_lt_cutoff B S hS X _ _ V
    (max_lt (SmallEtale.contains_chartScheme B S hS X.1 V) (B.cutoff_isStrongPrelimit hT))
    (le_max_left _ _) fun O => (hbound (O : (chartScheme V).Opens)).trans (le_max_right _ _)

end AlgebraicGeometry.Space

end
