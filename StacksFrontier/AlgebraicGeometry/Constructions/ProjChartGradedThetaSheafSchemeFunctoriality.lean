module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntThetaSchemeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaBuild

/-!
# The sheaf-level `θ` of Stacks Tag 01NK is functorial in the scheme

For `j : T' ⟶ T` a morphism of schemes and `ψ'` a [Stacks, Tag 01NK] datum on `(T', j^*L)` whose
values are the pullbacks of the values of `ψ` — the hypothesis `hψ` that
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedPullback` carries throughout —
this file proves that the **sheaf-level** `θ` of `ψ'`, the morphism
`…ProjChartGradedThetaBuild.pushTheta` of sheaves of modules on `Proj 𝒜`, acts on the sections
over `D₊(f)` by pulling back `ψ`'s chart comparison.

This is the scheme-variable counterpart of
`…ProjChartGradedThetaSheafRingFunctoriality.pushTheta_comap_app_basicOpen`. With it the
functoriality ladder of the tag is complete for `θ` in **both** of its variables, which is what
the nested compatibility of the relative `θ` of [Stacks, Tag 01O9] consumes: the datum over an
affine `V` of the base is `…RelativeProjInvertibleMorphism.GradedPowerMap.affineDatum V` over the
graded ring `𝒜(V)`, so for `Z ≤ V` the comparison runs over two graded rings *and* two schemes.

## Main results

* `…chartOpen_eq_preimage`: **the chart open of the pulled-back datum is the preimage of the
  chart open**, `T'_{ψ'(f)} = j^{-1}(T_{ψ(f)})`, which is what makes the pullback of a section
  over the one a section over the other.
* `…pushTheta_app_basicOpen_pullback`: **`θ` for `ψ'` on the sections over `D₊(f)` is the pullback
  of `θ` for `ψ`**, read through the chart comparison on each side.

## Implementation notes

**Why `D₊(f)` suffices and no gluing argument is needed.**
`…ProjChartGradedThetaBuild.pushTheta_app_basicOpen` already computes `θ`'s action on the sections
over a standard open of a homogeneous element of positive degree by the chart comparison, and
those standard opens are a basis. So the content of the sheaf-level statement is exactly the
chart-level one — `…ProjChartGradedIntThetaSchemeFunctoriality.intChartSection_pullback`, in every
integer degree — plus the cancellation `CategoryTheory.Iso.inv_hom_id_apply`.

**Why the chart opens are compared by an equality and not transported.** Unlike the graded-ring
half, where the two chart opens are equal but live over different homogeneous spectra, here they
are opens of *different schemes*, and `chartOpen_eq_preimage` relates them exactly as
`…ProjChartIntDivisionPullback.intPullSectionOn` wants: an inclusion `V' ≤ j^{-1}(V)`. So nothing
is transported along an equality of objects.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection nonvanishingOpen_pullSection)
open Stacks.AlgebraicGeometry.ProjChartIntDivisionPullback (intPullSectionOn)
open Stacks.AlgebraicGeometry.ProjChartIntMulMapPullback (intCompare)
open Stacks.AlgebraicGeometry.ProjChartGradedIntThetaSchemeFunctoriality (intChartSection_pullback)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (pushTheta pushTheta_app_basicOpen)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedThetaSheafSchemeFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L)
  (ψ' : GradedSections 𝒜 ((Scheme.Modules.pullback j).obj L))
  (hψ : ∀ (n : ℕ) (a : 𝒜 n), ψ'.toFun n a = pullSection j L n (ψ.toFun n a))
  {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e)

include hψ hf he

/-- **The chart open of the pulled-back datum is the preimage of the chart open.** Both are
nonvanishing loci, by clause (1) of the tag (`…GradedSections.chartOpen_eq`) on each side; the
hypothesis `hψ` makes the one downstairs the nonvanishing locus of a pulled-back section, and
`…ProjChartRatioPullback.nonvanishingOpen_pullSection` computes that as the preimage. -/
public theorem chartOpen_eq_preimage : ψ'.chartOpen f = j ⁻¹ᵁ ψ.chartOpen f :=
  ((ψ'.chartOpen_eq hf he).trans
      ((congrArg (fun z => nonvanishingOpen T'
          (natTensorPow ((Scheme.Modules.pullback j).obj L) e) z) (hψ e ⟨f, hf⟩)).trans
        (nonvanishingOpen_pullSection j L e (ψ.toFun e ⟨f, hf⟩)))).trans
    (congrArg (fun V : T.Opens => j ⁻¹ᵁ V) (ψ.chartOpen_eq hf he).symm)

/-- **The sheaf-level `θ` of [Stacks, Tag 01NK] for the pulled-back datum, read on the sections
over `D₊(f)`, is the pullback of `ψ`'s chart comparison.**

This is the scheme-variable counterpart of
`…ProjChartGradedThetaSheafRingFunctoriality.pushTheta_comap_app_basicOpen`, and with it the
functoriality ladder of the tag is complete for `θ` in both of its variables.

The content is `…ProjChartGradedThetaBuild.pushTheta_app_basicOpen`, which computes `θ`'s action
on the sections over a standard open of a homogeneous element of positive degree by the chart
comparison, and then `…ProjChartGradedIntThetaSchemeFunctoriality.intChartSection_pullback` in
every integer degree. No cover argument is re-run: those standard opens are a basis, and the
chart-level statement is the whole content of the sheaf-level one. -/
public theorem pushTheta_app_basicOpen_pullback (n : ℤ)
    (s : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (ψ'.chartTargetIso n f).hom
        ((pushTheta 𝒜 ψ' n).app (AlgebraicGeometry.Proj.basicOpen 𝒜 f) s)
      = intPullSectionOn j L (intCompare j L) n (chartOpen_eq_preimage 𝒜 j ψ ψ' hψ hf he).le
          (intChartSection ψ hf (ψ.chartOpen_eq hf he).le he n
            (sectionsTwistEquivGradedPiece 𝒜 hf he n s)) := by
  refine Eq.trans (congrArg (ψ'.chartTargetIso n f).hom
    (pushTheta_app_basicOpen 𝒜 ψ' n ⟨⟨e, ⟨f, hf⟩⟩, he⟩ s)) ?_
  refine Eq.trans (CategoryTheory.Iso.inv_hom_id_apply _ _) ?_
  exact intChartSection_pullback j L ψ ψ' hψ hf (ψ.chartOpen_eq hf he).le
    (chartOpen_eq_preimage 𝒜 j ψ ψ' hψ hf he).le (ψ'.chartOpen_eq hf he).le he n
    (sectionsTwistEquivGradedPiece 𝒜 hf he n s)

end Stacks.AlgebraicGeometry.ProjChartGradedThetaSheafSchemeFunctoriality

end
