module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.FiniteToNoetherian
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.IntegralToFinite
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Local
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effectivity along a surjective integral morphism reduces to a Noetherian affine base

Three reductions of the effectivity of quasi-compact separated étale descent are available: it
is Zariski-local on the base (`AlgebraicGeometry.qcSepEtaleEffective_of_isOpenCover`), over an
affine base an integral morphism may be replaced by the finite, finitely presented morphisms it
is a limit of (`AlgebraicGeometry.qcSepEtaleEffective_of_forall_isFinite_finitePresentation`),
and a finite, finitely presented morphism to an affine base may be replaced by its models over
the Noetherian affine stages of that base
(`AlgebraicGeometry.qcSepEtaleEffective_of_forall_isNoetherian`). Composing the three along an
affine open cover of the base reduces the effectivity half of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) to the single case of a finite
surjective morphism to an affine Noetherian scheme.

## Main results

* `AlgebraicGeometry.qcSepEtaleEffective_of_forall_isNoetherian_isFinite`: **effectivity of
  quasi-compact separated étale descent along a surjective integral morphism follows from
  effectivity along the finite surjective morphisms to affine Noetherian schemes.**

## Implementation notes

The hypothesis quantifies over the base as well as the source, because each of the three
reductions changes the base: the first to an affine open of it, the third to a Noetherian affine
scheme approximating that open. The second keeps the base and is applied after the first, so its
affineness hypothesis is met by the affine open.

## References

* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **Effectivity of quasi-compact separated étale descent along a surjective integral morphism
follows from effectivity along the finite surjective morphisms to affine Noetherian schemes.**
The base is covered by affine opens, over which the morphism is a limit of finite, finitely
presented surjective morphisms, each of which has a model over a Noetherian affine
approximation of that open. -/
@[sga "1 IX 4.7" "more general"]
theorem qcSepEtaleEffective_of_forall_isNoetherian_isFinite {S X : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [IsIntegralHom f]
    (H : ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
      Surjective g → QcSepEtaleEffective g) :
    QcSepEtaleEffective f := by
  refine qcSepEtaleEffective_of_isOpenCover f (fun U : S.affineOpens ↦ (U : S.Opens))
    (iSup_affineOpens_eq_top S) fun U ↦ ?_
  have : IsAffine (U : S.Opens).toScheme := U.2
  refine qcSepEtaleEffective_of_forall_isFinite_finitePresentation
    (pullback.snd f (U : S.Opens).ι) fun Y g hfin hfp hsurj ↦ ?_
  have := hfin
  have := hsurj
  exact qcSepEtaleEffective_of_forall_isNoetherian g hfp H

end AlgebraicGeometry

end
