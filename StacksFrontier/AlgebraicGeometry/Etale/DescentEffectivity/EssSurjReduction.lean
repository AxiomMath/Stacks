module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.OpenInduction

/-!
# The essential-surjectivity half of Tag 0BTP, reduced to the Noetherian induction step

The fully faithful half of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) is
`AlgebraicGeometry.fullyFaithful_quasiCompactSeparatedEtaleDescentFunctor_of_isIntegralHom`.
Essential surjectivity, hence the equivalence, follows from the single step of the Noetherian
induction in `AlgebraicGeometry.qcSepEtaleEffective_of_exists_not_le`, over an affine Noetherian
base along a finite surjective morphism.

Three reductions bring the general case to that one
(`AlgebraicGeometry.qcSepEtaleEffective_of_forall_isNoetherian_isFinite`): Zariski-locality on
the base, writing an integral morphism over an affine base as a limit of finite finitely
presented ones, and replacing such a morphism by its models over the Noetherian affine stages of
the base. The induction itself needs no Noetherian hypothesis
(`AlgebraicGeometry.qcSepEtaleEffective_of_exists_not_le`): the supremum of *all* opens over
which the datum is effective is effective, so one effective open not contained in it is already
a contradiction.

## Main results

* `AlgebraicGeometry.essSurj_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le`:
  **essential surjectivity of the functor of Tag 0BTI along a surjective integral morphism,
  from the Noetherian induction step.**
* `AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le`:
  **Tag 0BTP in full, from the same step.**

## References

* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **Essential surjectivity of the functor of Tag 0BTI along a surjective integral morphism,
from the single step of the Noetherian induction.** The step is: over an affine Noetherian base,
along a finite surjective morphism, a quasi-compact separated étale descent datum effective over
a proper open of the base is effective over some open not contained in it. -/
theorem essSurj_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le
    (H : ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
      Surjective g → ∀ (D : DescentDatum g) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
        IsSeparated D.over.hom → ∀ U₀ : T.Opens, (D.baseDatum U₀).IsEtaleEffective → U₀ ≠ ⊤ →
          ∃ U : T.Opens, (D.baseDatum U).IsEtaleEffective ∧ ¬ U ≤ U₀)
    {S X : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsIntegralHom f] :
    (quasiCompactSeparatedEtaleDescentFunctor f).EssSurj :=
  essSurj_quasiCompactSeparatedEtaleDescentFunctor f <|
    qcSepEtaleEffective_of_forall_isNoetherian_isFinite f fun T Y g hT hTN hg hgs ↦
      qcSepEtaleEffective_of_exists_not_le g (H T Y g hT hTN hg hgs)

/-- **Tag 0BTP in full, from the single step of the Noetherian induction.** Given the step `H` of
`essSurj_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le`, the functor of Tag 0BTI
along a surjective integral morphism is an equivalence. -/
theorem isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le
    (H : ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
      Surjective g → ∀ (D : DescentDatum g) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
        IsSeparated D.over.hom → ∀ U₀ : T.Opens, (D.baseDatum U₀).IsEtaleEffective → U₀ ≠ ⊤ →
          ∃ U : T.Opens, (D.baseDatum U).IsEtaleEffective ∧ ¬ U ≤ U₀)
    {S X : Scheme.{u}} (f : X ⟶ S) [Surjective f] [IsIntegralHom f] :
    (quasiCompactSeparatedEtaleDescentFunctor f).IsEquivalence :=
  have := essSurj_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le H f
  isEquivalence_quasiCompactSeparatedEtaleDescentFunctor f

end AlgebraicGeometry

end
