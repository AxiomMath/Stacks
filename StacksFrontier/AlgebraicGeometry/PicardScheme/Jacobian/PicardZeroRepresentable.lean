module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.HilbertChart
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.TranslatedCharts

/-!
# `Pic⁰` of a curve with a rational point is a group scheme (Stacks 0B9Z, 0BA0)

This file applies the group-scheme criterion
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor` ([Stacks, Tag 0B9Q]) to the
degree-zero rigidified Picard functor `Pic⁰_{X/k,σ}` of a proper smooth curve `X` over a field
`k` with a rational point `σ`, as in the proof of [Stacks, Tag 0B9Z]:

* condition (1), the Zariski sheaf property, is `Stacks.RigidifiedPicard.isSheaf_functorZero`;
* condition (2)(a), representability of the chart, is
  `Stacks.RigidifiedPicard.exists_representableBy_cohomologySubfunctorZero` ([Stacks, Tag 0B9X]);
* condition (2)(b), openness of the chart, is
  `Stacks.RigidifiedPicard.isOpenImmersion_presheaf_cohomologySubfunctorZero`
  ([Stacks, Tag 0B9V]);
* condition (2)(c), the translates meet every field point, is [Stacks, Tag 0B9Y].

The chart is the translate by a class `θ` of degree `g` of the source's chart (the source
represents all of `Pic_{X/k,σ}` and then cuts out `Pic⁰`; representing `Pic⁰` directly is the
same argument with the chart translated). Every property of the chart which is local on the
source — smoothness in particular — passes to the group scheme
(`AlgebraicGeometry.of_chart_of_isZariskiLocalAtSource`).

The inputs are hypotheses here: the two halves of [Stacks, Tag 0B91] (`h0B91`, `hbc`), which the
library proves as `ProperFlatFibreEulerCharacteristic.perfectDerivedPushforward` and
`ProperFlatFibreEulerCharacteristic.baseChangeDerivedPushforward`; the claim in the proof of
[Stacks, Tag 0B9X] (`hexists`, `huniq`); and [Stacks, Tag 0B9Y] in the form needed (`hfield`).
No Stacks attribute is attached.

## Main results

* `Stacks.RigidifiedPicard.exists_grp_iso_functorZero` — the group scheme, with every property
  local on the source that the chart has.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f]
  [LocallyOfFinitePresentation f] [IsProper f] [SmoothOfRelativeDimension 1 f]
  [LocallyOfFiniteType f] (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- **`Pic⁰_{X/k,σ}` is represented by a group scheme**, given the inputs listed in the module
documentation; every property local on the source which the chart `W ⊆ Hilb^g` has, so has the
group scheme. -/
theorem exists_grp_iso_functorZero
    (hOiso : ∀ U : Over (Spec (.of k)), IsIso (bcProj f U).toLRSHom.toHom.c)
    (h0B91 : PerfectDerivedPushforward.{u}) (hbc : BaseChangeDerivedPushforward.{u})
    (θ : Stacks.Picard.ofScheme X) {g : ℕ}
    (hθ : ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = g) {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H g)
    (hexists : ∀ (T : Over (Spec (.of k))) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T g) (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over (Spec (.of k))) (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T g),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z')
    (hfield : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op (fieldExtensionPoint k K))),
      ∃ r : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of k))))),
        (functorZero f hdim σ hσ).map (Over.homMk (fieldExtensionPoint k K).hom).op r * c ∈
          (cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ).obj (op (fieldExtensionPoint k K))) :
    ∃ A : Grp (Over (Spec (.of k))), Nonempty (yonedaGrp.obj A ≅ functorZero f hdim σ hσ) ∧
      ∀ (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P], P H.hom → P A.X.hom := by
  obtain ⟨W, ⟨R⟩⟩ := exists_representableBy_cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ hH
    hθ hexists huniq
  have hopen := isOpenImmersion_presheaf_cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ
  obtain ⟨A, ⟨e⟩⟩ := exists_grp_iso_of_representable_openSubfunctor k (functorZero f hdim σ hσ)
    (isSheaf_functorZero f hdim σ hσ hOiso) _ ⟨_, ⟨R⟩⟩ hopen hfield
  refine ⟨A, ⟨e⟩, fun P _ hPH => ?_⟩
  have hPW : P (Over.mk (W.ι ≫ H.hom)).hom := IsZariskiLocalAtSource.comp hPH W.ι
  exact of_chart_of_isZariskiLocalAtSource A e P _ _ (Functor.representableByEquiv R) hopen
    hfield hPW

end Stacks.RigidifiedPicard

end
