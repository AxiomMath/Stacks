module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule

/-!
# The trace map of the right adjoint of pushforward

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes and let
`a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be the right adjoint of `Rf_*` of [Stacks, Tag 0A9E]. The counit
of the adjunction is the *trace map* `Tr_f : Rf_* ∘ a ⟶ id`, and the bijection
`Hom_X(L, a(K)) ⟶ Hom_Y(Rf_*L, K)` which characterizes the right adjoint is
`φ ↦ Tr_{f,K} ∘ Rf_*φ`. This is the opening of Section 48.4 of the Stacks project,
[Stacks, Tag 0AWG].

## Main definitions

* `Stacks.Duality.qcqsTrace` — the trace map `Tr_f : Rf_* ∘ a ⟶ id`.

## Main results

* `Stacks.Duality.qcqsTrace_app` — its component `Tr_{f,K} : Rf_*a(K) ⟶ K` is the counit of
  `Rf_* ⊣ a` at `K`.
* `Stacks.Duality.twistedInverseImageAdjunction_homEquiv_symm_qcqs` — the bijection
  `Hom_X(L, a(K)) ⟶ Hom_Y(Rf_*L, K)` of the adjunction is `φ ↦ Tr_{f,K} ∘ Rf_*φ`.

## Implementation notes

The right adjoint is `Stacks.Duality.twistedInverseImage` of the restriction of `Rf_*` formed with
part (1) of [Stacks, Tag 08D5] discharged
(`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs`), which is the spelling under
which [Stacks, Tag 0B6J] is stated in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChangeTrace.lean`. Its existence
is the instance
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`,
[Stacks, Tag 0A9E] for a morphism of quasi-compact quasi-separated schemes, so no adjointness is
assumed here. The derived categories are the locally small models, the only ones at which
[Stacks, Tag 0A9E] holds.

The map of Equation 48.3.0.1 obtained by composing with `Tr_{f,K}` is
`Stacks.Duality.sheafyTrace` ([Stacks, Tag 0B6H]).

## References

* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] (f : X ⟶ Y)

/-- **The trace map `Tr_f : Rf_* ∘ a ⟶ id`** of a morphism `f : X ⟶ Y` of quasi-compact and
quasi-separated schemes, where `a` is the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
([Stacks, Tag 0A9E]): the counit of the adjunction `Rf_* ⊣ a`. -/
@[stacks 0AWG "the trace map Tr_f : Rf_* ∘ a ⟶ id of a morphism of quasi-compact and \
quasi-separated schemes, the counit of the adjunction Rf_* ⊣ a of Tag 0A9E"]
def qcqsTrace :
    twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⋙
        quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⟶
      𝟭 _ :=
  (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit

/-- The component `Tr_{f,K} : Rf_*a(K) ⟶ K` of the trace map is the counit of `Rf_* ⊣ a` at
`K`. -/
theorem qcqsTrace_app (K : quasiCoherentDerivedCategory Y) :
    (qcqsTrace f).app K =
      (twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app K :=
  rfl

/-- **The trace map characterizes the right adjoint.** For a morphism `f : X ⟶ Y` of
quasi-compact and quasi-separated schemes, the bijection
`Hom_X(L, a(K)) ⟶ Hom_Y(Rf_*L, K)` of the adjunction `Rf_* ⊣ a` sends `φ` to
`Tr_{f,K} ∘ Rf_*φ`. -/
@[stacks 0AWG "the bijection Hom_X(L, a(K)) ⟶ Hom_Y(Rf_*L, K) characterizing the right adjoint \
is φ ↦ Tr_{f,K} ∘ Rf_*φ"]
theorem twistedInverseImageAdjunction_homEquiv_symm_qcqs (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y)
    (φ : L ⟶ (twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) :
    ((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv L K).symm φ =
      (quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map φ ≫
        (qcqsTrace f).app K :=
  (twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv_counit L K φ

end Stacks.Duality

end
