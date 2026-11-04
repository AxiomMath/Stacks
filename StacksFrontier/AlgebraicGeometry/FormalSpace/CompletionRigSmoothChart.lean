module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleChart
public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Rig.RigSmoothAdicCompletionAscent

/-!
# The map of adic completions of a finite type algebra smooth off `V(I)` is rig-smooth

Let `φ : A → A'` be a finite type homomorphism of Noetherian rings, `I ⊆ A` an ideal, and assume
`Spec A' → Spec A` smooth over `Spec A ∖ V(I)`. Then the induced map `A^∧ → (A')^∧` of `I`-adic
completions, with their adic topologies, is a rig-smooth arrow of `WAdm^{Noeth}` in the sense of
**Stacks 0GCJ**.

This is the affine case of **Stacks 0GDH**: "By Lemma 0GAK we see that `(A')^∧` is rig-smooth over
`(A, I)` which in turn means that `A^∧ → (A')^∧` is rig-smooth". Part (1) of Stacks 0GAK is
`Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom`, and the passage from rig-smoothness over
`(A, I)` to rig-smoothness over `(A^∧, IA^∧)` is
`Rig.isRigSmoothOver_adicCompletion_of_isRigSmoothOver`. It is the rig-smooth counterpart of
`AlgebraicGeometry.FormalSpace.isRigEtaleHom_adicCompletionMap_of_isEtaleOutside`.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmoothArrow_adicCompletionMap_of_smoothAwayFrom`: the affine
  case of Stacks 0GDH.

## References

* [Stacks Project, Tag 0GAK](https://stacks.math.columbia.edu/tag/0GAK)
* [Stacks Project, Tag 0GCJ](https://stacks.math.columbia.edu/tag/0GCJ)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] adicCompletionModuleTopology
  isTopologicalRing_adicCompletionModuleTopology isLinearTopology_adicCompletionModuleTopology

variable {A A' : Type u} [CommRing A] [CommRing A'] [IsNoetherianRing A] [IsNoetherianRing A']

/-- **The affine case of Stacks 0GDH.** For a finite type homomorphism `φ : A → A'` of Noetherian
rings and an ideal `I ⊆ A` such that `Spec A' → Spec A` is smooth over `Spec A ∖ V(I)`, the
induced map of `I`-adic completions `A^∧ → (A')^∧` is a rig-smooth arrow of `WAdm^{Noeth}`. -/
theorem isRigSmoothArrow_adicCompletionMap_of_smoothAwayFrom (φ : A →+* A') (I : Ideal A)
    (hft : φ.FiniteType)
    (hφ : letI : Algebra A A' := φ.toAlgebra; Rig.SmoothAwayFrom A I A') :
    RingHom.IsRigSmoothArrow (adicCompletionMap φ I (I.map φ) le_rfl) := by
  intro _ _ _ _
  let : Algebra A A' := φ.toAlgebra
  have : Algebra.FiniteType A A' := hft
  set α := algebraMap A (AdicCompletion I A) with hα
  set g := adicCompletionMap φ I (I.map φ) le_rfl with hg
  -- rig-smoothness over the non-complete base, by part (1) of Stacks 0GAK
  have h0 := Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom I (B := A') hφ
  have hcomp : g.comp α = algebraMap A (Rig.adicCompletionObj I (B := A')).carrier := by
    rw [hg, adicCompletionMap_comp_algebraMap]
    rfl
  have hover : Rig.IsRigSmoothOver (g.comp α) I := by
    rw [hcomp]
    exact ⟨(Rig.adicCompletionObj I (B := A')).isAdicallyComplete,
      (Rig.adicCompletionObj I (B := A')).property.2, h0⟩
  -- rig-smoothness over the completed base, with its finite type data
  obtain ⟨hc, hf, hrig⟩ := Rig.isRigSmoothOver_adicCompletion_of_isRigSmoothOver g hover
  have hft' := finiteTypeAdicAlgebraForEveryIdeal_adicCompletionMap φ I hc hf
  have hdef : TopologicalRing.IsIdealOfDefinition (I.map α) :=
    isIdealOfDefinition_map_adicModuleTopology I (IsNoetherian.noetherian I)
  exact ⟨continuous_adicCompletionMap φ I (I.map φ) le_rfl, hft', I.map α, hdef, hrig⟩

end AlgebraicGeometry.FormalSpace

end
