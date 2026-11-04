/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Ample
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.ChowConsumption
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# A projective embedding of the product of two H-projective schemes with a product twist

Let `U` be an affine scheme and `q₁ : Z₁ ⟶ U`, `q₂ : Z₂ ⟶ U` H-projective. The pullbacks
`𝒜 = j₁^*𝒪(1)` and `ℬ = j₂^*𝒪(1)` along the closed immersions `jᵢ : Zᵢ ⟶ ℙ^{nᵢ}_U` are ample
(Stacks 01PU), so `ℳ = pr₁^*𝒜 ⊗ pr₂^*ℬ` is ample on `Z₁ ×_U Z₂` (Stacks 0DNK), and some power
`ℳ^{⊗ e}` is the pullback of `𝒪(1)` along an immersion `i : Z₁ ×_U Z₂ ⟶ ℙᴺ_U` over `U`
(Stacks 01VS), which is a closed immersion because `Z₁ ×_U Z₂` is proper over `U`.

This is the projective embedding through which the graphs of the proof of Stacks 0DSQ are read
as points of the Hilbert scheme of `ℙᴺ_U`, with a twist that Riemann–Roch can evaluate on a graph.

## Main results

* `AlgebraicGeometry.ProjectivePairProductEmbedding.exists_isClosedImmersion_twist`.

## References

* [Stacks Project, Tag 01PU](https://stacks.math.columbia.edu/tag/01PU)
* [Stacks Project, Tag 0DNK](https://stacks.math.columbia.edu/tag/0DNK)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectivePairProductEmbedding

open Stacks.Ample Stacks.AmpleProjectiveImmersion Stacks.AmpleExternalTensor

/-- The pullback of `𝒪(1)` along a closed immersion into `ℙⁿ_U` over an affine `U` is ample. -/
private theorem isAmple_pullback_twistingSheaf {U Z : Scheme.{u}} [IsAffine U] {n : ℕ}
    (j : Z ⟶ projectiveSpaceOver n U) [IsClosedImmersion j] :
    IsAmple Z ((Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf n U)) :=
  (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp
    (Scheme.Modules.isAmple_pullback_of_isClosedImmersion j _
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
        (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf (n := n) (S := U))))

/-- **A closed immersion of `Z₁ ×_U Z₂` into `ℙᴺ_U` pulling `𝒪(1)` back to a power of an external
tensor product of invertible modules.** -/
theorem exists_isClosedImmersion_twist {U Z₁ Z₂ : Scheme.{u}} [IsAffine U] (q₁ : Z₁ ⟶ U)
    (q₂ : Z₂ ⟶ U) (hq₁ : IsProjectiveMorphism q₁) (hq₂ : IsProjectiveMorphism q₂) :
    ∃ (A : Z₁.Modules) (B : Z₂.Modules) (_ : IsInvertibleModule Z₁ A)
      (_ : IsInvertibleModule Z₂ B) (e : ℕ) (N : ℕ) (i : pullback q₁ q₂ ⟶ projectiveSpaceOver N U),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver N U ↘ U) = pullback.snd q₁ q₂ ≫ q₂ ∧
      Nonempty (tensorPowModule (pullback q₁ q₂) (externalTensor q₁ q₂ A B) (e : ℤ) ≅
        (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N U)) := by
  obtain ⟨a, j₁, hj₁, hj₁f⟩ := hq₁
  obtain ⟨b, j₂, hj₂, hj₂f⟩ := hq₂
  have := hj₁
  have := hj₂
  have hproper₁ : IsProper q₁ := isProper_of_isProjectiveMorphism q₁ ⟨a, j₁, hj₁, hj₁f⟩
  have hproper₂ : IsProper q₂ := isProper_of_isProjectiveMorphism q₂ ⟨b, j₂, hj₂, hj₂f⟩
  let A := (Scheme.Modules.pullback j₁).obj (projectiveSpaceTwistingSheaf a U)
  let B := (Scheme.Modules.pullback j₂).obj (projectiveSpaceTwistingSheaf b U)
  have : IsInvertibleModule Z₁ A := inferInstance
  have : IsInvertibleModule Z₂ B := inferInstance
  have hA := isAmple_pullback_twistingSheaf j₁
  have hB := isAmple_pullback_twistingSheaf j₂
  have hM : IsAmple (pullback q₁ q₂) (externalTensor q₁ q₂ A B) :=
    isAmple_externalTensor q₁ q₂ A B hA hB
  obtain ⟨d₀, -, hall⟩ := Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple
    (pullback.snd q₁ q₂ ≫ q₂) (externalTensor q₁ q₂ A B) hM
  obtain ⟨N, i, himm, hover, ⟨eL⟩⟩ := hall d₀ le_rfl
  have hover' : i ≫ (projectiveSpaceOver N U ↘ U) = pullback.snd q₁ q₂ ≫ q₂ := hover
  have : IsImmersion i := himm
  have : IsProper (i ≫ (projectiveSpaceOver N U ↘ U)) := by
    rw [hover']
    infer_instance
  have : IsSeparated (projectiveSpaceOver N U ↘ U) := inferInstance
  have : IsProper i := IsProper.of_comp i (projectiveSpaceOver N U ↘ U)
  exact ⟨A, B, inferInstance, inferInstance, d₀, N, i,
    isClosedImmersion_of_isImmersion_of_isProper i, hover', ⟨eL⟩⟩

end AlgebraicGeometry.ProjectivePairProductEmbedding

end
