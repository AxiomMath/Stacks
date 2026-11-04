module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RetrocompactOpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Quasi-coherence of direct images in the formal glueing situation

In the formal glueing situation of Stacks 0AEV, with `f : Y ⟶ X`, the open immersions
`j : U ⟶ X` and `j' : V ⟶ Y`, and the closed subspace `Z` of `X` of finite presentation, the
three morphisms `f`, `j` and `f ∘ j'` are quasi-compact and quasi-separated, so direct images
along them preserve quasi-coherence (Stacks 03M9), and kernels of morphisms of quasi-coherent
`𝒪_X`-modules are quasi-coherent (Stacks 03M1). All declarations below are in the namespace
`AlgebraicGeometry.Space.FormalGlueingSituation`.

## Main results

* `modulePushforwardPreservesQuasicoherence_ambientMorphism`,
  `modulePushforwardPreservesQuasicoherence_openImmersion` and
  `modulePushforwardPreservesQuasicoherence_overlapImmersion`: direct images along `f`, `j` and
  `f ∘ j'` preserve quasi-coherence.
* `hasQuasicoherentKernels_spaceX`: the kernel of a morphism of quasi-coherent `𝒪_X`-modules is
  quasi-coherent.
* `isQuasiCompact_openImmersion`, `isQuasiCompact_openImmersionOver`,
  `isQuasiCompact_overlapImmersion`, `isQuasiSeparated_openImmersion`,
  `isQuasiSeparated_openImmersionOver` and `isQuasiSeparated_overlapImmersion`: the morphisms
  `j`, `j'` and `f ∘ j'` are quasi-compact and quasi-separated.
* `isClosedSubspace_preimage_Z` and `isFinitePresentation_ι_preimage_Z`: the inverse image
  `f⁻¹(Z)` is a closed subspace of `Y` whose inclusion is of finite presentation.

## References

* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- **Stacks 03M9 for `f : Y ⟶ X`.** In the formal glueing situation of Stacks 0AEV the direct
image along `f` of a quasi-coherent `𝒪_Y`-module is quasi-coherent. -/
theorem modulePushforwardPreservesQuasicoherence_ambientMorphism :
    ModulePushforwardPreservesQuasicoherence B S hS D.ambientMorphism :=
  fun F hF => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.ambientMorphism
    D.quasiCompact_f D.quasiSeparated_f F hF

/-- The kernel of a morphism of quasi-coherent `𝒪_X`-modules on the ambient space `X` of the
formal glueing situation is quasi-coherent. -/
theorem hasQuasicoherentKernels_spaceX :
    HasQuasicoherentKernels B S hS D.spaceX.1 D.spaceX.2 :=
  fun φ hM hN => @isQuasicoherentOnSite_kernel_of_quasicoherent B S hS D.spaceX.1 D.spaceX.2
    _ _ φ hM hN

/-! ### Quasi-compactness and quasi-separatedness of the two open immersions -/

/-- The open immersion `j : U ⟶ X` is quasi-compact. -/
theorem isQuasiCompact_openImmersion :
    IsQuasiCompact B S hS D.openImmersion.hom :=
  isQuasiCompact_ι_openComplement_of_isFinitePresentation B S hS D.algebraicSpace_X D.Z
    D.closed_Z D.finitePresentation_Z

/-- The inverse image `f⁻¹(Z)` is a closed subspace of `Y`. -/
theorem isClosedSubspace_preimage_Z : IsClosedSubspace B S hS (D.Z.preimage D.f) :=
  isClosedSubspace_preimage B S hS D.f D.Z D.algebraicSpace_X D.algebraicSpace_Y D.closed_Z

/-- The inclusion of `f⁻¹(Z)` is of finite presentation, being the base change along `f` of the
inclusion of `Z`. -/
theorem isFinitePresentation_ι_preimage_Z :
    IsFinitePresentation B S hS (D.Z.preimage D.f).ι :=
  IsFinitePresentation.of_isPullback B S hS D.isClosedSubspace_preimage_Z.1 D.closed_Z.1
    D.algebraicSpace_Y D.algebraicSpace_X (Subfunctor.isPullback_preimage D.f D.Z)
    D.finitePresentation_Z

/-- The open immersion `j' : V ⟶ Y` is quasi-compact. -/
theorem isQuasiCompact_openImmersionOver :
    IsQuasiCompact B S hS D.openImmersionOver.hom := by
  show IsQuasiCompact B S hS D.V.ι
  rw [D.V_eq_openComplement_preimage]
  exact isQuasiCompact_ι_openComplement_of_isFinitePresentation B S hS D.algebraicSpace_Y _
    D.isClosedSubspace_preimage_Z D.isFinitePresentation_ι_preimage_Z

/-- The open immersion `j : U ⟶ X` is quasi-separated. -/
theorem isQuasiSeparated_openImmersion :
    IsQuasiSeparated B S hS D.openImmersion.hom :=
  isQuasiSeparated_of_mono B S hS D.U.ι inferInstance

/-- The open immersion `j' : V ⟶ Y` is quasi-separated. -/
theorem isQuasiSeparated_openImmersionOver :
    IsQuasiSeparated B S hS D.openImmersionOver.hom :=
  isQuasiSeparated_of_mono B S hS D.V.ι inferInstance

/-- The morphism `f ∘ j' : V ⟶ X` is quasi-compact. -/
theorem isQuasiCompact_overlapImmersion :
    IsQuasiCompact B S hS D.overlapImmersion.hom :=
  isQuasiCompact_comp B S hS D.algebraicSpace_Y D.algebraicSpace_X D.V.ι D.f
    D.isQuasiCompact_openImmersionOver D.quasiCompact_f

/-- The morphism `f ∘ j' : V ⟶ X` is quasi-separated. -/
theorem isQuasiSeparated_overlapImmersion :
    IsQuasiSeparated B S hS D.overlapImmersion.hom :=
  isQuasiSeparated_comp B S hS D.isOpenSubspace_V.1 D.algebraicSpace_Y D.V.ι D.f
    D.isQuasiSeparated_openImmersionOver D.quasiSeparated_f

/-! ### Stacks 03M9 for the remaining two morphisms of the glueing square -/

/-- **Stacks 03M9 for `j : U ⟶ X`.** The direct image along `j` of a quasi-coherent
`𝒪_U`-module is quasi-coherent. -/
theorem modulePushforwardPreservesQuasicoherence_openImmersion :
    ModulePushforwardPreservesQuasicoherence B S hS D.openImmersion :=
  fun F hF => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.openImmersion
    D.isQuasiCompact_openImmersion D.isQuasiSeparated_openImmersion F hF

/-- **Stacks 03M9 for `f ∘ j' : V ⟶ X`.** The direct image along `f ∘ j'` of a quasi-coherent
`𝒪_V`-module is quasi-coherent. -/
theorem modulePushforwardPreservesQuasicoherence_overlapImmersion :
    ModulePushforwardPreservesQuasicoherence B S hS D.overlapImmersion :=
  fun F hF => isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS D.overlapImmersion
    D.isQuasiCompact_overlapImmersion D.isQuasiSeparated_overlapImmersion F hF

end AlgebraicGeometry.Space.FormalGlueingSituation

end
