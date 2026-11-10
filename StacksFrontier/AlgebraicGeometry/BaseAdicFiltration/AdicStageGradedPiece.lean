module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FunctorialGraded
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension

/-!
# The graded piece of an adic filtration is the ideal sheaf of one step of the adic tower

`Stacks.BaseAdicFiltration.adicStage` presents the `I`-adic filtration of a family
`p : U ⟶ Spec A` as a tower of closed subschemes `U₀ ⊆ U₁ ⊆ … ⊆ U` of `U`, with `Uₙ` cut out by
`Iⁿ⁺¹𝒪_U`; `Stacks.BaseAdicFiltration.gradedPiece` presents the same filtration as a chain of
subsheaves `Iⁿ(𝒪_U/Iⁿ⁺¹𝒪_U)` of the quotients. This file identifies the two: the ideal sheaf of
the step `Uₙ ⊆ Uₙ₊₁`, pushed forward to `U`, is the graded piece,

```
(ι_{n+1})_* ker(𝒪_{U_{n+1}} ⟶ (Uₙ ⊆ Uₙ₊₁)_* 𝒪_{U_n})  ≅  Iⁿ⁺¹(𝒪_U/Iⁿ⁺²𝒪_U).
```

## Main definitions

* `Stacks.Cohomology.FormalFunctions.pushforwardKernelUnitComparisonIso`: for a factorization
  `j ≫ w = v`, the direct image along `w` of the kernel of `𝒪_W ⟶ j_* 𝒪_V` is the kernel of the
  comparison `w_* 𝒪_W ⟶ v_* 𝒪_V`.
* `Stacks.Cohomology.FormalFunctions.kernelIdealPowerQuotientDropIso`: the kernels of the
  exponent-lowering maps of the quotients and of the closed subschemes of the powers of an ideal
  sheaf agree.
* `Stacks.Cohomology.FormalFunctions.pushforwardKernelIsoKernelIdealPowerQuotientDrop`: the ideal
  sheaf of one step of the tower of closed subschemes of the powers of an ideal sheaf, pushed
  forward, is the kernel of the exponent-lowering map of the quotients.
* `Stacks.BaseAdicFiltration.gradedPieceIsoKernelIdealPowerQuotientDrop`: the graded piece of
  an adic filtration is that same kernel.
* `Stacks.BaseAdicFiltration.pushforwardKernelAdicStageSuccIsoGradedPiece` and
  `Stacks.BaseAdicFiltration.pushforwardKernelImmersionStructureMapIsoGradedPiece`: the ideal
  sheaf of the step `Uₙ ⊆ Uₙ₊₁`, pushed forward to `U`, is the graded piece, with the
  structure-sheaf comparison written as `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit`
  and as `SheafOfModules.unitToPushforwardObjUnit` respectively.

## Main results

* `Stacks.BaseAdicFiltration.gradedShortComplex_g_eq_idealPowerQuotientDrop`: the second map of
  the filtration sequence is the exponent-lowering map.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Algebraization

universe u

namespace Stacks.Cohomology.FormalFunctions

/-! ### The kernel of the comparison of direct images of structure sheaves -/

section Comparison

variable {Z : Scheme.{u}}

/-- The comparison of direct images of structure sheaves along a factorization, written as the
direct image of the structure-sheaf comparison followed by an isomorphism. -/
theorem pushforwardUnitComparison_eq {W V : Scheme.{u}} (j : V ⟶ W) (w : W ⟶ Z) {v : V ⟶ Z}
    (hw : j ≫ w = v) :
    pushforwardUnitComparison (Z := Z) j w hw =
      (Scheme.Modules.pushforward w).map (Scheme.Modules.unitToPushforwardUnit j) ≫
        ((Scheme.Modules.pushforwardComp j w).hom.app (Scheme.unitModule V) ≫
          eqToHom (congrArg
            (fun f : V ⟶ Z => (Scheme.Modules.pushforward f).obj (Scheme.unitModule V)) hw)) :=
  rfl

/-- **The direct image of the ideal sheaf of a morphism is the kernel of the comparison.** For
`j ≫ w = v`, the direct image along `w` of the kernel of `𝒪_W ⟶ j_* 𝒪_V` is the kernel of
`w_* 𝒪_W ⟶ v_* 𝒪_V`. -/
def pushforwardKernelUnitComparisonIso {W V : Scheme.{u}} (j : V ⟶ W) (w : W ⟶ Z) {v : V ⟶ Z}
    (hw : j ≫ w = v) :
    (Scheme.Modules.pushforward w).obj
        (kernel (Scheme.Modules.unitToPushforwardUnit j)) ≅
      kernel (pushforwardUnitComparison (Z := Z) j w hw) :=
  haveI : PreservesLimits (Scheme.Modules.pushforward w) :=
    (Scheme.Modules.pullbackPushforwardAdjunction w).rightAdjoint_preservesLimits
  haveI : Mono ((Scheme.Modules.pushforwardComp j w).hom.app (Scheme.unitModule V) ≫
      eqToHom (congrArg
        (fun f : V ⟶ Z => (Scheme.Modules.pushforward f).obj (Scheme.unitModule V)) hw)) :=
    @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ (((Scheme.Modules.pushforwardComp j w).app
      (Scheme.unitModule V)).isIso_hom)) _ (@IsIso.mono_of_iso _ _ _ _ _ (eqToIso (congrArg
        (fun f : V ⟶ Z => (Scheme.Modules.pushforward f).obj (Scheme.unitModule V)) hw)).isIso_hom)
  PreservesKernel.iso (Scheme.Modules.pushforward w)
      (Scheme.Modules.unitToPushforwardUnit j) ≪≫
    (kernelCompMono (Scheme.Modules.pushforward w |>.map
        (Scheme.Modules.unitToPushforwardUnit j))
        ((Scheme.Modules.pushforwardComp j w).hom.app (Scheme.unitModule V) ≫
          eqToHom (congrArg
            (fun f : V ⟶ Z => (Scheme.Modules.pushforward f).obj (Scheme.unitModule V))
            hw))).symm ≪≫
      kernelIsoOfEq (pushforwardUnitComparison_eq j w hw).symm

end Comparison

/-! ### The tower of closed subschemes of the powers of an ideal sheaf -/

section Tower

variable {Z : Scheme.{u}} (J : Z.IdealSheafData) {n m : ℕ} (h : n ≤ m)

/-- **The kernels of the two exponent-lowering maps agree.** The kernel of
`Stacks.Algebraization.idealPowerQuotientDrop`, on the quotients of the structure sheaf, is
isomorphic to the kernel of `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeDrop`,
on the direct images of the structure sheaves of the closed subschemes. -/
def kernelIdealPowerQuotientDropIso :
    kernel (idealPowerQuotientDrop J h (Scheme.unitModule Z)) ≅
      kernel (idealPowerQuotientSubschemeDrop J h) :=
  kernel.mapIso (idealPowerQuotientDrop J h (Scheme.unitModule Z))
    (idealPowerQuotientSubschemeDrop J h)
    (idealPowerQuotientSubschemeIso J m) (idealPowerQuotientSubschemeIso J n)
    (idealPowerQuotientSubschemeIso_naturality J h)

/-- **The ideal sheaf of one step of the tower of closed subschemes, pushed forward, is the
kernel of the exponent-lowering map of the quotients.** For `n ≤ m`, the inclusion
`(𝓘ᵐ).subscheme ⊇ (𝓘ⁿ).subscheme` has an ideal sheaf; its direct image along
`(𝓘ᵐ).subschemeι` is the kernel of `𝒪_Z/𝓘ᵐ𝒪_Z ⟶ 𝒪_Z/𝓘ⁿ𝒪_Z`. -/
def pushforwardKernelIsoKernelIdealPowerQuotientDrop :
    (Scheme.Modules.pushforward (J ^ m).subschemeι).obj
        (kernel (Scheme.Modules.unitToPushforwardUnit
          (idealPowerSubschemeInclusion J h))) ≅
      kernel (idealPowerQuotientDrop J h (Scheme.unitModule Z)) :=
  pushforwardKernelUnitComparisonIso (idealPowerSubschemeInclusion J h) (J ^ m).subschemeι
      (Scheme.IdealSheafData.inclusion_subschemeι _) ≪≫
    (kernelIdealPowerQuotientDropIso J h).symm

end Tower

end Stacks.Cohomology.FormalFunctions

namespace Stacks.BaseAdicFiltration

open Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (n : ℕ)

/-! ### The graded piece as a kernel -/

/-- **The second map of the filtration sequence is the exponent-lowering map of the quotients.**
The map `ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iⁿℱ` of `Stacks.BaseAdicFiltration.gradedShortComplex` is
`Stacks.Algebraization.idealPowerQuotientDrop`. -/
theorem gradedShortComplex_g_eq_idealPowerQuotientDrop (F : U.Modules) [F.IsQuasicoherent] :
    (gradedShortComplex p I n F).g =
      idealPowerQuotientDrop (baseIdeal p I) (Nat.le_succ n) F := by
  have h : adicProj p I (n + 1) F ≫ (gradedShortComplex p I n F).g =
      adicProj p I (n + 1) F ≫ idealPowerQuotientDrop (baseIdeal p I) (Nat.le_succ n) F :=
    (adicProj_comp_gradedShortComplex_g p I n F).trans
      (idealPowerQuotientDrop_π (baseIdeal p I) (Nat.le_succ n) F).symm
  exact (cancel_epi (adicProj p I (n + 1) F)).1 h

/-- **The graded piece of an adic filtration is the kernel of the exponent-lowering map.** The
graded piece `Iⁿ(ℱ/Iⁿ⁺¹ℱ)` is the kernel of
`Stacks.Algebraization.idealPowerQuotientDrop : ℱ/Iⁿ⁺¹ℱ ⟶ ℱ/Iⁿℱ`. -/
def gradedPieceIsoKernelIdealPowerQuotientDrop (F : U.Modules) [F.IsQuasicoherent] :
    (gradedPiece p I n F).toSheafOfModules ≅
      kernel (idealPowerQuotientDrop (baseIdeal p I) (Nat.le_succ n) F) :=
  (gradedShortComplex_shortExact p I n F).fIsKernel.conePointUniqueUpToIso
      (limit.isLimit _) ≪≫
    kernelIsoOfEq (gradedShortComplex_g_eq_idealPowerQuotientDrop p I n F)

/-! ### The ideal sheaf of one step of the adic tower -/

/-- **The ideal sheaf of one step of the adic tower, pushed forward to the family, is the graded
piece of the adic filtration.**

The step `Uₙ ⊆ Uₙ₊₁` of the tower of closed subschemes cut out by the powers of `I 𝒪_U` is a
first-order thickening; its ideal sheaf is the kernel of the structure-sheaf comparison
`𝒪_{U_{n+1}} ⟶ (Uₙ ⊆ Uₙ₊₁)_* 𝒪_{U_n}`, and the direct image of that kernel along the immersion
`ι_{n+1} : U_{n+1} ⟶ U` is the graded piece `Iⁿ⁺¹(𝒪_U/Iⁿ⁺²𝒪_U)`. -/
def pushforwardKernelAdicStageSuccIsoGradedPiece :
    (Scheme.Modules.pushforward (adicStageι p I (n + 1))).obj
        (kernel (Scheme.Modules.unitToPushforwardUnit (adicStageSucc p I n))) ≅
      (gradedPiece p I (n + 1) (Scheme.unitModule U)).toSheafOfModules :=
  pushforwardKernelIsoKernelIdealPowerQuotientDrop (baseIdeal p I)
      (Nat.le_succ (n + 1)) ≪≫
    (gradedPieceIsoKernelIdealPowerQuotientDrop p I (n + 1) (Scheme.unitModule U)).symm

/-- **The ideal sheaf of one step of the adic tower is the graded piece, with the structure-sheaf
comparison written as `SheafOfModules.unitToPushforwardObjUnit`.** This is
`Stacks.BaseAdicFiltration.pushforwardKernelAdicStageSuccIsoGradedPiece` with the structure sheaf
written as `SheafOfModules.unit`. -/
def pushforwardKernelImmersionStructureMapIsoGradedPiece :
    (Scheme.Modules.pushforward (adicStageι p I (n + 1))).obj
        (kernel (C := (adicStage p I (n + 1)).Modules)
          (SheafOfModules.unitToPushforwardObjUnit
            (adicStageSucc p I n).toRingCatSheafHom)) ≅
      (gradedPiece p I (n + 1) (SheafOfModules.unit U.ringCatSheaf)).toSheafOfModules :=
  pushforwardKernelAdicStageSuccIsoGradedPiece p I n

end Stacks.BaseAdicFiltration

end
