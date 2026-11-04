module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectivityLocusChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsLocallyProjective

/-!
# Tensor powers of an invertible module on an algebraic space, read on a scheme over it

Let `X` be an algebraic space over a scheme `S` of a big fppf site and `𝓛` an invertible
`𝒪_X`-module. Its tensor powers `𝓛^{⊗ n}` (`n ≥ 0`) are the iterated tensor products of the
monoidal structure of Stacks 01CA. This file records that they are compatible with inverse
images along morphisms of algebraic spaces and with the restriction of a module on a represented
space `h_U` to the Zariski site of the underlying scheme, where they become the tensor powers
`Stacks.Ample.tensorPowModule` of the ampleness theory of schemes.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackNatTensorPowIso`: `f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.TensorPowers (natTensorPow)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-- **Inverse images commute with the tensor powers.** For a morphism `f : X ⟶ Y` of algebraic
spaces and an `𝒪_Y`-module `𝓛`, `f^*(𝓛^{⊗ n}) ≅ (f^*𝓛)^{⊗ n}`, from Stacks 03EL and the
comparison `f^*𝒪_Y ≅ 𝒪_X`. -/
def modulePullbackNatTensorPowIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS Y.1 Y.2).obj (structureRingPresheaf_isSheaf B S hS Y.1 Y.2))) :
    (n : ℕ) → (modulePullback B S hS f).obj (natTensorPow (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS Y.1 Y.2).obj (structureRingPresheaf_isSheaf B S hS Y.1 Y.2))) L n) ≅
      natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2)))
        ((modulePullback B S hS f).obj L) n
  | 0 => (modulePullback B S hS f).mapIso
        (AlgebraicGeometry.SheafOfModules.unitIso _ (structureRingPresheaf_isSheaf B S hS Y.1 Y.2))
            ≪≫
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
        (smallEtaleRingedToposModulesHom B S hS f)).symm ≪≫
      (AlgebraicGeometry.SheafOfModules.unitIso _ (structureRingPresheaf_isSheaf B S hS X.1
          X.2)).symm
  | n + 1 => (modulePullback B S hS f).mapIso
        (AlgebraicGeometry.SheafOfModules.tensorIso _ (structureRingPresheaf_isSheaf B S hS Y.1 Y.2)
          (natTensorPow L n) L) ≪≫
      (Stacks.SheafOfModules.pullbackTensorIso
        (smallEtaleRingedToposModulesHom B S hS f)).app
          (natTensorPow (C := SheafOfModules.{u}
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            (structureSheaf B S hS Y.1 Y.2).obj (structureRingPresheaf_isSheaf B S hS Y.1 Y.2))) L
                n, L) ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
        (modulePullbackNatTensorPowIso f L n)).app ((modulePullback B S hS f).obj L) ≪≫
      (AlgebraicGeometry.SheafOfModules.tensorIso _ (structureRingPresheaf_isSheaf B S hS X.1 X.2)
        _ _).symm

section Represented

variable (U : BigFppfOver B S hS)

/-- **Restriction to the Zariski site of the represented scheme commutes with the tensor
powers.** For a quasi-coherent module `𝓜` on `h_U` all of whose tensor powers are quasi-coherent,
the restriction of `𝓜^{⊗ n}` to the Zariski site of the underlying scheme `W` is the `n`th tensor
power of the restriction of `𝓜`. Each step is the compatibility of the restriction with the
tensor product of two quasi-coherent modules,
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`. -/
def restrictToChartSchemeNatTensorPowIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))))
    (hM : SheafOfModules.IsQuasicoherentOnSite M)
    (hpow : ∀ k : ℕ, SheafOfModules.IsQuasicoherentOnSite (natTensorPow (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))) M
          k)) :
    (n : ℕ) → restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (natTensorPow (C := SheafOfModules.{u}
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))) M
          n) (idEtaleChart B S hS U) ≅
      natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (chartScheme (idEtaleChart B S hS U)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme
            (idEtaleChart B S hS U)))))
        (restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) M
          (idEtaleChart B S hS U)) n
  | 0 => (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (idEtaleChart B S hS U)).mapIso
        (AlgebraicGeometry.SheafOfModules.unitIso _
          (structureRingPresheaf_isSheaf B S hS (yoneda.obj U)
              (isAlgebraicSpace_yoneda B S hS U))) ≪≫
      restrictToChartSchemeUnitIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (idEtaleChart B S hS U) ≪≫
      (AlgebraicGeometry.SheafOfModules.unitIso _
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
          (chartScheme (idEtaleChart B S hS U)))).symm
  | n + 1 => (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (idEtaleChart B S hS U)).mapIso
        (AlgebraicGeometry.SheafOfModules.tensorIso _
          (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
          (natTensorPow (C := SheafOfModules.{u}
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))) M
          n) M ≪≫
        (modulesTensorObjIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          (natTensorPow (C := SheafOfModules.{u}
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))) M
          n) M).symm) ≪≫
      restrictToChartSchemeIdEtaleChartTensorIso B S hS U (natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))) M
          n) M (hpow n) hM ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
        (restrictToChartSchemeNatTensorPowIso M hM hpow n)).app _ ≪≫
      (AlgebraicGeometry.SheafOfModules.tensorIso _
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
          (chartScheme (idEtaleChart B S hS U))) _ _).symm

end Represented

/-- Every tensor power of an invertible module on an algebraic space is invertible. -/
private theorem isInvertible_natTensorPow {X : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) M] (k : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2)
      (natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2))) M k) :=
  inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible _ _
    (AlgebraicGeometry.SheafOfModules.tensorPow (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) M (k : ℤ)))

/-- Every tensor power of an invertible module on an algebraic space is quasi-coherent: it is
invertible, hence finite locally free (Stacks 0B8Q). -/
theorem isQuasicoherentOnSite_natTensorPow_of_isInvertible {X : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) M] (k : ℕ) :
    SheafOfModules.IsQuasicoherentOnSite
      (natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2))) M k) :=
  isQuasicoherentOnSite_of_isInvertible B S hS X _
    (isInvertible_natTensorPow M k)

/-- Every tensor power of an invertible module on an algebraic space is of finite type: it is
invertible, hence finite locally free (Stacks 0B8Q), hence of finite presentation. -/
theorem isFiniteTypeOnSite_natTensorPow {X : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) M] (k : ℕ) :
    SheafOfModules.IsFiniteTypeOnSite
      (natTensorPow (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2))) M
            k) := by
  have hfree := (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X
    (natTensorPow (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (structureSheaf B S hS X.1 X.2).obj (structureRingPresheaf_isSheaf B S hS X.1 X.2))) M k)
    (isInvertible_natTensorPow M k)).isFiniteLocallyFreeOnSite
  have hfp := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hfree
  exact ⟨fun U => by
    obtain ⟨I, V, f, hf, h⟩ := hfp.locally_hasFiniteGlobalPresentation U
    exact ⟨I, V, f, hf, fun i => (h i).hasFiniteGlobalGenerators⟩⟩

section Chart

variable (U : BigFppfOver B S hS)

/-- The quasi-coherent `𝒪_W`-module corresponding to a quasi-coherent module `𝓠` on `h_U` is the
restriction of `𝓠` to the Zariski site of `W`. -/
def chartInverseObjIso
    (Q : QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj Q).obj ≅
      restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) Q.obj
        (idEtaleChart B S hS U) :=
  (restrictToChartSchemeRepresentedAssociatedModuleIso B S hS U _
      ((representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj Q).property).symm ≪≫
    (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso
      ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
          U).counitIso.app Q))

end Chart

/-- **The chart-scheme module of a tensor power is the tensor power of the base change.** For an
invertible module `𝓛` on an algebraic space `Z` and a scheme point `w : h_U ⟶ Z`, the
quasi-coherent `𝒪_W`-module corresponding to `w^*(𝓛^{⊗ n})` is the `n`th tensor power of the base
change of `𝓛` to `U`. -/
def natTensorPowIsoChartSchemeTarget {Z : AlgebraicSpaces B S hS}
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)))
    [AlgebraicGeometry.SheafOfModules.IsInvertible (structureSheaf B S hS Z.1 Z.2).obj
      (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L]
    {U : BigFppfOver B S hS} (w : yoneda.obj U ⟶ Z.1)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
      (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
      ((modulePullback B S hS (chartSpaceMap w)).obj L)]
    (n : ℕ) :
    natTensorPow (C := SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        (chartScheme (idEtaleChart B S hS U)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (chartScheme
            (idEtaleChart B S hS U)))))
        (baseChangeModule B S hS L U w) n ≅
      chartSchemeTarget (𝓕 := natTensorPow (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          (structureSheaf B S hS Z.1 Z.2).obj (structureRingPresheaf_isSheaf B S hS Z.1 Z.2))) L n)
        (h𝓕 := isQuasicoherentOnSite_natTensorPow_of_isInvertible L n) w :=
  (restrictToChartSchemeNatTensorPowIso U ((modulePullback B S hS (chartSpaceMap w)).obj L)
      (isQuasicoherentOnSite_of_isInvertible B S hS _ _
        (inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible
          (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).obj
          (structureRingPresheaf_isSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
          ((modulePullback B S hS (chartSpaceMap w)).obj L))))
      (isQuasicoherentOnSite_natTensorPow_of_isInvertible _) n).symm ≪≫
    (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso (modulePullbackNatTensorPowIso (chartSpaceMap w) L n).symm ≪≫
    (chartInverseObjIso U (@chartPullbackQcoh B S hS Z U w _
      (isQuasicoherentOnSite_natTensorPow_of_isInvertible L n))).symm

end AlgebraicGeometry.Space

end
