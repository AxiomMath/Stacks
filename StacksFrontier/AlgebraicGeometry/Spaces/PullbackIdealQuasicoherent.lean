module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer

/-!
# The inverse image of a quasi-coherent sheaf of ideals is quasi-coherent

Let `f : Y ⟶ X` be a representable morphism of algebraic spaces over a scheme `S` and let
`ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals.  The inverse-image ideal `f⁻¹ℐ · 𝒪_Y`
(`AlgebraicGeometry.Space.pullbackIdealSubsheaf`), the smallest sheaf of ideals of `𝒪_Y`
containing the pullbacks `f♯(a)` of the sections `a` of `ℐ`, is quasi-coherent.

The reason is that it is the image of the adjoint `f^*ℐ ⟶ 𝒪_Y` of the composite
`ℐ ⟶ 𝒪_X ⟶ f_*𝒪_Y`: the source `f^*ℐ` is quasi-coherent by Stacks 03GA, so the image, the
kernel of a morphism from `𝒪_Y` to the cokernel of a morphism of quasi-coherent modules, is
quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.pullbackIdealSubsheaf_eq_ker_cokernel`: the inverse-image ideal is
  the image of the adjoint `f^*ℐ ⟶ 𝒪_Y` of `ℐ ⟶ f_*𝒪_Y`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_pullbackIdealSubsheaf`: **the inverse image of
  a quasi-coherent sheaf of ideals is quasi-coherent.**

## Implementation notes

The direct image is `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, which is the
direct image of sheaves of modules `SheafOfModules.pushforward` along the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp`; its sections over a chart `Q` of `X` are the
sections over the base-changed chart `Q ×_X Y`, so the morphism `𝒪_X ⟶ f_*𝒪_Y` is
`SheafOfModules.unitToPushforwardObjUnit`, which is `f♯` on sections.  Its left adjoint
`SheafOfModules.pullback` is isomorphic to the inverse image of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackChartIso`), which is how Stacks 03GA reaches it.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0GF8](https://stacks.math.columbia.edu/tag/0GF8)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)

variable (I : (SheafOfModules.unit (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)

/-- The composite `ℐ ⟶ 𝒪_X ⟶ f_*𝒪_Y`, which is `f♯` on sections. -/
def idealToPushforwardUnit :
    I.toSheafOfModules ⟶ (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f hf)).obj
      (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2)) :=
  I.ι ≫ SheafOfModules.unitToPushforwardObjUnit (smallBaseChangeSharp B S hS f hf)

/-- On sections over a chart `Q` of `X`, `idealToPushforwardUnit` sends a section `a` of `ℐ` to
its pullback `chartIdealPullbackHom B S hS f hf Q a`. -/
theorem idealToPushforwardUnit_val_app (Q : SmallEtale B S hS X.1)
    (a : I.toSheafOfModules.val.obj (op Q)) :
    (idealToPushforwardUnit B S hS f hf I).val.app (op Q) a =
      chartIdealPullbackHom B S hS f hf Q a.1 :=
  rfl

/-- The adjoint `f^*ℐ ⟶ 𝒪_Y` of `ℐ ⟶ f_*𝒪_Y`. -/
def pullbackIdealToUnit :
    (SheafOfModules.pullback.{u} (smallBaseChangeSharp B S hS f hf)).obj I.toSheafOfModules ⟶
      SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2) :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallBaseChangeSharp B S hS f hf)).homEquiv _ _).symm (idealToPushforwardUnit B S hS f hf I)

/-- `ℐ ⟶ f_*𝒪_Y` is the unit of the adjunction followed by the direct image of its adjoint. -/
theorem idealToPushforwardUnit_eq :
    idealToPushforwardUnit B S hS f hf I =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallBaseChangeSharp B S hS f hf)).unit.app I.toSheafOfModules ≫
      (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f hf)).map
        (pullbackIdealToUnit B S hS f hf I) := by
  rw [pullbackIdealToUnit]
  exact (((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallBaseChangeSharp B S hS f hf)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)).symm

/-- **The inverse-image ideal is the image of `f^*ℐ ⟶ 𝒪_Y`**, the kernel of the cokernel of
the adjoint of `ℐ ⟶ f_*𝒪_Y`.

The image contains the pullback `f♯(a)` of a section `a` of `ℐ` over a chart `Q` of `X`, since
over `Q ×_X Y` that is the value of the adjoint on the image of `a` under the unit of the
adjunction.  Conversely the adjoint factors through the inverse-image ideal because its adjoint
`ℐ ⟶ f_*𝒪_Y` does, on sections; and a submodule is the kernel of its cokernel. -/
theorem pullbackIdealSubsheaf_eq_ker_cokernel :
    pullbackIdealSubsheaf B S hS f hf I =
      SheafOfModules.Submodule.ker (cokernel.π (pullbackIdealToUnit B S hS f hf I)) := by
  set θ := pullbackIdealToUnit B S hS f hf I with hθ
  set P := pullbackIdealSubsheaf B S hS f hf I
  set adj := SheafOfModules.pullbackPushforwardAdjunction.{u} (smallBaseChangeSharp B S hS f hf)
  refine le_antisymm (pullbackIdealSubsheaf_le B S hS f hf I fun Q a ha => ?_) ?_
  · show _ = (0 : (cokernel θ).val.obj _)
    have h := idealToPushforwardUnit_val_app B S hS f hf I Q ⟨a, ha⟩
    rw [idealToPushforwardUnit_eq] at h
    rw [← h]
    show (θ ≫ cokernel.π θ).val.app _ _ = 0
    rw [cokernel.condition]
    rfl
  · -- the adjoint factors through `P`
    have hc : θ ≫ cokernel.π P.ι = 0 := by
      have h0 : idealToPushforwardUnit B S hS f hf I ≫
          (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f hf)).map
            (cokernel.π P.ι) = 0 := by
        ext Q a
        show (cokernel.π P.ι).val.app _ (P.ι.val.app _
          ⟨chartIdealPullbackHom B S hS f hf Q.unop a.1,
            chartIdealPullbackHom_mem_pullbackIdealSubsheaf B S hS f hf I Q.unop a.2⟩) = 0
        show (P.ι ≫ cokernel.π P.ι).val.app _ _ = 0
        rw [cokernel.condition]
        rfl
      have h1 := Adjunction.homEquiv_naturality_right_symm adj
        (idealToPushforwardUnit B S hS f hf I) (cokernel.π P.ι)
      rw [h0] at h1
      rw [hθ, pullbackIdealToUnit, ← h1, Adjunction.homEquiv_counit, Functor.map_zero,
        zero_comp]
    -- so the kernel of the cokernel of `θ` lies in `P`
    intro W x hx
    have hx' : (cokernel.π P.ι).val.app W x = 0 := by
      rw [← cokernel.π_desc θ (cokernel.π P.ι) hc]
      show (cokernel.desc θ (cokernel.π P.ι) hc).val.app W
        ((cokernel.π θ).val.app W x) = 0
      rw [(SheafOfModules.Submodule.mem_ker _ W x).1 hx, map_zero]
    let k := SheafOfModules.Submodule.ker (cokernel.π P.ι)
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π P.ι) (cokernel.condition P.ι)) (cokernelIsCokernel P.ι))
      k.ι (SheafOfModules.Submodule.ker_ι_comp _)
    have hxk : x ∈ k.obj W := hx'
    have hxl : P.ι.val.app W (l.val.app W ⟨x, hxk⟩) = x := by
      show (l ≫ P.ι).val.app W ⟨x, hxk⟩ = x
      rw [show l ≫ P.ι = k.ι from hl]
      rfl
    rw [← hxl]
    exact (l.val.app W ⟨x, hxk⟩).2

/-- **The inverse image of a quasi-coherent sheaf of ideals is quasi-coherent.**  For a
representable morphism `f : Y ⟶ X` of algebraic spaces and a quasi-coherent sheaf of ideals
`ℐ ⊆ 𝒪_X`, the sheaf of ideals `f⁻¹ℐ · 𝒪_Y` is quasi-coherent.

It is the image of `f^*ℐ ⟶ 𝒪_Y`
(`AlgebraicGeometry.Space.pullbackIdealSubsheaf_eq_ker_cokernel`), whose source is
quasi-coherent by Stacks 03GA. -/
theorem isQuasicoherentOnSite_pullbackIdealSubsheaf
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite) :
    (pullbackIdealSubsheaf B S hS f hf I).toSheafOfModules.IsQuasicoherentOnSite := by
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (smallEtaleRingSheaf B S hS Y.1 Y.2)).IsClosedUnderKernels :=
    isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS Y.1 Y.2
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (smallEtaleRingSheaf B S hS Y.1 Y.2)).IsClosedUnderCokernels :=
    isClosedUnderCokernels_quasicoherentSheaves B S hS Y.1 Y.2
  have hsrc : ((SheafOfModules.pullback.{u} (smallBaseChangeSharp B S hS f hf)).obj
      I.toSheafOfModules).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePullbackChartIso B S hS f hf).app I.toSheafOfModules)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f _ hI)
  have hunit : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2)).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_unit _
  rw [pullbackIdealSubsheaf_eq_ker_cokernel]
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (SheafOfModules.Submodule.kerIsoKernel _).symm
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_kernel _ hunit
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (smallEtaleRingSheaf B S hS Y.1 Y.2)).prop_cokernel
          (pullbackIdealToUnit B S hS f hf I) hsrc hunit))

end AlgebraicGeometry.Space
