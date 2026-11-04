module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceCompositeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
import StacksCore.Tactic.StacksAttribute

/-!
# The first arrow of the conormal sequence at the kernel ideal sheaf

Let `B` be an algebraic space over a scheme `S`, let `f : X ⟶ Y` be a morphism of algebraic
spaces and let `g : Y ⟶ B` be a structure morphism. This file builds the first arrow
`f^*𝓘_f ⟶ f^*Ω_{Y/B}` of the conormal sequence of Stacks 05ZA out of the **kernel ideal sheaf**
`𝓘_f = ker(f♯ : 𝒪_Y ⟶ f_*𝒪_X)` of an arbitrary morphism, and proves that its composite with the
second arrow is zero. For the inclusion of a closed subspace the kernel ideal sheaf is the
defining ideal sheaf of Stacks 03MB
(`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`), and the arrow is
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealUnitDifferential`: the adjoint form of the arrow, the
  morphism of `𝒪_Y`-modules `𝓘_f ⟶ f_*f^*Ω_{Y/B}` obtained by restricting
  `AlgebraicGeometry.Space.pullbackUnitDerivation`, `d_{Y/B}` followed by the unit of
  `f^* ⊣ f_*`, to the kernel ideal sheaf.
* `AlgebraicGeometry.Space.kernelConormalFirstMap`: the arrow `f^*𝓘_f ⟶ f^*Ω_{Y/B}`, its
  transpose along the adjunction of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.kernelIdealAt_smul_modulePushforward_eq_zero`: a section of the kernel
  ideal sheaf annihilates every section of a direct image along `f` (Stacks 04CJ, part (3), for
  an arbitrary morphism `f`).
* `AlgebraicGeometry.Space.kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero`: the
  composite of this arrow with the second arrow of Stacks 05ZA is zero.
* `AlgebraicGeometry.Space.kernelConormalFirstMap_eq_conormalSequenceIdealPullbackMap`: at the
  inclusion of a closed subspace this arrow is
  `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ), part (3), annihilation
  of a direct image by the kernel of the structure map.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction
  `f^* ⊣ f_*` the transposition is taken along.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map that
  is the second arrow.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Bb : AlgebraicSpaces B S hS}

/-- **Stacks 04CJ, part (3), at the kernel ideal sheaf of an arbitrary morphism.**  A section of
`𝓘_f = ker(f♯)` annihilates every section of a direct image of modules along `f`. -/
theorem kernelIdealAt_smul_modulePushforward_eq_zero (f : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS Y).obj.obj U))
    (ha : a ∈ (kernelIdealSheaf B S hS f).obj U)
    (m : ((modulePushforward B S hS f).obj G).val.obj U) :
    letI : Module ((structureRingSheaf B S hS Y).obj.obj U)
        (((modulePushforward B S hS f).obj G).val.obj U) :=
      (((modulePushforward B S hS f).obj G).val.obj U).isModule
    a • m = 0 :=
  Stacks.Sheaves.PushforwardEssentialImage.smul_restrictScalars_eq_zero
    (structureSharp B S hS f) ((moduleDirectImage B S hS f).obj G) U a
    (RingHom.mem_ker.1 ha) m

/-- **The adjoint form of the first arrow of Stacks 05ZA at the kernel ideal sheaf**: the morphism
of `𝒪_Y`-modules `𝓘_f ⟶ f_*f^*Ω_{Y/B}` obtained by restricting
`AlgebraicGeometry.Space.pullbackUnitDerivation` to `𝓘_f`. -/
noncomputable def kernelIdealUnitDifferential (f : X ⟶ Y) (g : Y ⟶ Bb) :
    (kernelIdealSheaf B S hS f).toSheafOfModules ⟶
      (modulePushforward B S hS f).obj
        ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)) :=
  submoduleDerivationHom B S hS (kernelIdealSheaf B S hS f) _
    (pullbackUnitDerivation B S hS f g)
    (fun U a ha m ↦ kernelIdealAt_smul_modulePushforward_eq_zero B S hS f _ U a ha m)

/-- The value of `AlgebraicGeometry.Space.kernelIdealUnitDifferential` on a local section of the
kernel ideal sheaf is the value on it of `AlgebraicGeometry.Space.pullbackUnitDerivation`, that
is, `d_{Y/B}` of the section followed by the unit of `f^* ⊣ f_*`. -/
theorem kernelIdealUnitDifferential_val_app_apply (f : X ⟶ Y) (g : Y ⟶ Bb)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U) :
    (ModuleCat.Hom.hom ((kernelIdealUnitDifferential B S hS f g).val.app U)) x =
      (pullbackUnitDerivation B S hS f g).d x.1 :=
  rfl

/-- **The first arrow of Stacks 05ZA at the kernel ideal sheaf**: the transpose along the
adjunction `f^* ⊣ f_*` of Stacks 03LU of
`AlgebraicGeometry.Space.kernelIdealUnitDifferential`. -/
noncomputable def kernelConormalFirstMap (f : X ⟶ Y) (g : Y ⟶ Bb) :
    (modulePullback B S hS f).obj (kernelIdealSheaf B S hS f).toSheafOfModules ⟶
      (modulePullback B S hS f).obj (sheafOfDifferentials B S hS g) :=
  submoduleTranspose B S hS f (kernelIdealSheaf B S hS f)
    ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g))
    (kernelIdealUnitDifferential B S hS f g)

/-- **The composite of the two arrows of Stacks 05ZA is zero, at the kernel ideal sheaf of an
arbitrary morphism.**  The arrow `f^*𝓘_f ⟶ f^*Ω_{Y/B}` followed by the comparison map
`f^*Ω_{Y/B} ⟶ Ω_{X/B}` of Stacks 04CX is the zero morphism. -/
theorem kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero (f : X ⟶ Y) (g : Y ⟶ Bb) :
    kernelConormalFirstMap B S hS f g ≫ pullbackDifferentialsMap B S hS f g = 0 :=
  submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero' B S hS f g
    (kernelIdealSheaf B S hS f) (kernelIdealUnitDifferential B S hS f g)
    (pullbackUnitDerivation B S hS f g) rfl
    (kernelIdealUnitDifferential_val_app_apply B S hS f g)
    (fun _ x ↦ RingHom.mem_ker.1 x.2)
    rfl

/-- **At the inclusion of a closed subspace this is the first arrow of Stacks 05ZA.** At the
inclusion of a closed subspace `Z`, `AlgebraicGeometry.Space.kernelConormalFirstMap` is
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`, the first arrow of Stacks 05ZA built
from the defining ideal sheaf of Stacks 03MB. -/
theorem kernelConormalFirstMap_eq_conormalSequenceIdealPullbackMap
    (Z : ClosedSubspaces B S hS Y.1) (b : Y ⟶ Bb) :
    kernelConormalFirstMap B S hS (subspaceInclusion B S hS Y Z) b =
      conormalSequenceIdealPullbackMap B S hS Z b :=
  rfl

end AlgebraicGeometry.Space

end
