module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# Inverse image of `Ker(ℰ → ℒ) ⊗ ℒ^{⊗ -1}` along a flat morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `ℒ` an invertible `𝒪_Y`-module.  The
inverse image `f^*` carries the integral tensor powers of `ℒ` to those of `f^*ℒ` (it is compatible
with the tensor product, Stacks 03EL, and with the structure sheaves), and when `f` is flat it is
exact, so it carries the kernel of a map `q : ℰ ⟶ ℒ` to the kernel of `f^*q`.  Together:
`f^*(Ker(q) ⊗ ℒ^{⊗ -1}) ≅ Ker(f^*q) ⊗ (f^*ℒ)^{⊗ -1}`, the source of the conormal isomorphism of
Stacks 0B4I restricted to `X`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackTensorPowerIso`: `f^*(ℒ^{⊗ n}) ≅ (f^*ℒ)^{⊗ n}`.
* `AlgebraicGeometry.Space.modulePullbackKernelIso`: `f^*Ker(q) ≅ Ker(f^*q)` for flat `f`.
* `AlgebraicGeometry.Space.modulePullbackKernelTensorInverseIso`: the combination.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The inverse image is compatible with tensoring by a fixed module (Stacks 03EL), in the shape
the transport of integral tensor powers consumes. -/
def modulePullbackTensorComparison (L : Modules.{u, u} B S hS Y.1 Y.2) :
    Stacks.SheafOfModules.TensorPower.TensorComparison (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (modulePullback B S hS f) L :=
  fun M => (Stacks.SheafOfModules.pullbackTensorIso
    (smallEtaleRingedToposModulesHom B S hS f)).app (M, L)

/-- **The inverse image of an integral tensor power of an invertible module is the tensor power
of the inverse image**: `f^*(ℒ^{⊗ n}) ≅ (f^*ℒ)^{⊗ n}` for every `n : ℤ`. -/
def modulePullbackTensorPowerIso (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L]
    (n : ℤ) :
    haveI := isInvertible_modulePullback_obj B S hS f L hL
    (modulePullback B S hS f).obj (Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L n) ≅
      Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property ((modulePullback B S hS f).obj L) n :=
  haveI := isInvertible_modulePullback_obj B S hS f L hL
  haveI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L
  haveI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
    ((modulePullback B S hS f).obj L)
  Stacks.SheafOfModules.TensorPower.mapTensorPowerIso (structureCommRings B S hS Y)
    (structureRingSheaf B S hS Y).property (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property (modulePullback B S hS f) L
    (modulePullbackTensorComparison f L) (modulePullbackUnitIso B S hS f) n

/-- **The inverse image along a flat morphism carries kernels to kernels.** -/
def modulePullbackKernelIso (hf : (smallEtaleRingedToposHom B S hS f).IsFlat)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (q : M ⟶ N) :
    (modulePullback B S hS f).obj (kernel q) ≅ kernel ((modulePullback B S hS f).map q) :=
  haveI : PreservesFiniteLimits (modulePullback B S hS f) :=
    ((exactFunctor_iff _).mp (exactFunctor_modulePullback_of_isFlat B S hS f hf)).1
  haveI : (modulePullback B S hS f).PreservesZeroMorphisms :=
    haveI : (modulePullback B S hS f).IsLeftAdjoint :=
      (modulePullbackAdjunction B S hS f).isLeftAdjoint
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  PreservesKernel.iso (modulePullback B S hS f) q

/-- **`f^*(Ker(q) ⊗ ℒ^{⊗ -1}) ≅ Ker(f^*q) ⊗ (f^*ℒ)^{⊗ -1}`** for a flat morphism `f` and a map
`q : ℰ ⟶ ℒ` into an invertible module. -/
def modulePullbackKernelTensorInverseIso
    (hf : (smallEtaleRingedToposHom B S hS f).IsFlat)
    {M L : Modules.{u, u} B S hS Y.1 Y.2} (q : M ⟶ L)
    [hL : IsInvertible (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L] :
    haveI := isInvertible_modulePullback_obj B S hS f L hL
    (modulePullback B S hS f).obj (kernel q ⊗ Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS Y) (structureRingSheaf B S hS Y).property L (-1)) ≅
      kernel ((modulePullback B S hS f).map q) ⊗ Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        ((modulePullback B S hS f).obj L) (-1) :=
  haveI := isInvertible_modulePullback_obj B S hS f L hL
  modulePullbackTensorIso B S hS f _ _ ≪≫
    tensorIso (modulePullbackKernelIso f hf q) (modulePullbackTensorPowerIso f L (-1))

end AlgebraicGeometry.Space

end
