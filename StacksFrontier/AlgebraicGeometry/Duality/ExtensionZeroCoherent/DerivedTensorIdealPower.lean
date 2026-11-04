module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.Injectivity
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# The derived tensor products `K ⊗^L 𝓘^n`

Let `X` be a scheme and `𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals. For `K` in `D(𝒪_X)` the
derived tensor products `K ⊗^L_{𝒪_X} 𝓘^n` with the ideal powers, placed in degree zero, form an
inverse system in `D(𝒪_X)` along the inclusions `𝓘^{n+1} ⊆ 𝓘^n`. This is the system of
[Stacks, Tag 0G4U].

## Main definitions

* `AlgebraicGeometry.idealPowerSheaf`: the ideal power `𝓘^n`, as an `𝒪_X`-module.
* `AlgebraicGeometry.idealPowerSheafTransition`: the inclusion `𝓘^{n+1} ⟶ 𝓘^n`.
* `AlgebraicGeometry.derivedTensorIdealPowerSystem`: the inverse system `(K ⊗^L 𝓘^n)_n`.

## Implementation notes

The derived tensor product is the canonical one of [Stacks, Tag 06YU],
`Stacks.Cohomology.TorAmplitude.derTensor`, read at the standard model of `D(𝒪_X)`, which is the
model of `AlgebraicGeometry.BoundedCoherentDerived` and of Deligne systems.

## References

* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The ideal power `𝓘^n` of a quasi-coherent sheaf of ideals, as an `𝒪_X`-module: the subsheaf
`𝓘^n · 𝒪_X` of the structure sheaf, that is
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow`. -/
public abbrev idealPowerSheaf (I : X.IdealSheafData) (n : ℕ) : X.Modules :=
  Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow I n

/-- The inclusion `𝓘^{n+1} ⟶ 𝓘^n` of ideal powers. -/
public abbrev idealPowerSheafTransition (I : X.IdealSheafData) (n : ℕ) :
    idealPowerSheaf I (n + 1) ⟶ idealPowerSheaf I n :=
  idealPowerMultipleMap I (SheafOfModules.unit X.ringCatSheaf) (Nat.le_succ n)

/-- **The inverse system `(K ⊗^L_{𝒪_X} 𝓘^n)_n`** in `D(𝒪_X)`, with the transition maps induced
by the inclusions `𝓘^{n+1} ⊆ 𝓘^n`. The derived tensor product is that of [Stacks, Tag 06YU],
and `𝓘^n` sits in degree zero. -/
public def derivedTensorIdealPowerSystem (I : X.IdealSheafData) (K : DerivedCategory X.Modules) :
    ℕᵒᵖ ⥤ DerivedCategory X.Modules :=
  Functor.ofOpSequence
    (X := fun n => ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj K).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n)))
    (fun n => ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj K).map
      ((DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)))

end AlgebraicGeometry

end
