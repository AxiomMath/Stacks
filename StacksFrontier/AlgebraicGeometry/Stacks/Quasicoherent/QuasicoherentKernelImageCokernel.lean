module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInputs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentKernelCokernel
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.CoreflectiveKernelImage

/-!
# Kernels, images and cokernels of maps of quasi-coherent modules (Stacks 0GQL)

Let `𝒳` be an algebraic stack over `S`, `QCoh(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` its quasi-coherent modules inside
all modules on its fppf site, and `i` the inclusion. **Stacks 0GQL** says that `QCoh(𝒪_𝒳)` is
abelian, that `i` is right exact, and that for a map `φ : 𝓕 → 𝓖` of quasi-coherent modules

1. `Coker(φ)` computed in `Mod(𝒪_𝒳)` is quasi-coherent and is the cokernel of `φ` in `QCoh(𝒪_𝒳)`;
2. `Im(φ)` computed in `Mod(𝒪_𝒳)` is quasi-coherent and is the image of `φ` in `QCoh(𝒪_𝒳)`;
3. `Ker(φ)` computed in `Mod(𝒪_𝒳)` lies in `LQCoh^fbc(𝒪_𝒳)` and `Q(Ker(φ))` is the kernel of `φ`
   in `QCoh(𝒪_𝒳)`, where `Q` is the coherator of **Stacks 0778**.

This file proves the right exactness of `i` and part (1) with no hypothesis.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteColimits_quasicoherentInclusion`: the
  inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is right exact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isColimitCokernelCoforkQuasicoherentInclusion` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasicoherent_cokernel_quasicoherentInclusion`:
  **Stacks 0GQL** part (1).

## Implementation notes

Both rest on the closure of quasi-coherence under colimits,
`AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_quasicoherentModules`, which holds on the
essentially small fppf site of an algebraic stack: it makes `QCoh(𝒪_𝒳)` cocomplete and `i`
cocontinuous. These are recorded as instances, so that `cokernel φ` makes sense in
`QCoh(𝒪_𝒳)`; the arguments are those of
`AlgebraicGeometry.FibredSite.isColimitCokernelCoforkMapQuasicoherentInclusion`, which carries
the two facts as instance arguments.

## References

* [Stacks Project, Tag 0GQL](https://stacks.math.columbia.edu/tag/0GQL)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- `QCoh(𝒪_𝒳)` has colimits indexed at the universe of the schemes: quasi-coherence on the fppf
site of an algebraic stack is closed under colimits. -/
theorem hasColimitsOfSize_quasicoherentModules :
    HasColimitsOfSize.{u, u} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
  FibredSite.hasColimitsOfSize_quasicoherentModules B S hS _ _
    (FibredSite.closedUnderColimitsOfSize_quasicoherentModules B S hS _ _)

/-- The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` preserves colimits indexed at the universe of the
schemes. -/
theorem preservesColimitsOfSize_quasicoherentInclusion :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι :=
  FibredSite.preservesColimitsOfSize_quasicoherentInclusion B S hS _ _
    (FibredSite.closedUnderColimitsOfSize_quasicoherentModules B S hS _ _)

/-- **Stacks 0GQL, the right exactness of the inclusion.** The inclusion
`QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` of the quasi-coherent modules on an algebraic stack is right exact. -/
@[stacks 0GQL "the inclusion QCoh(𝒪_𝒳) → Mod(𝒪_𝒳) is right exact"]
theorem preservesFiniteColimits_quasicoherentInclusion :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι :=
  have := preservesColimitsOfSize_quasicoherentInclusion B S hS 𝒳
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- A map of quasi-coherent modules on an algebraic stack has a cokernel in `QCoh(𝒪_𝒳)`. -/
instance hasCokernel_quasicoherentModules
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G) : HasCokernel φ :=
  haveI := hasColimitsOfSize_quasicoherentModules B S hS 𝒳
  haveI : HasColimitsOfSize.{0, 0} (FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  @HasColimitsOfShape.has_colimit _ _ _ _
    (HasColimitsOfSize.has_colimits_of_shape WalkingParallelPair) (parallelPair φ 0)

/-- The inclusion `QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` preserves the cokernel of a map of quasi-coherent
modules. -/
instance preservesColimit_parallelPair_quasicoherentInclusion
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G) :
    PreservesColimit (parallelPair φ 0) (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).ι :=
  haveI := preservesFiniteColimits_quasicoherentInclusion B S hS 𝒳
  inferInstance

/-- **Stacks 0GQL, part (1).** Let `φ : 𝓕 → 𝓖` be a map of quasi-coherent modules on an algebraic
stack `𝒳`. The cokernel of `φ` in `QCoh(𝒪_𝒳)`, included into `Mod(𝒪_𝒳)` with its projection, is a
cokernel of `φ` in `Mod(𝒪_𝒳)`: the cokernel computed in `Mod(𝒪_𝒳)` is the cokernel in
`QCoh(𝒪_𝒳)`. -/
@[stacks 0GQL "part (1): the cokernel computed in Mod(𝒪_𝒳) of a map of quasi-coherent modules is \
  the cokernel computed in QCoh(𝒪_𝒳)"]
def isColimitCokernelCoforkQuasicoherentInclusion
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G) :
    IsColimit (Cofork.ofπ
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            .fppf)).ι.map (cokernel.π φ))
      (by simp only [← Functor.map_comp, cokernel.condition, zero_comp, Functor.map_zero]) :
      Cofork ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι.map φ) 0) :=
  isColimitOfHasCokernelOfPreservesColimit _ _

/-- **Stacks 0GQL, part (1), the quasi-coherence half.** The cokernel computed in `Mod(𝒪_𝒳)` of a
map of quasi-coherent modules on an algebraic stack is quasi-coherent. -/
@[stacks 0GQL "part (1), the quasi-coherence half: the cokernel computed in Mod(𝒪_𝒳) of a map of \
  quasi-coherent modules is quasi-coherent"]
theorem isQuasicoherent_cokernel_quasicoherentInclusion
    {F G : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids} (φ : F ⟶ G) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
      (cokernel ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).ι.map φ)) :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).prop_of_iso (PreservesCokernel.iso _ φ) (cokernel φ).property

end AlgebraicGeometry.Stack.AlgebraicStacks

end
