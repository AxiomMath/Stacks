module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealShortExact
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations

/-!
# The inverse image of the kernel ideal sheaf is a kernel

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, with kernel ideal sheaf `𝓘_f = ker(f♯) ⊆ 𝒪_Y`.  This file transports the short
exact sequence
```
  0 ⟶ 𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X ⟶ 0
```
of `AlgebraicGeometry.Space.kernelIdealShortComplex` — whose left-hand half, that `𝓘_f` is the
kernel of the projection, holds for every `f` — along the inverse image of sheaves of modules
of Stacks 03D2 and then along its right adjoint, the direct image of Stacks 03D1, and reads the
result on sections.

`StacksFrontier/AlgebraicGeometry/Spaces/InverseImageDefiningIdealKernel.lean` does the same for
the inclusion of a bundled `AlgebraicGeometry.Space.ClosedSubspaces`, through the short exact
sequence of Stacks 03MB.  Everything below has the morphism a free variable and uses only the
left-exact half, which is what the conormal sequence of a general immersion needs: an immersion
is not a closed immersion, and the closed immersion Stacks 04CE factors it through is not the
inclusion of a bundled closed subspace.

## Main results

* `AlgebraicGeometry.Space.isLimitKernelFork_inverseImageKernelIdeal`:
  `f⁻¹𝓘_f ⟶ f⁻¹𝒪_Y` is a kernel of `f⁻¹(f♯)`, the inverse image of sheaves of modules
  preserving finite limits (Stacks 04JC at module level).
* `AlgebraicGeometry.Space.isLimitKernelFork_directImageKernelIdeal`:
  `f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y` is a kernel of `f_*f⁻¹(f♯)`, the direct image of modules being a
  right adjoint and so left exact.
* `AlgebraicGeometry.Space.injective_directImageKernelIdeal_f_val_app` and
  `AlgebraicGeometry.Space.mem_range_directImageKernelIdeal_f_val_app`: over every object of
  the small étale site of `Y` the inclusion `(f_*f⁻¹𝓘_f)(U) ⟶ (f_*f⁻¹𝒪_Y)(U)` is injective and
  its range is exactly the sections killed by `f_*f⁻¹(f♯)`.

**Every statement below holds for an arbitrary morphism of algebraic spaces.**  Only
left exactness is used: the kernel ideal sheaf is the kernel of `𝒪_Y ⟶ f_*𝒪_X` for every `f`,
and both the inverse image and the direct image of sheaves of modules preserve kernels.  Short
exactness, which needs `f` to be a closed immersion, is not needed and is not invoked.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC), exactness of the
  inverse image.
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image, and
  [Tag 03D3](https://stacks.math.columbia.edu/tag/03D3), its adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The inverse image of sheaves of modules along an arbitrary morphism of algebraic spaces
preserves zero morphisms.  Proved in its own declaration and handed to
`CategoryTheory.ShortComplex.map` as an explicit argument, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/InverseImageDefiningIdealKernel.lean`. -/
theorem preservesZeroMorphisms_inverseImageModules_hom (f : X ⟶ Y) :
    (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).PreservesZeroMorphisms :=
  inferInstance

/-- The direct image of sheaves of modules along an arbitrary morphism of algebraic spaces
preserves zero morphisms. -/
theorem preservesZeroMorphisms_directImageModules_hom (f : X ⟶ Y) :
    (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).PreservesZeroMorphisms :=
  inferInstance

/-- **The inverse image of the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X`.**  The short complex
`f⁻¹𝓘_f ⟶ f⁻¹𝒪_Y ⟶ f⁻¹f_*𝒪_X` of sheaves of `f⁻¹𝒪_Y`-modules on the small étale site of `X`. -/
noncomputable def inverseImageKernelIdealComplex (f : X ⟶ Y) :=
  @ShortComplex.map _ _ _ _ _ _ (kernelIdealShortComplex B S hS f)
    (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y))
    (preservesZeroMorphisms_inverseImageModules_hom B S hS f)

/-- **`f⁻¹𝓘_f ⟶ f⁻¹𝒪_Y` is a kernel of `f⁻¹(f♯)`**, for an *arbitrary* morphism `f`.

The inclusion of the kernel ideal sheaf is a kernel of the projection
(`AlgebraicGeometry.Space.isLimitKernelFork_kernelIdealShortComplex`), and the inverse image of
sheaves of modules along a morphism of topoi preserves finite limits, hence kernels.  This is
the half of Stacks 04JC that survives without the projection being an epimorphism, and it is
the half the conormal sequence needs: the projection `𝒪_Y ⟶ f_*𝒪_X` is an epimorphism only for
a closed immersion, while its kernel is the kernel ideal sheaf for every `f`. -/
noncomputable def isLimitKernelFork_inverseImageKernelIdeal (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (inverseImageKernelIdealComplex B S hS f).f
      (inverseImageKernelIdealComplex B S hS f).zero) := by
  haveI hfl : PreservesFiniteLimits
      (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) :=
    inverseImageModules_preservesFiniteLimits
      (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y)
  haveI hsh : PreservesLimitsOfShape WalkingParallelPair
      (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) :=
    hfl.preservesFiniteLimits WalkingParallelPair
  exact @KernelFork.mapIsLimit _ _ _ _ _ _ _ _ _ _
    (isLimitKernelFork_kernelIdealShortComplex B S hS f)
    (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y))
    (preservesZeroMorphisms_inverseImageModules_hom B S hS f) hsh.preservesLimit

/-- **The direct image of the inverse image of the sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X`.**  The short
complex `f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y ⟶ f_*f⁻¹f_*𝒪_X` of sheaves of `𝒪_Y`-modules on the small étale
site of `Y`.  It is not claimed to be short exact: neither the direct image nor, for a general
`f`, the projection it is built from is epimorphic. -/
noncomputable def directImageKernelIdealComplex (f : X ⟶ Y) :=
  @ShortComplex.map _ _ _ _ _ _ (inverseImageKernelIdealComplex B S hS f)
    (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y))
    (preservesZeroMorphisms_directImageModules_hom B S hS f)

/-- The direct image of sheaves of modules of Stacks 03D1 along an arbitrary morphism preserves
finite limits: it is the right adjoint of the adjunction of Stacks 03D3. -/
theorem preservesFiniteLimits_directImageModules_hom (f : X ⟶ Y) :
    PreservesFiniteLimits
      (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) := by
  have : PreservesLimitsOfSize.{0, 0}
      (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) :=
    (inverseImageAdjDirectImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- **`f_*f⁻¹𝓘_f ⟶ f_*f⁻¹𝒪_Y` is a kernel of `f_*f⁻¹(f♯)`**, for an arbitrary morphism `f`:
the direct image of modules preserves finite limits, hence kernels. -/
noncomputable def isLimitKernelFork_directImageKernelIdeal (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (directImageKernelIdealComplex B S hS f).f
      (directImageKernelIdealComplex B S hS f).zero) := by
  haveI hfl := preservesFiniteLimits_directImageModules_hom B S hS f
  haveI hsh : PreservesLimitsOfShape WalkingParallelPair
      (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y)) :=
    hfl.preservesFiniteLimits WalkingParallelPair
  exact @KernelFork.mapIsLimit _ _ _ _ _ _ _ _ _ _
    (isLimitKernelFork_inverseImageKernelIdeal B S hS f)
    (directImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y))
    (preservesZeroMorphisms_directImageModules_hom B S hS f) hsh.preservesLimit

/-- **The inclusion `(f_*f⁻¹𝓘_f)(U) ⟶ (f_*f⁻¹𝒪_Y)(U)` is injective** over every object `U` of
the small étale site of `Y`, for an arbitrary morphism `f`. -/
theorem injective_directImageKernelIdeal_f_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Function.Injective ((directImageKernelIdealComplex B S hS f).f.val.app U) :=
  _root_.SheafOfModules.injective_val_app_of_isLimit_kernelFork
    (isLimitKernelFork_directImageKernelIdeal B S hS f) U

/-- **A section of `f_*f⁻¹𝒪_Y` killed by `f_*f⁻¹(f♯)` comes from `f_*f⁻¹𝓘_f`**, for an
arbitrary morphism `f`. -/
theorem mem_range_directImageKernelIdeal_f_val_app (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    {x : (directImageKernelIdealComplex B S hS f).X₂.val.obj U}
    (hx : (directImageKernelIdealComplex B S hS f).g.val.app U x = 0) :
    x ∈ LinearMap.range ((directImageKernelIdealComplex B S hS f).f.val.app U).hom :=
  _root_.SheafOfModules.mem_range_val_app_of_isLimit_kernelFork
    (isLimitKernelFork_directImageKernelIdeal B S hS f) U hx

end AlgebraicGeometry.Space

end
