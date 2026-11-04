module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal

/-!
# The sequence `0 ⟶ 𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X` of an arbitrary morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  `StacksFrontier/AlgebraicGeometry/Spaces/MorphismKernelIdeal.lean` attaches to it the
kernel ideal sheaf `𝓘_f = ker(f♯ : 𝒪_Y ⟶ f_*𝒪_X)`.  This file exhibits that ideal as a kernel
*in the category of sheaves of modules*, and proves the sequence short exact when `f` is a
closed immersion.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraDegreeZero.lean` already does this for the
inclusion of a bundled `AlgebraicGeometry.Space.ClosedSubspaces`.  The statements below are the
same ones with the morphism a free variable and the ideal read as the kernel ideal sheaf, which
is what the conormal sequence of an immersion needs: the closed immersion an immersion factors
through by Stacks 04CE is not the inclusion of a bundled closed subspace.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealStructureProjection`: the canonical map
  `𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules, given on sections by the structure map of `f`.
* `AlgebraicGeometry.Space.kernelIdealShortComplex`: the sequence
  `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.ker_kernelIdealStructureProjection`: the kernel ideal sheaf *is* the
  kernel of that projection, with no comparison map between them.
* `AlgebraicGeometry.Space.isLimitKernelFork_kernelIdealShortComplex`: the inclusion of the
  kernel ideal sheaf is a kernel of the projection, for an arbitrary `f`.
* `AlgebraicGeometry.Space.kernelIdealShortComplex_exact` and
  `AlgebraicGeometry.Space.mono_kernelIdealShortComplex_f`: exactness at the middle term and the
  monomorphism, for an arbitrary `f`.
* `AlgebraicGeometry.Space.epi_kernelIdealStructureProjection` and
  `AlgebraicGeometry.Space.kernelIdealShortComplex_shortExact`: the surjectivity clause of
  Stacks 03MB and the resulting short exactness, for a closed immersion with the morphism a
  free variable.  The tag is registered where the clause is proved,
  `AlgebraicGeometry.Space.isLocallySurjective_structureSharp`; nothing is registered here.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the structure map of a
  closed immersion is surjective with the defining ideal sheaf for kernel.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The canonical map `𝒪_Y ⟶ f_*𝒪_X` of `𝒪_Y`-modules**, for an arbitrary morphism `f` of
algebraic spaces, given on sections over an object of the small étale site of `Y` by the
structure map of Stacks 03G8.

The sections of `f_*𝒪_X` over such an object are its sections as a sheaf of rings, so the
underlying additive map is the structure map itself; `𝒪_Y`-linearity is multiplicativity of the
structure map, the action of `𝒪_Y` on the target being restriction of scalars along it.

At the inclusion of a bundled closed subspace this is
`AlgebraicGeometry.Space.structureProjection`. -/
noncomputable def kernelIdealStructureProjection (f : X ⟶ Y) :
    SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶
      (modulePushforward B S hS f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map ((structureSharp B S hS f).hom.app U)) (fun r ↦ by
      ext m
      exact (((structureSharp B S hS f).hom.app U).hom.map_mul r m).symm)
  val.naturality g := by
    ext
    exact ConcreteCategory.congr_hom ((structureSharp B S hS f).hom.naturality g) _

/-- The projection acts on sections as the structure map of `f`. -/
@[simp]
theorem kernelIdealStructureProjection_val_app_apply (f : X ⟶ Y)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (a : (structureRingSheaf B S hS Y).obj.obj U) :
    (kernelIdealStructureProjection B S hS f).val.app U a =
      (structureSharp B S hS f).hom.app U a :=
  rfl

/-- **The kernel ideal sheaf of `f` is the kernel of the projection `𝒪_Y ⟶ f_*𝒪_X`.**

Both submodule subsheaves have, over every object of the small étale site, the
ring-homomorphism kernel of the structure map for their sections, so no comparison map between
them is needed. -/
theorem ker_kernelIdealStructureProjection (f : X ⟶ Y) :
    SheafOfModules.Submodule.ker (kernelIdealStructureProjection B S hS f) =
      kernelIdealSheaf B S hS f := by
  apply SheafOfModules.Submodule.ext
  rfl

/-- The sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X`, with the kernel ideal sheaf of `f` in the left-hand
spot.  It is a complex because the ideal is the kernel of the projection. -/
noncomputable def kernelIdealShortComplex (f : X ⟶ Y) :
    ShortComplex (Modules.{u, u} B S hS Y.1 Y.2) :=
  ShortComplex.mk (kernelIdealSheaf B S hS f).ι (kernelIdealStructureProjection B S hS f)
    (SheafOfModules.Submodule.ker_ι_comp (kernelIdealStructureProjection B S hS f))

/-- **The inclusion of the kernel ideal sheaf is a kernel of the projection `𝒪_Y ⟶ f_*𝒪_X`**,
for an arbitrary morphism `f`: the submodule it is the kernel of the projection on the nose. -/
noncomputable def isLimitKernelFork_kernelIdealShortComplex (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kernelIdealShortComplex B S hS f).f
      (kernelIdealShortComplex B S hS f).zero) :=
  SheafOfModules.Submodule.isLimitKernelFork (kernelIdealStructureProjection B S hS f)

/-- **The sequence `𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X` is exact at the middle term**, for an arbitrary
morphism `f`. -/
theorem kernelIdealShortComplex_exact (f : X ⟶ Y) :
    (kernelIdealShortComplex B S hS f).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork_kernelIdealShortComplex B S hS f)

/-- **The inclusion of the kernel ideal sheaf is a monomorphism**, for an arbitrary morphism
`f`. -/
theorem mono_kernelIdealShortComplex_f (f : X ⟶ Y) :
    Mono (kernelIdealShortComplex B S hS f).f :=
  mono_of_isLimit_fork (isLimitKernelFork_kernelIdealShortComplex B S hS f)

/-- **Stacks 03MB, surjectivity, at a free closed immersion.**  The projection `𝒪_Y ⟶ f_*𝒪_X`
is an epimorphism of sheaves of modules when `f` is a closed immersion, because the structure
map of a closed immersion is locally surjective on the small étale site of the target
(`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`) and the projection has the
structure map for its map on sections. -/
theorem epi_kernelIdealStructureProjection (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Epi (kernelIdealStructureProjection B S hS f) := by
  have h : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1)
      (structureSharp B S hS f).hom :=
    isLocallySurjective_structureSharp B S hS f hf
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨fun {_} s ↦ h.imageSieve_mem s⟩

/-- **`0 ⟶ 𝓘_f ⟶ 𝒪_Y ⟶ f_*𝒪_X ⟶ 0` is short exact at a free closed immersion**, which is the
content of Stacks 03MB read at the kernel ideal sheaf.

Exactness and the monomorphism hold for an arbitrary morphism, the kernel ideal sheaf being the
kernel of the projection on the nose; the epimorphism is
`AlgebraicGeometry.Space.epi_kernelIdealStructureProjection`.

At the inclusion of a bundled closed subspace this is
`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`. -/
theorem kernelIdealShortComplex_shortExact (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    (kernelIdealShortComplex B S hS f).ShortExact where
  exact := kernelIdealShortComplex_exact B S hS f
  mono_f := mono_kernelIdealShortComplex_f B S hS f
  epi_g := epi_kernelIdealStructureProjection B S hS f hf

end AlgebraicGeometry.Space

end
