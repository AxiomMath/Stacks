module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# The conormal algebra of a closed subspace of an algebraic space in degree zero

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `Z` be a
closed subspace of `X` with inclusion `i : Z ⟶ X`, and let `𝓘 ⊆ 𝒪_X` be the defining ideal sheaf
of `Z` on the small étale site of `X`, that is `AlgebraicGeometry.Space.definingIdealSheaf`, the
sheaf of ideals of Stacks 03MB.  The conormal algebra of `Z` in `X` is the graded `𝒪_Z`-algebra
whose piece in degree `n` is the quasi-coherent `𝒪_Z`-module `𝒞_{Z/X, n}` characterized by

`i_*𝒞_{Z/X, n} = 𝓘ⁿ/𝓘ⁿ⁺¹`.

In degree zero `𝒞_{Z/X, 0} = 𝒪_Z`, while `𝓘⁰ = 𝒪_X` and `𝓘¹ = 𝓘`, so that characterization reads
`i_*𝒪_Z = 𝒪_X/𝓘`.  This file proves it in the form that the canonical map `𝒪_X ⟶ i_*𝒪_Z`
exhibits `i_*𝒪_Z` as the cokernel of the inclusion `𝓘 ⟶ 𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardStructureSheaf`: the direct image `i_*𝒪_Z` of the structure
  sheaf of a closed subspace.
* `AlgebraicGeometry.Space.structureProjection`: the canonical map `𝒪_X ⟶ i_*𝒪_Z` of
  `𝒪_X`-modules, given on sections over an object of the small étale site by the structure map of
  the inclusion.
* `AlgebraicGeometry.Space.definingIdealShortComplex`: the sequence `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z`.
* `AlgebraicGeometry.Space.isColimitCokernelCofork`: the structure projection is a cokernel of the
  inclusion of the defining ideal sheaf.
* `AlgebraicGeometry.Space.conormalAlgebraDegreeZeroIso`: the identification `𝒪_X/𝓘 ≅ i_*𝒪_Z` of
  the quotient of the structure sheaf by the defining ideal with the direct image of the structure
  sheaf of the subspace.

## Main results

* `AlgebraicGeometry.Space.structureProjection_val_app_apply`: the structure projection acts on
  sections as the structure map of the inclusion.
* `AlgebraicGeometry.Space.ker_structureProjection`: the defining ideal sheaf of `Z` is the kernel
  of the structure projection.
* `AlgebraicGeometry.Space.epi_structureProjection`: the structure projection is an epimorphism.
* `AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`: `0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` is
  short exact.
* `AlgebraicGeometry.Space.cokernel_π_comp_conormalAlgebraDegreeZeroIso_hom`: the identification
  in degree zero is the map induced by the structure projection.

## Implementation notes

`AlgebraicGeometry.Space.pushforwardStructureSheaf B S hS X Z` is
`AlgebraicGeometry.Space.structureSheafPushforward` at
`AlgebraicGeometry.Space.subspaceInclusion B S hS X Z`; the general form cannot be used here
because its module imports this one, and it is the one to prefer in new files.

Mathlib's instance making the inclusion of a submodule subsheaf a monomorphism does not apply at
this presentation of the small étale modules, so the monomorphism is taken from the limit fork
`CategoryTheory.SheafOfModules.Submodule.isLimitKernelFork`.

## References

* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- The direct image `i_*𝒪_Z` along the inclusion of a closed subspace, of the structure sheaf of
the subspace regarded as a module over itself.  It is the pushforward to `X` of the piece
`𝒞_{Z/X, 0} = 𝒪_Z` of the conormal algebra of `Z` in `X`. -/
noncomputable abbrev pushforwardStructureSheaf : Modules.{u, u} B S hS X.1 X.2 :=
  (modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨Z.1.toFunctor, Z.2.1⟩))

/-- The canonical map `𝒪_X ⟶ i_*𝒪_Z` of `𝒪_X`-modules along the inclusion of a closed subspace,
given on sections over an object of the small étale site of `X` by the structure map of the
inclusion. -/
noncomputable def structureProjection :
    (SheafOfModules.unit (structureRingSheaf B S hS X)) ⟶
      pushforwardStructureSheaf B S hS X Z where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map
      ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U)) (fun r ↦ by
      ext m
      exact (((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom.map_mul
        r m).symm)
  val.naturality g := by
    ext
    exact ConcreteCategory.congr_hom
      ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.naturality g) _

/-- The structure projection acts on sections as the structure map of the inclusion. -/
@[simp]
theorem structureProjection_val_app_apply (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (structureRingSheaf B S hS X).obj.obj U) :
    (structureProjection B S hS X Z).val.app U a =
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U a :=
  rfl

/-- **The defining ideal sheaf of a closed subspace is the kernel of the structure projection.** -/
theorem ker_structureProjection :
    SheafOfModules.Submodule.ker (structureProjection B S hS X Z) =
      definingIdealSheaf B S hS X Z := by
  apply SheafOfModules.Submodule.ext
  rfl

/-- **The structure projection is an epimorphism.** -/
theorem epi_structureProjection : Epi (structureProjection B S hS X Z) := by
  have h : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom :=
    isLocallySurjective_structureSharp B S hS (subspaceInclusion B S hS X Z) Z.2.2
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨fun {_} s ↦ h.imageSieve_mem s⟩

/-- The sequence `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z`, with the defining ideal sheaf of the closed subspace in the
left-hand spot. -/
noncomputable def definingIdealShortComplex : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk (definingIdealSheaf B S hS X Z).ι (structureProjection B S hS X Z)
    (SheafOfModules.Submodule.ker_ι_comp (structureProjection B S hS X Z))

/-- **`0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` is short exact.** -/
theorem definingIdealShortComplex_shortExact :
    (definingIdealShortComplex B S hS X Z).ShortExact := by
  have h := SheafOfModules.Submodule.isLimitKernelFork (structureProjection B S hS X Z)
  exact { exact := ShortComplex.exact_of_f_is_kernel _ h
          mono_f := mono_of_isLimit_fork h
          epi_g := epi_structureProjection B S hS X Z }

/-- The structure projection exhibits `i_*𝒪_Z` as the cokernel of the inclusion of the defining
ideal sheaf. -/
noncomputable def isColimitCokernelCofork :
    IsColimit (CokernelCofork.ofπ (structureProjection B S hS X Z)
      (SheafOfModules.Submodule.ker_ι_comp (structureProjection B S hS X Z))) :=
  (definingIdealShortComplex_shortExact B S hS X Z).gIsCokernel

/-- For a closed subspace `Z` of an algebraic space `X` with
inclusion `i` and defining ideal sheaf `𝓘`, the direct image of the structure sheaf of `Z` is the
quotient of the structure sheaf of `X` by `𝓘`:

`i_*𝒞_{Z/X, 0} = i_*𝒪_Z = 𝒪_X/𝓘 = 𝓘⁰/𝓘¹`.

The isomorphism is induced by the structure projection. -/
@[stacks 09RP "degree zero"]
noncomputable def conormalAlgebraDegreeZeroIso :
    cokernel (definingIdealSheaf B S hS X Z).ι ≅ pushforwardStructureSheaf B S hS X Z :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitCokernelCofork B S hS X Z)

/-- The identification in degree zero is the map induced by the structure projection: composing
the projection onto the quotient with it gives back the structure projection. -/
@[simp]
theorem cokernel_π_comp_conormalAlgebraDegreeZeroIso_hom :
    cokernel.π (definingIdealSheaf B S hS X Z).ι ≫
        (conormalAlgebraDegreeZeroIso B S hS X Z).hom =
      structureProjection B S hS X Z :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (isColimitCokernelCofork B S hS X Z) WalkingParallelPair.one

end AlgebraicGeometry.Space

end
