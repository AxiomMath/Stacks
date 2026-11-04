module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.RingedSpaceComorphism

/-!
# The structure sheaf of a closed subspace as the quotient by its ideal sheaf

Let `i : Z ⟶ X` be a morphism of ringed spaces with surjective comorphism — a closed immersion,
say — and let `ℐ = Stacks.ClosedImmersion.idealSheaf i` be its ideal sheaf, by definition the
kernel of the comorphism `𝒪_X ⟶ i_*𝒪_Z`. This file names the canonical isomorphism

  `𝒪_X / ℐ ≅ i_*𝒪_Z`

and the identity pinning it down: it is compatible with the quotient map and the comorphism.

The isomorphism is formal — the comorphism of a closed immersion is an epimorphism, which is one
of the three defining conditions, and in an abelian category the cokernel of the kernel of an
epimorphism is its target — but it was not available: the fact had been proved only inside proof
bodies, as the `private` helpers `Stacks.ClosedImmersion.cokernelKernelIso` of
`StacksFrontier.AlgebraicGeometry.Schemes.ClosedImmersions.IsomorphismOfClosedSubspaces` and
`kernelQuotientIso_of_epi` of
`StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence`, and as a field
`quotientIso` of `Stacks.ClosedImmersion.ClosedSubspaceData`, which is the *output* of the
Tag 01HN construction for an arbitrary locally generated ideal sheaf rather than a statement
about a given closed immersion. The public statement nearest to it was
`Stacks.Cohomology.AmpleH1.shortExact_idealSheaf`, the short exact sequence
`0 ⟶ ℐ ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` of a closed immersion of schemes, from which the isomorphism
follows but which does not name it.

## Why it is wanted

It is the step that turns a Koszul resolution of a quotient `𝒪_X/ℐ` into a resolution of
`i_*𝒪_Z`. This repository resolves the quotient — `Stacks.RegularSequence` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf` identify the Koszul quotient with `𝒪_X/ℐ`
(`koszulQuotientIsoIdealQuotient`) and give the quasi-isomorphism of the Koszul augmentation for
a Koszul-regular ideal sheaf — but every such statement stops at `𝒪_X/ℐ`, and the Chern classes
of [Stacks, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF) are those of `i_*𝒪_X` for the
zero section `i`. Nothing here is specific to Tag 0FEF, and the statement carries no tag: it is
an input, not the conclusion of a tag.

## Main results

* `Stacks.ClosedImmersion.structureSheafQuotientIso` is `𝒪_X / ℐ ≅ i_*𝒪_Z`, stated for a
  morphism of ringed spaces whose comorphism is an epimorphism, which is the only condition the
  isomorphism uses out of the three defining a closed immersion.
* `Stacks.ClosedImmersion.cokernelπ_comp_structureSheafQuotientIso_hom` pins it to the
  comorphism.
* `Stacks.ClosedImmersion.schemeStructureSheafQuotientIso` and
  `Stacks.ClosedImmersion.cokernelπ_comp_schemeStructureSheafQuotientIso_hom` are the same for a
  closed immersion of schemes, with the target written as
  `AlgebraicGeometry.Scheme.Modules.pushforward`, the spelling the derived category and the Chern
  classes use.

## References

* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
* [Stacks Project, Tag 01QO](https://stacks.math.columbia.edu/tag/01QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- **`𝒪_X / ℐ ≅ i_*𝒪_Z` for a morphism of ringed spaces with surjective comorphism.** The ideal
sheaf `ℐ` is the kernel of the comorphism `𝒪_X ⟶ i_*𝒪_Z`; when that comorphism is an epimorphism
— one of the three defining conditions of a closed immersion, Stacks 01C2, available as the
instance `Stacks.ClosedImmersion.epi_structureSheafHom` — it exhibits `i_*𝒪_Z` as the cokernel of
the inclusion of `ℐ`. -/
public def structureSheafQuotientIso {X Z : RingedSpace.{u, u}} (i : Z ⟶ X)
    [Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))] :
    cokernel (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))) ≅
      (SheafOfModules.pushforward.{u} (structureSheafHom i)).obj
        (SheafOfModules.unit (structureSheafRing Z)) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (ShortComplex.exact_kernel
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))).gIsCokernel

/-- **The isomorphism `𝒪_X / ℐ ≅ i_*𝒪_Z` is the one induced by the comorphism.** This is what
pins it down: without it the isomorphism would only say that the two objects are abstractly
isomorphic. -/
public theorem cokernelπ_comp_structureSheafQuotientIso_hom {X Z : RingedSpace.{u, u}}
    (i : Z ⟶ X) [Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))] :
    cokernel.π (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))) ≫
        (structureSheafQuotientIso i).hom =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (ShortComplex.exact_kernel
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i))).gIsCokernel
    WalkingParallelPair.one

/-- **`𝒪_X / ℐ ≅ i_*𝒪_Z` for a closed immersion of schemes**, the form in which the Chern classes
of the structure sheaf of a closed subscheme are computed. The comorphism of a closed immersion of
schemes is an epimorphism of sheaves of modules by
`Stacks.ClosedImmersion.epi_unitToPushforwardObjUnit_structureSheafHom`; no local-generation
hypothesis on the ideal sheaf is needed, so this does not go through
`Stacks.ClosedImmersion.isClosedImmersion_toShHom`. -/
public def schemeStructureSheafQuotientIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    cokernel (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.toLRSHom.toShHom))) ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  haveI := epi_unitToPushforwardObjUnit_structureSheafHom i
  structureSheafQuotientIso i.toLRSHom.toShHom

/-- The scheme-level isomorphism is the one induced by the comorphism. -/
public theorem cokernelπ_comp_schemeStructureSheafQuotientIso_hom {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    cokernel.π (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))) ≫
        (schemeStructureSheafQuotientIso i).hom =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom) :=
  have := epi_unitToPushforwardObjUnit_structureSheafHom i
  cokernelπ_comp_structureSheafQuotientIso_hom i.toLRSHom.toShHom

end Stacks.ClosedImmersion

end
