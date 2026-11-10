module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# The defining ideal sheaf of a closed subspace is a kernel

Let `Z ⊆ X` be a closed subspace of an algebraic space over a scheme `S` contained in a big fppf
site `B`.  Its defining ideal sheaf `AlgebraicGeometry.Space.definingIdealSheaf` of Stacks 03MB is
a `CategoryTheory.SheafOfModules.Submodule` of `𝒪_X` on the small étale site of `X`, given over an
étale chart by the kernel of the structure map of the inclusion.  This file identifies it, **as an
object**, with the categorical kernel of the structure projection `𝒪_X ⟶ i_*𝒪_Z` of
`AlgebraicGeometry.Space.structureProjection`.

## Main definitions

* `AlgebraicGeometry.Space.definingIdealSheafIsoKernel`: **the defining ideal sheaf of a closed
  subspace is the kernel of the structure projection**, as an `𝒪_X`-module on the small étale site.

## Main results

* `AlgebraicGeometry.Space.definingIdealSheafIsoKernel_hom_comp_ι` and
  `AlgebraicGeometry.Space.definingIdealSheafIsoKernel_inv_comp_ι`: the identification is
  compatible with the two inclusions into `𝒪_X`, so it introduces no twist of its own and is the
  canonical comparison.
* `AlgebraicGeometry.Space.preservesFiniteLimits_representedModulePushforward`: the second factor
  of the transport of a module on the representing scheme to the small étale site of the algebraic
  space it represents is left exact.  The left exactness of the whole transport is
  `AlgebraicGeometry.Space.preservesFiniteLimits_representedAssociatedModule` of
  `StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback`.  This is what
  carries a kernel presentation across the transport, so that the two ideal sheaves of a
  representable closed immersion are kernels of two morphisms with the same source and target;
  see the section *What this leaves owed* below.

## Implementation notes

Both inputs are in the library and carry no hypothesis:
`AlgebraicGeometry.Space.ker_structureProjection`
says that the sectionwise kernel `CategoryTheory.SheafOfModules.Submodule.ker` of the structure
projection *is* the defining ideal sheaf, and
`CategoryTheory.SheafOfModules.Submodule.kerIsoKernel` identifies a sectionwise kernel on an
arbitrary site with the categorical one.  The comparison is their composite.

The sectionwise kernel and the defining ideal sheaf are equal by `rfl` — that is how
`ker_structureProjection` is proved — but the two `toSheafOfModules` are *not* interchangeable in
practice: unifying them directly exhausts the heartbeat budget inside `whnf`, so the equation is
transported with `CategoryTheory.eqToIso` rather than left to defeq.  This is why
`AlgebraicGeometry.Space.eqToHom_toSheafOfModules_comp_ι` is proved first: with the submodule
generalized, the equation can be substituted, and the transport of the inclusion is then the
inclusion.

This supplies what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFunctorial.lean` and of the module
`Conormal` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection`
record as unavailable — a presentation of the defining ideal sheaf as a kernel on the small étale
site.  On the scheme side the corresponding comparison is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHomIso`, which identifies the
sectionwise `definingIdealOfHom` with the categorical `Stacks.ClosedImmersion.idealSheaf`; the two
levels are now presented in the same shape, which is the form in which the comparison of a closed
subspace of a representable algebraic space with the representing closed immersion of schemes —
still owed, see the file named above — can be stated.

No `stacks` attribute is claimed: the kernel presentation is a change of presentation of the
ideal sheaf of Stacks 03MB rather than a clause of that tag, and the left exactness of the
transport is Stacks 08H8 for the scheme's small étale site — proved there, not here — composed
with an equivalence.

## What this leaves owed

The comparison of the two ideal sheaves of a closed subspace of a *representable* algebraic space
as **objects** — the clause (2) of the module
`Conormal` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection`
— is *not* proved here, and this file does not reduce it to nothing.  What it reduces it to is one
square: both ideal sheaves are now kernels of a structure projection, and the transport carries the
scheme-side kernel to the kernel of the transported projection, so what remains is to identify that
transported projection with `AlgebraicGeometry.Space.structureProjection` of the closed subspace,
under the identifications of its source and target
(`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`,
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso` and
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`).  The implementation notes of the
file named above record that square, and the ring-level square it should follow from
(`AlgebraicGeometry.Space.representedStructureMapRing_square`).

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **The transport of a submodule along an equality of submodules carries the inclusion to the
inclusion.**  With the target submodule generalized the equality can be substituted, after which
the transport is the identity. -/
theorem eqToHom_toSheafOfModules_comp_ι {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R} {I I' : M.Submodule} (e : I = I') :
    eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules e) ≫ I'.ι = I.ι := by
  subst e
  simp

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **The defining ideal sheaf of a closed subspace is the kernel of the structure projection.**
The ideal sheaf `𝓘_Z ⊆ 𝒪_X` of Stacks 03MB, read as an `𝒪_X`-module on the small étale site of
`X`, is the categorical kernel of the canonical map `𝒪_X ⟶ i_*𝒪_Z` of
`AlgebraicGeometry.Space.structureProjection`.

The sectionwise kernel of the structure projection is the defining ideal sheaf
(`AlgebraicGeometry.Space.ker_structureProjection`), and a sectionwise kernel of a morphism of
sheaves of modules on any site is its categorical kernel
(`CategoryTheory.SheafOfModules.Submodule.kerIsoKernel`). -/
noncomputable def definingIdealSheafIsoKernel :
    (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      kernel (structureProjection B S hS X Z) :=
  eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (ker_structureProjection B S hS X Z).symm) ≪≫
    SheafOfModules.Submodule.kerIsoKernel (structureProjection B S hS X Z)

/-- The identification of the defining ideal sheaf with the kernel of the structure projection is
compatible with their inclusions into `𝒪_X`: it carries the inclusion of the kernel to the
inclusion of the ideal sheaf, so no twist of its own is introduced. -/
@[reassoc]
theorem definingIdealSheafIsoKernel_hom_comp_ι :
    (definingIdealSheafIsoKernel B S hS X Z).hom ≫
        kernel.ι (structureProjection B S hS X Z) =
      (definingIdealSheaf B S hS X Z).ι := by
  have h := SheafOfModules.Submodule.kerIsoKernel_hom_comp_ι (structureProjection B S hS X Z)
  simp only [definingIdealSheafIsoKernel, Iso.trans_hom, eqToIso.hom, Category.assoc, h]
  exact eqToHom_toSheafOfModules_comp_ι (ker_structureProjection B S hS X Z).symm

/-- The inverse identification is compatible with the inclusions as well. -/
@[reassoc]
theorem definingIdealSheafIsoKernel_inv_comp_ι :
    (definingIdealSheafIsoKernel B S hS X Z).inv ≫ (definingIdealSheaf B S hS X Z).ι =
      kernel.ι (structureProjection B S hS X Z) := by
  rw [← definingIdealSheafIsoKernel_hom_comp_ι B S hS X Z, Iso.inv_hom_id_assoc]

/-! ### Left exactness of the transport to a represented algebraic space -/

section Transport

variable (U : BigFppfOver B S hS)

/-- **Transport of modules along the equivalence of the two small étale sites preserves finite
limits**, being the functor of an equivalence. -/
noncomputable instance preservesFiniteLimits_representedModulePushforward :
    Limits.PreservesFiniteLimits (representedModulePushforward B S hS U) :=
  inferInstanceAs
    (Limits.PreservesFiniteLimits (representedSmallEtaleModuleEquivalence B S hS U).functor)

end Transport

end AlgebraicGeometry.Space

end
