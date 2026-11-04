module

public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent

/-!
# A quasi-coherent sheaf of ideals as a submodule of the structure sheaf

A quasi-coherent sheaf of ideals on a scheme `X` is spelled in this library in two ways. Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData` records it by its ideal of sections over each *affine*
open, which is what the ideal-power multiples `I ^ n • M` and the closed subscheme it cuts out are
built from. The other spelling is a submodule of the structure sheaf viewed as a sheaf of modules,
`(SheafOfModules.unit X.ringCatSheaf).Submodule`, which is what the annihilator subsheaves of
[Stacks, Tag 01PQ] and the Artin–Rees lemma of [Stacks, Tag 01YA] are stated at.

This file passes from the first spelling to the second, once: `I.unitSubmodule` is the kernel of
`𝒪_X ⟶ i_* 𝒪_Z` for the closed immersion `i` of the subscheme cut out by `I`, its sections over
an affine open are `I`'s own ideal there, and it is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` — the ideal sheaf data `I`, read as a
  submodule of the structure sheaf.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine` — over an affine open the
  sections of `I.unitSubmodule` are the ideal `I.ideal U`.
* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent` — `I.unitSubmodule` is
  quasi-coherent.

## Implementation notes

The kernel is the embedded one,
`Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule`, so that it really is
a submodule of the structure sheaf rather than an object mapping monomorphically to it; its
sections over an open are a submodule of the sections there by construction, which is what makes
`unitSubmodule_obj_affine` an equality of ideals. Quasi-coherence is only available for the
categorical kernel — it is `AlgebraicGeometry.isQuasicoherent_kernel_unitToPushforwardObjUnit`,
[Stacks, Tag 01R8], applied to the closed immersion `I.subschemeι`, which is quasi-compact — and
is transported across `AlgebraicGeometry.SheafOfModules.Submodule.kernelIso`.

Sections over a *non*-affine open are not computed: `Scheme.IdealSheafData` carries no data
there, and the ideal of sections of the kernel over a general open is the sheafification of the
affine-local data, not a pointwise power. Every consumer of this bridge tests membership on
affine opens.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- A quasi-coherent sheaf of ideals, given by its affine-local ideal data, read as a submodule
of the structure sheaf viewed as a sheaf of modules.

It is the kernel of the map `𝒪_X ⟶ i_* 𝒪_Z` to the structure sheaf of the closed subscheme `Z`
cut out by `I`, taken as an embedded submodule of `𝒪_X`. -/
public noncomputable def unitSubmodule (I : X.IdealSheafData) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule :=
  Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule
    (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)

/-- Over an affine open the sections of `I.unitSubmodule` are the ideal `I.ideal U`: a function
is killed by the map to the structure sheaf of the subscheme cut out by `I` exactly when it lies
in that ideal. -/
public lemma unitSubmodule_obj_affine (I : X.IdealSheafData) (U : X.affineOpens) :
    I.unitSubmodule.toSubmodule.obj (op U.1) = I.ideal U := by
  ext x
  have h : ((I.subschemeι.app U.1).hom (show Γ(X, U.1) from x) = 0) ↔
      (show Γ(X, U.1) from x) ∈ I.ideal U := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app]
  exact h

/-- The submodule of the structure sheaf attached to a sheaf of ideals is quasi-coherent.

This is [Stacks, Tag 01R8] for the quasi-compact morphism `I.subschemeι`, transported from the
categorical kernel to the embedded one. -/
instance unitSubmodule_isQuasicoherent (I : X.IdealSheafData) :
    I.unitSubmodule.toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (SheafOfModules.Submodule.kernelIso
      (SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom)).symm
    (isQuasicoherent_kernel_unitToPushforwardObjUnit I.subschemeι)

end AlgebraicGeometry.Scheme.IdealSheafData

end
