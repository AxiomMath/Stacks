module

public import StacksFrontier.AlgebraicGeometry.GenericPointDecomposition.Defs
public import StacksFrontier.AlgebraicGeometry.MeromorphicSectionsTensor.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Meromorphic sections are the tensor product with the meromorphic functions

The source's proof of part (2) of Stacks Tag 02OW is one sentence: *"since
`𝒦_X(F) = F ⊗_{𝒪_X} 𝒦_X` we see that (2) follows from the other statements"*. This file supplies
that identification, and reads off the quasi-coherence clause from it.

The sheaf of meromorphic sections is by definition (Tag 01X4) the extension of scalars of `F`
along `𝒪_X ⟶ 𝒦_X`, read again as an `𝒪_X`-module by restriction of scalars; extension of scalars
is the sectionwise tensor product of Tag 03CU followed by sheafification. The tensor product of
`𝒪_X`-modules (Tag 01CA) is the sectionwise tensor product followed by sheafification as well, and
on the nose the two sectionwise tensor products are the *same* presheaf: `𝒦_X(U) ⊗_{𝒪_X(U)} F(U)`
with the same restriction maps and the same `𝒪_X(U)`-action. What separates the two sheaves is
only the order of sheafification and restriction of scalars, and those commute
(`Stacks.SheafOfModules.RestrictScalarsSheafification.sheafificationRestrictScalarsIso`).

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicSectionsTensor.meromorphicSectionsIsoTensor`: the sheaf of
  meromorphic sections of `F` is the tensor product `𝒦_X ⊗_{𝒪_X} F`.
* `Stacks.AlgebraicGeometry.MeromorphicSectionsTensor.isQuasicoherent_meromorphicSections`: if the
  sheaf of meromorphic functions and `F` are both quasi-coherent, so is the sheaf of meromorphic
  sections of `F`.

## Implementation notes

The identification is by construction, not by a computation on sections: the two presheaf-level
tensor products are equal, so the comparison is the identity of the underlying presheaf and the
isomorphism comes from the commutation of sheafification with restriction of scalars.

Quasi-coherence of the tensor product is Stacks Tag 01CE, formalized as
`AlgebraicGeometry.tensor_isQC`. It is stated for a ringed space over
`structureSheafRing`, which for a scheme is
  `AlgebraicGeometry.Scheme.ringCatSheaf`
with the same underlying presheaf; the two spellings are definitionally equal but instance
resolution does not cross between them, so the two quasi-coherence hypotheses are transported into
that spelling before the tag is applied.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

open Stacks.AlgebraicGeometry.GenericPointDecomposition

variable (X : Scheme.{u}) (F : X.Modules)

/-- The sectionwise tensor product `U ↦ 𝒦_X(U) ⊗_{𝒪_X(U)} F(U)` of Tag 03CU, as a presheaf of
modules over the sheaf of total quotient rings. Sheafifying it is the sheaf of meromorphic
sections of `F`. -/
abbrev sectionwiseTensor : PresheafOfModules (totalQuotientRingCatSheaf X).obj :=
  Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsObj (AlgebraicGeometry.toTotalQuotientSheaf
    X.sheaf).hom F.val

/-- **`𝒦_X(F) = F ⊗_{𝒪_X} 𝒦_X`.** The tensor product of the sheaf of meromorphic functions with
`F` is the sheaf of meromorphic sections of `F`.

Both sides sheafify the same presheaf of abelian groups, `U ↦ 𝒦_X(U) ⊗_{𝒪_X(U)} F(U)`; they
differ only in whether the scalars are restricted from `𝒦_X` to `𝒪_X` before or after
sheafification. -/
def meromorphicSectionsIsoTensor :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
      (meromorphicFunctions X)).obj F ≅
      meromorphicSections X F :=
  Stacks.SheafOfModules.RestrictScalarsSheafification.sheafificationRestrictScalarsIso
    (toTotalQuotientRingCatSheaf X) (sectionwiseTensor X F)

/-- **Quasi-coherence of the sheaf of meromorphic sections, from quasi-coherence of the sheaf of
meromorphic functions.** This is the source's own reduction: `𝒦_X(F)` is the tensor product of
`𝒦_X` with `F`, and the tensor product of two quasi-coherent modules is quasi-coherent (Stacks
Tag 01CE). -/
theorem isQuasicoherent_meromorphicSections
    (hK : (meromorphicFunctions X).IsQuasicoherent) (hF : F.IsQuasicoherent) :
    (meromorphicSections X F).IsQuasicoherent := by
  let _ : SheafOfModules.IsQuasicoherent
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
        (meromorphicFunctions X) := hK
  let _ : SheafOfModules.IsQuasicoherent
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) F := hF
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (meromorphicSectionsIsoTensor X F)
    (_root_.AlgebraicGeometry.tensor_isQC X.toRingedSpace (meromorphicFunctions X) F)

end Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

end
