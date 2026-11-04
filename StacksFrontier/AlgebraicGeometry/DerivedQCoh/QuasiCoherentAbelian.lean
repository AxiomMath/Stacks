module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-coherent modules on `Spec R` form an abelian category

The quasi-coherent `𝒪_{Spec R}`-modules are closed under kernels
(`Stacks.AffineTilde.isQuasicoherent_kernel`) and cokernels
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`); this file adds the two remaining
closure properties — the zero object and finite products — and so obtains the `Abelian` instance
on the full subcategory `QCoh(𝒪_{Spec R})` through Mathlib's
`CategoryTheory.ObjectProperty.instAbelianFullSubcategory`.

Both new closure properties come from the tilde functor. The zero object is `0^~`, and a finite
product of quasi-coherent modules is `(M ⨯ N)^~` for the corresponding product of modules,
because `AlgebraicGeometry.tilde.functor` preserves finite limits
(`AlgebraicGeometry.tilde.preservesFiniteLimits`). Only the binary case and the zero
object are needed, since `CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts.mk'` reduces
all finite products to those.

The point of the abelian structure is that it makes `D(QCoh(𝒪_{Spec R}))` — the left-hand vertex
of the diagram of Stacks 06Z0 — exist as a derived category, and that the inclusion
`CategoryTheory.ObjectProperty.ι` into all `𝒪_{Spec R}`-modules is then exact, by Mathlib's
`CategoryTheory.ObjectProperty.preservesKernels_ι` and
`CategoryTheory.ObjectProperty.preservesCokernels_ι`.

## Main results

* `Stacks.DerivedQCoh.isQuasicoherent_prod`: a binary product of quasi-coherent modules on
  `Spec R` is quasi-coherent.
* the instances `CategoryTheory.ObjectProperty.ContainsZero`,
  `CategoryTheory.ObjectProperty.IsClosedUnderCokernels` and
  `CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts` for
  `AlgebraicGeometry.SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf`, from which
  `Abelian` of the full subcategory follows.

## Implementation notes

The closure properties are stated for the object property on
`AlgebraicGeometry.SheafOfModules.{u} (Spec R).ringCatSheaf` rather than for the `Scheme.Modules`
spelling, because that is the type of `AlgebraicGeometry.SheafOfModules.isQuasicoherent` and
hence the one Mathlib's full-subcategory machinery sees. The library's kernel and cokernel results
are stated for `AlgebraicGeometry.Scheme.Modules` but apply directly at this type.

## References

* [The Stacks Project, Lemma 29.24.1 (01IC)](https://stacks.math.columbia.edu/tag/01IC)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry
open scoped ZeroObject

universe u

namespace Stacks.DerivedQCoh

variable (R : CommRingCat.{u})

/-- A binary product of quasi-coherent `𝒪_{Spec R}`-modules is quasi-coherent: both factors are
in the essential image of the tilde functor, which preserves finite limits, so the product is the
tilde of the product of the corresponding modules. -/
theorem isQuasicoherent_prod {M N : SheafOfModules.{u} (Spec R).ringCatSheaf}
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) : (M ⨯ N).IsQuasicoherent := by
  obtain ⟨a, ⟨eM⟩⟩ : (tilde.functor R).essImage M := by rw [essImage_tilde]; exact hM
  obtain ⟨b, ⟨eN⟩⟩ : (tilde.functor R).essImage N := by rw [essImage_tilde]; exact hN
  have : PreservesFiniteLimits (tilde.functor R) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits R
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (PreservesLimitPair.iso (tilde.functor R) a b ≪≫ prod.mapIso eM eN) inferInstance

/-- `0^~` is a zero object which is quasi-coherent, so the quasi-coherent modules contain a zero
object. -/
instance containsZero_isQuasicoherent :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ContainsZero :=
  ⟨(tilde.functor R).obj 0, (tilde.functor R).map_isZero (isZero_zero _), inferInstance⟩

/-- The quasi-coherent `𝒪_{Spec R}`-modules are closed under cokernels, in the form Mathlib's
full-subcategory machinery consumes. The mathematical content is
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`. -/
instance isClosedUnderCokernels_isQuasicoherent :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have hX := hf.1
    have hY := hf.2
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (Scheme.Modules.isQuasicoherent_cokernel (X := Spec R) f)

/-- The quasi-coherent `𝒪_{Spec R}`-modules are closed under binary products. -/
instance isClosedUnderBinaryProducts_isQuasicoherent :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro _ ⟨h⟩
    have hlim : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) (limit h.diag) :=
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        (HasLimit.isoOfNatIso (diagramIsoPair h.diag)).symm
        (isQuasicoherent_prod R (h.prop_diag_obj ⟨WalkingPair.left⟩)
          (h.prop_diag_obj ⟨WalkingPair.right⟩))
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (h.isLimit.conePointUniqueUpToIso (limit.isLimit h.diag)).symm hlim

/-- The quasi-coherent `𝒪_{Spec R}`-modules are closed under finite products. -/
instance isClosedUnderFiniteProducts_isQuasicoherent :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderFiniteProducts :=
  IsClosedUnderFiniteProducts.mk'

/-- **Stacks Project, Tag 01IC (abelian category).** The quasi-coherent modules on `Spec R` form
an abelian category, kernels, cokernels and finite products being computed as in all
`𝒪_{Spec R}`-modules. -/
@[stacks 01IC "abelian category"]
instance abelianQuasiCoherent :
    Abelian (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  inferInstance

end Stacks.DerivedQCoh

end
