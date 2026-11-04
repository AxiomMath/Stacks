module

public import StacksFrontier.AlgebraicGeometry.ClosedSubschemeProjQuotient.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The saturation identification as an equality of ideal sheaves

Let `i : Z ⟶ Proj 𝒮` be a closed immersion and `I` its graded ideal of equations.
`Stacks.ClosedSubschemeProjQuotient.SaturationIdentification 𝒮 i`, an isomorphism
`Z ≅ Proj (𝒮 / I)` over `Proj 𝒮`, is equivalent to the equality of kernel ideal sheaves
`i.ker = (ambientHom 𝒮 i).ker` on `Proj 𝒮`. That equality may be checked on the kernels of the
maps on sections over a family of affine opens covering `Proj 𝒮`, in particular over standard
opens `D₊(f k)`.

## Main definitions

* `Stacks.ProjQuotientSaturationKer.standardAffineChart`: the standard open `D₊(f)`, for `f`
  homogeneous of positive degree, as an affine open of `Proj 𝒮`.

## Main results

* `Stacks.ProjQuotientSaturationKer.ker_eq_of_saturationIdentification`: the identification
  implies `i.ker = (ambientHom 𝒮 i).ker`.
* `Stacks.ProjQuotientSaturationKer.saturationIdentification_of_ker_eq`: the converse.
* `Stacks.ProjQuotientSaturationKer.saturationIdentification_iff_ker_eq`: the two together, as an
  `Iff`.
* `Stacks.ProjQuotientSaturationKer.saturationIdentification_of_ker_app_eq`: the identification
  holds if the kernels of the two maps on sections agree over each member of a family of affine
  opens whose supremum is `⊤`.
* `Stacks.ProjQuotientSaturationKer.saturationIdentification_of_ker_app_eq_basicOpen`: the same
  with the family taken to be standard opens `D₊(f k)` of homogeneous elements of positive degree.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Stacks.ClosedSubschemeProjQuotient

universe u

namespace Stacks.ProjQuotientSaturationKer

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒮 : ℕ → Submodule R S)
  [GradedAlgebra 𝒮]

/-! ### The equivalence with an equality of ideal sheaves -/

/-- If `Z` is isomorphic to `Proj (𝒮 / I)` over `Proj 𝒮`, then `i` and `ambientHom 𝒮 i` have the
same kernel ideal sheaf. -/
public theorem ker_eq_of_saturationIdentification {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] (h : SaturationIdentification 𝒮 i) :
    i.ker = (ambientHom 𝒮 i).ker := by
  obtain ⟨e, he⟩ := h
  conv_lhs => rw [← he]
  exact Scheme.Hom.ker_comp_of_isIso e.hom (ambientHom 𝒮 i)

/-- If `i` and `ambientHom 𝒮 i` have the same kernel ideal sheaf, then `Z` is isomorphic to
`Proj (𝒮 / I)` over `Proj 𝒮`. -/
public theorem saturationIdentification_of_ker_eq {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] (h : i.ker = (ambientHom 𝒮 i).ker) :
    SaturationIdentification 𝒮 i := by
  have : IsClosedImmersion (ambientHom 𝒮 i) := isClosedImmersion_ambientHom 𝒮 i
  have : IsIso (IsClosedImmersion.lift (ambientHom 𝒮 i) i h.symm.le) :=
    IsClosedImmersion.isIso_lift (ambientHom 𝒮 i) i h.symm
  exact ⟨asIso (IsClosedImmersion.lift (ambientHom 𝒮 i) i h.symm.le),
    IsClosedImmersion.lift_fac (ambientHom 𝒮 i) i h.symm.le⟩

/-- `Z` is isomorphic to `Proj (𝒮 / I)` over `Proj 𝒮` if and only if `i` and `ambientHom 𝒮 i`
have the same kernel ideal sheaf. -/
public theorem saturationIdentification_iff_ker_eq {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] :
    SaturationIdentification 𝒮 i ↔ i.ker = (ambientHom 𝒮 i).ker :=
  ⟨ker_eq_of_saturationIdentification 𝒮 i, saturationIdentification_of_ker_eq 𝒮 i⟩

/-! ### Reduction to an affine open cover -/

/-- Let `U k` be affine opens of `Proj 𝒮` whose supremum is `⊤`. If, over each `U k`, the maps
on sections induced by `i` and by `ambientHom 𝒮 i` have the same kernel, then
`SaturationIdentification 𝒮 i` holds. -/
public theorem saturationIdentification_of_ker_app_eq {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] {ι : Type*} (U : ι → (AlgebraicGeometry.Proj 𝒮).affineOpens)
    (hU : ⨆ k, (U k).1 = ⊤)
    (H : ∀ k, RingHom.ker (i.app (U k)).hom =
      RingHom.ker ((ambientHom 𝒮 i).app (U k)).hom) :
    SaturationIdentification 𝒮 i := by
  have : IsClosedImmersion (ambientHom 𝒮 i) := isClosedImmersion_ambientHom 𝒮 i
  refine saturationIdentification_of_ker_eq 𝒮 i
    (Scheme.IdealSheafData.ext_of_iSup_eq_top U hU fun k ↦ ?_)
  rw [Scheme.Hom.ker_apply i (U k), Scheme.Hom.ker_apply (ambientHom 𝒮 i) (U k), H k]

/-- The standard open `D₊(f)` of `Proj 𝒮`, for `f` homogeneous of positive degree, as an affine
open. -/
public def standardAffineChart {m : ℕ} (f : S) (hf : f ∈ 𝒮 m) (hm : 0 < m) :
    (AlgebraicGeometry.Proj 𝒮).affineOpens :=
  ⟨AlgebraicGeometry.Proj.basicOpen 𝒮 f,
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮 f hf hm⟩

/-- The underlying open of `standardAffineChart 𝒮 f hf hm` is `D₊(f)`. -/
@[simp] public theorem standardAffineChart_coe {m : ℕ} (f : S) (hf : f ∈ 𝒮 m) (hm : 0 < m) :
    (standardAffineChart 𝒮 f hf hm).1 = AlgebraicGeometry.Proj.basicOpen 𝒮 f := rfl

/-- Let `f k` be homogeneous elements of positive degrees whose standard opens cover `Proj 𝒮`.
If, over each `D₊(f k)`, the maps on sections induced by `i` and by `ambientHom 𝒮 i` have the same
kernel, then `SaturationIdentification 𝒮 i` holds. -/
public theorem saturationIdentification_of_ker_app_eq_basicOpen {Z : Scheme.{u}}
    (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] {ι : Type*} (f : ι → S) (d : ι → ℕ)
    (hf : ∀ k, f k ∈ 𝒮 (d k)) (hd : ∀ k, 0 < d k)
    (hcover : ⨆ k, AlgebraicGeometry.Proj.basicOpen 𝒮 (f k) = ⊤)
    (H : ∀ k, RingHom.ker (i.app (standardAffineChart 𝒮 (f k) (hf k) (hd k))).hom =
      RingHom.ker ((ambientHom 𝒮 i).app (standardAffineChart 𝒮 (f k) (hf k) (hd k))).hom) :
    SaturationIdentification 𝒮 i :=
  saturationIdentification_of_ker_app_eq 𝒮 i
    (fun k ↦ standardAffineChart 𝒮 (f k) (hf k) (hd k)) hcover H

end Stacks.ProjQuotientSaturationKer

end
