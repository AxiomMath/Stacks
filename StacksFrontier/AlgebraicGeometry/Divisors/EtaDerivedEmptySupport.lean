module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafUnitIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedUnconditional

/-!
# The derived décalage of a divisor with empty support is the identity

Let `X` be a scheme and let `D ⊆ X` be an effective Cartier divisor whose support has no points
— equivalently, whose ideal sheaf is the unit ideal.  Then the inclusion `ℐ_D ⟶ 𝒪_X` is an
isomorphism, and the derived décalage `Lη_{ℐ_D} : D(𝒪_X) ⥤ D(𝒪_X)` is the identity functor.

The situation arises by restriction: the ideal sheaf of an effective Cartier divisor pulled back
to the complement of its support is the unit ideal, so the derived décalage attached to a divisor
does nothing away from that divisor.

## Main results

* `Stacks.Divisors.Eta.supportSet_comap_eq_empty`: an ideal sheaf pulled back along a morphism
  whose image misses its support has empty support.
* `Stacks.Divisors.Eta.isIso_idealSheafι_of_supportSet_eq_empty`: the ideal-sheaf inclusion of a
  closed subscheme with empty support is an isomorphism.
* `Stacks.Divisors.Eta.derivedEtaIsoId_of_supportSet_eq_empty`: **the derived décalage of an
  effective Cartier divisor with empty support is the identity functor of `D(𝒪_X)`.**

## Implementation notes

An ideal sheaf with empty support is the unit ideal sheaf, by
`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff`, and the closed subscheme it cuts
out is empty.  Sections of the structure sheaf of an empty scheme over any open form a
subsingleton, so the structure-sheaf map `𝒪_X ⟶ i_* 𝒪_D` whose kernel is the ideal sheaf is the
zero morphism, and the kernel inclusion of a zero morphism is an isomorphism.

The derived statement is `Stacks.IdealTorsion.Eta.derivedEtaIsoId` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafUnitIdeal`, whose hypothesis is exactly
the invertibility of the ideal inclusion.

## References

* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors.Eta

variable {X : Scheme.{u}}

/-- **An ideal sheaf pulled back along a morphism missing its support has empty support.** -/
theorem supportSet_comap_eq_empty {Y : Scheme.{u}} (I : X.IdealSheafData) (h : Y ⟶ X)
    (hh : ∀ y : Y, h.base y ∉ I.supportSet) : (I.comap h).supportSet = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy => hh y ?_
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    Scheme.IdealSheafData.support_comap] at hy
  exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 hy

/-- An ideal sheaf whose support has no points is the unit ideal sheaf. -/
theorem eq_top_of_supportSet_eq_empty (D : X.IdealSheafData) (h : D.supportSet = ∅) : D = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact TopologicalSpace.Closeds.ext h

/-- The structure-sheaf map `𝒪_X ⟶ i_* 𝒪_D` of the closed subscheme cut out by the unit ideal
sheaf is zero: that subscheme is empty, so every section of its structure sheaf is zero. -/
theorem unitToPushforwardObjUnit_top_eq_zero (X : Scheme.{u}) :
    SheafOfModules.unitToPushforwardObjUnit
        (RingedSpaceModuleAdjunction.structureSheafHom
          (⊤ : X.IdealSheafData).subschemeι.toLRSHom.toShHom) = 0 := by
  ext U
  exact Subsingleton.elim (α := Γ((⊤ : X.IdealSheafData).subscheme,
    (⊤ : X.IdealSheafData).subschemeι ⁻¹ᵁ U.unop)) _ _

/-- **The ideal-sheaf inclusion of a closed subscheme with empty support is an isomorphism.**
The ideal sheaf is the kernel of the structure-sheaf map `𝒪_X ⟶ i_* 𝒪_D`, which is zero because
the subscheme is empty, and the kernel inclusion of a zero morphism is an isomorphism. -/
theorem isIso_idealSheafι_of_supportSet_eq_empty (D : X.IdealSheafData)
    (h : D.supportSet = ∅) : IsIso (idealSheafι D) := by
  obtain rfl := eq_top_of_supportSet_eq_empty D h
  exact kernel.ι_of_zero (unitToPushforwardObjUnit_top_eq_zero X)

/-- **The derived décalage of an effective Cartier divisor with empty support is the identity
functor of `D(𝒪_X)`.**  The ideal inclusion is invertible, and the derived décalage of an
invertible ideal inclusion is the identity. -/
def derivedEtaIsoId_of_supportSet_eq_empty (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (h : D.supportSet = ∅) :
    (derivedEtaData D).functor ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheaf X.toRingedSpace.sheaf))) :=
  haveI := isIso_idealSheafι_of_supportSet_eq_empty D h
  Stacks.IdealTorsion.Eta.derivedEtaIsoId X.toRingedSpace (idealSheaf D) (idealSheafι D)
    (hasTorsionFreeResolutions D)

end Stacks.Divisors.Eta

end
