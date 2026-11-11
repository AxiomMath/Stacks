module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectivizedNormalCone
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalCone

/-!
# `X' ∩ E` is the projectivized normal cone

Let `X` be a scheme, `ℐ` a quasi-coherent sheaf of ideals on `X` with closed subscheme `Z`,
`X' ⟶ X` the blowup of `X` in `Z`, and `b : W ⟶ 𝐏¹_X` the blowup of `𝐏¹_X` in `∞(Z)` with
exceptional divisor `E`, so that `X'` is a closed subscheme of `W`
(`Stacks.Chow.blowUpToBlowupAtInfinity`). This file proves assertion (6) of [Stacks, Tag 0FBG]:

  `X' ∩ E = Proj_Z(𝒞_{Z/X,*})`,

the intersection of `X'` and `E` inside `W` being identified, over `Z`, with the projectivized
normal cone `P_ZX` of `Z` in `X` (`Stacks.Conormal.projectivizedNormalCone`).

`X' ∩ E` is the closed subscheme of `E` cut out by the ideal of `X'`
(`Stacks.Chow.strictTransformIdealOnExceptional`), the form in which assertion (7)
(`Stacks.Chow.normalConeToExceptionalDivisor_spec`) speaks of it.

## The route

* `X' ∩ E` is the fibre product `E ×_W X'` of two closed immersions; so is the closed subscheme of
  `X'` cut out by the inverse image of `E`, and by assertion (3)
  (`Stacks.Chow.comap_exceptionalIdealAtInfinity`) that inverse image is the exceptional divisor of
  `X' ⟶ X`. Hence `X' ∩ E` is the exceptional divisor of the blowup `X' ⟶ X`.
* The exceptional divisor of `X' ⟶ X` is `Proj_Z(𝒞_{Z/X,*})`
  (`Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectivizedNormalCone`).

The source deduces (6) from (5) on the chart `D₊(f⁽¹⁾)`; the route above goes through (3) instead
and does not need the affine description of `E`.

## Main results

* `Stacks.Chow.isPullback_strictTransformOnExceptional`: `X' ∩ E = E ×_W X'`.
* `Stacks.Chow.isPullback_exceptionalDivisor_blowUpToBlowupAtInfinity`: the exceptional divisor of
  `X' ⟶ X` is `X' ×_W E`.
* `Stacks.Chow.strictTransformOnExceptionalIsoProjectivizedNormalCone` and
  `Stacks.Chow.strictTransformOnExceptionalIsoProjectivizedNormalCone_hom_toBase`:
  **assertion (6)**, `X' ∩ E ≅ Proj_Z(𝒞_{Z/X,*})` over `Z`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-- The morphism `X' ∩ E ⟶ X'`: the closed subscheme `X' ∩ E` of `E` lies in `X'`. -/
def strictTransformOnExceptionalToBlowUp :
    (strictTransformIdealOnExceptional ℐ).subscheme ⟶ blowUp ℐ :=
  IsClosedImmersion.lift (blowUpToBlowupAtInfinity ℐ)
    ((strictTransformIdealOnExceptional ℐ).subschemeι ≫
      (exceptionalIdealAtInfinity ℐ).subschemeι)
    (Scheme.IdealSheafData.le_map_comap (strictTransformIdealAtInfinity ℐ)
      (exceptionalIdealAtInfinity ℐ).subschemeι)

/-- `X' ∩ E ⟶ X' ⟶ W` is `X' ∩ E ⟶ E ⟶ W`. -/
@[reassoc]
theorem strictTransformOnExceptionalToBlowUp_comp :
    strictTransformOnExceptionalToBlowUp ℐ ≫ blowUpToBlowupAtInfinity ℐ =
      (strictTransformIdealOnExceptional ℐ).subschemeι ≫
        (exceptionalIdealAtInfinity ℐ).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- **`X' ∩ E` is the fibre product `E ×_W X'`.** -/
theorem isPullback_strictTransformOnExceptional :
    IsPullback (strictTransformIdealOnExceptional ℐ).subschemeι
      (strictTransformOnExceptionalToBlowUp ℐ) (exceptionalIdealAtInfinity ℐ).subschemeι
      (blowUpToBlowupAtInfinity ℐ) :=
  isPullback_of_isClosedImmersion _ _ _ _ (strictTransformOnExceptionalToBlowUp_comp ℐ).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; rfl)

/-- The inverse image of `E` on `X'` is the exceptional divisor of `X' ⟶ X` (assertion (3)), so
the exceptional ideal of `X' ⟶ X` maps into `E`. -/
theorem exceptionalIdealAtInfinity_le_map_exceptionalIdeal :
    exceptionalIdealAtInfinity ℐ ≤ (exceptionalIdeal ℐ).map (blowUpToBlowupAtInfinity ℐ) := by
  rw [← comap_exceptionalIdealAtInfinity ℐ]
  exact Scheme.IdealSheafData.le_map_comap _ _

/-- The morphism from the exceptional divisor of `X' ⟶ X` to `E`. -/
def exceptionalDivisorToExceptionalAtInfinity :
    exceptionalDivisor ℐ ⟶ exceptionalDivisorAtInfinity ℐ :=
  Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) (exceptionalIdealAtInfinity ℐ)
    (blowUpToBlowupAtInfinity ℐ) (exceptionalIdealAtInfinity_le_map_exceptionalIdeal ℐ)

/-- **The exceptional divisor of `X' ⟶ X` is the fibre product `X' ×_W E`**, by
assertion (3). -/
theorem isPullback_exceptionalDivisor_blowUpToBlowupAtInfinity :
    IsPullback (exceptionalIdeal ℐ).subschemeι (exceptionalDivisorToExceptionalAtInfinity ℐ)
      (blowUpToBlowupAtInfinity ℐ) (exceptionalIdealAtInfinity ℐ).subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      comap_exceptionalIdealAtInfinity])

/-- `X' ∩ E`, as a closed subscheme of `E`, is the exceptional divisor of `X' ⟶ X`. -/
def strictTransformOnExceptionalIsoExceptionalDivisor :
    (strictTransformIdealOnExceptional ℐ).subscheme ≅ exceptionalDivisor ℐ :=
  (isPullback_strictTransformOnExceptional ℐ).isoIsPullback _ _
    (isPullback_exceptionalDivisor_blowUpToBlowupAtInfinity ℐ).flip

@[reassoc]
theorem strictTransformOnExceptionalIsoExceptionalDivisor_hom_subschemeι :
    (strictTransformOnExceptionalIsoExceptionalDivisor ℐ).hom ≫
        (exceptionalIdeal ℐ).subschemeι =
      strictTransformOnExceptionalToBlowUp ℐ :=
  (isPullback_strictTransformOnExceptional ℐ).isoIsPullback_hom_snd _ _
    (isPullback_exceptionalDivisor_blowUpToBlowupAtInfinity ℐ).flip

/-- **Stacks 0FBG, assertion (6).** `X' ∩ E = Proj_Z(𝒞_{Z/X,*})`: the intersection of the blowup
`X'` of `X` in `Z` with the exceptional divisor `E` of the blowup at infinity, as a closed
subscheme of `E`, is the projectivized normal cone of `Z` in `X`, the relative `Proj` over `Z` of
the conormal algebra. -/
@[stacks 0FBG "(6): X' ∩ E = Proj_Z(C_{Z/X,*})"]
def strictTransformOnExceptionalIsoProjectivizedNormalCone :
    (strictTransformIdealOnExceptional ℐ).subscheme ≅
      Stacks.Conormal.projectivizedNormalCone ℐ.subschemeι :=
  strictTransformOnExceptionalIsoExceptionalDivisor ℐ ≪≫
    Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectivizedNormalCone ℐ

/-- **Stacks 0FBG, assertion (6), over `Z`.** The identification `X' ∩ E ≅ Proj_Z(𝒞_{Z/X,*})`
is one of schemes over `Z`: followed by the projection `P_ZX ⟶ Z ⟶ X` it is the inclusion
`X' ∩ E ⟶ E ⟶ W` followed by `W ⟶ X`. -/
@[stacks 0FBG "(6): the identification X' ∩ E = Proj_Z(C_{Z/X,*}) is over Z"]
theorem strictTransformOnExceptionalIsoProjectivizedNormalCone_hom_toBase :
    (strictTransformOnExceptionalIsoProjectivizedNormalCone ℐ).hom ≫
        Stacks.Conormal.projectivizedNormalConeToBase ℐ.subschemeι ≫ ℐ.subschemeι =
      (strictTransformIdealOnExceptional ℐ).subschemeι ≫
        (exceptionalIdealAtInfinity ℐ).subschemeι ≫ blowupAtInfinityToBase ℐ := by
  rw [strictTransformOnExceptionalIsoProjectivizedNormalCone, Iso.trans_hom, Category.assoc,
    Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectivizedNormalCone_hom_toBase_assoc,
    Scheme.IdealSheafData.subschemeMap_subschemeι,
    strictTransformOnExceptionalIsoExceptionalDivisor_hom_subschemeι_assoc,
    ← strictTransformOnExceptionalToBlowUp_comp_assoc, blowUpToBlowupAtInfinity_comp_toBase]

end Stacks.Chow

end
