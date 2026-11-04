module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.LinearAlgebra.ExteriorPower.Localization
public import StacksFrontier.LinearAlgebra.ExteriorPower.LocalizationSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparing the stalks of an exterior power along a specialization

Let `F` be an `𝒪_X`-module on a scheme `X` and let `y ⤳ x` be a specialization of points. The
stalk of the `n`-th exterior power of `F` at a point is the `n`-th exterior power of the stalk
(`SheafOfModules.exteriorPowerStalkEquiv`, [Stacks, Tag 01CH]), at `x` over `𝒪_{X,x}` and at `y`
over `𝒪_{X,y}`. Comparing those two identifications along `y ⤳ x` is an identity about the
square

```
(⋀ⁿ F)_x  ───────▸  (⋀ⁿ F)_y
   │                    │
   ▾                    ▾
⋀ⁿ_{𝒪_{X,x}} F_x ──▸ ⋀ⁿ_{𝒪_{X,y}} F_y
```

whose bottom edge is `exteriorPower.mapTower` of the comparison `F_x ⟶ F_y`. This file proves
that the square commutes, and deduces that under the identification at `y` the image of `(⋀ⁿ F)_x`
inside `(⋀ⁿ F)_y` is the image of `⋀ⁿ_{𝒪_{X,x}} F_x` inside `⋀ⁿ_{𝒪_{X,y}} F_y`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquiv`:
  `SheafOfModules.exteriorPowerStalkEquiv` for the exterior algebra of an `𝒪_X`-module on a
  scheme.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquivₗ`: the same identification stated
  over `AlgebraicGeometry.Scheme.Modules.presheaf` and `X.presheaf`, with the module structures
  of `Stacks.ModuleStalkSpecialization`.

## Main results

* `AlgebraicGeometry.exists_germ_eq_of_fin`: finitely many elements of a stalk are germs of
  sections over one common open.
* `AlgebraicGeometry.isScalarTower_stalkSpecializes_stalk`: the scalar tower
  `𝒪_{X,x} → 𝒪_{X,y} → F_y` carried by a specialization.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquiv_symm_ιMulti_germ`: a wedge of germs
  of local sections of `F` is the germ of the ordered product of those sections.
* `AlgebraicGeometry.Scheme.Modules.stalkSpecializesₗ_comp_exteriorPowerStalkEquivₗ_symm`: the
  square above commutes.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquivₗ_image_range_stalkSpecializes`: the
  identification at `y` carries the image of `(⋀ⁿ F)_x` in `(⋀ⁿ F)_y` onto the image of
  `exteriorPower.mapTower n (stalkSpecializesₗ F h)`.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.ModuleStalkSpecialization

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The scalar tower `𝒪_{X,x} → 𝒪_{X,y} → F_y` for a specialization `y ⤳ x`: the action of
`𝒪_{X,x}` on `F_y` is by definition the action through the comparison of local rings. -/
theorem isScalarTower_stalkSpecializes_stalk (F : X.Modules) {x y : X} (h : y ⤳ x) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI := stalkModule F y
    letI := stalkSpecializesModule F h
    IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk y) (F.presheaf.stalk y) :=
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := stalkModule F y
  let := stalkSpecializesModule F h
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Finitely many elements of a stalk are germs of sections over one common open. -/
theorem exists_germ_eq_of_fin (F : X.Modules) (x : X) {n : ℕ} (v : Fin n → F.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Fin n → Γ(F, U)),
      ∀ i, F.presheaf.germ U x hx (s i) = v i := by
  choose U hU s hs using fun i ↦ TopCat.Presheaf.exists_germ_eq F.presheaf (v i)
  have hmem : x ∈ (↑(⨅ i, U i) : Set X) := by
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hU
  refine ⟨⨅ i, U i, hmem, fun i ↦ F.presheaf.map (homOfLE (iInf_le U i)).op (s i), fun i ↦ ?_⟩
  rw [F.presheaf.germ_res_apply]
  exact hs i

namespace Scheme.Modules

/-- The stalk of the `n`-th exterior power of an `𝒪_X`-module is the `n`-th exterior power of
its stalk: `SheafOfModules.exteriorPowerStalkEquiv` at the exterior algebra
`AlgebraicGeometry.Scheme.Modules.exteriorAlgebra F`. -/
@[ega "0 4.1.5" "special case"]
noncomputable abbrev exteriorPowerStalkEquiv (F : X.Modules) (n : ℕ) (x : X) :=
  SheafOfModules.exteriorPowerStalkEquiv (exteriorAlgebra F) (exteriorGenerator F)
    (isExteriorAlgebra_exteriorAlgebra F) n x

/-- A wedge of germs of local sections of `F` is the image under
`AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquiv` of the germ of the ordered product of
those sections in the exterior algebra. -/
theorem exteriorPowerStalkEquiv_symm_ιMulti_germ (F : X.Modules) (n : ℕ) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Fin n → Γ(F, U)) :
    letI := stalkModule F x
    (exteriorPowerStalkEquiv F n x).symm
        (exteriorPower.ιMulti _ n fun i ↦ F.presheaf.germ U x hx (s i)) =
      (exteriorPower F (n : ℤ)).presheaf.germ U x hx
        ((exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i ↦ (exteriorGenerator F).val.app (op U) (s i)) :=
  (LinearEquiv.symm_apply_eq _).2
    (SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd _ _ _ n x U hx s).symm

/-! ### Comparison along a specialization -/

/-- The stalk of `⋀ⁿ F` is `⋀ⁿ` of the stalk, stated over
`AlgebraicGeometry.Scheme.Modules.presheaf` and `X.presheaf` with the module structures of
`Stacks.ModuleStalkSpecialization`. -/
noncomputable def exteriorPowerStalkEquivₗ (F : X.Modules) (n : ℕ) (x : X) :
    letI := stalkModule F x
    letI := stalkModule (exteriorPower F (n : ℤ)) x
    ((exteriorPower F (n : ℤ)).presheaf.stalk x) ≃ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^n (F.presheaf.stalk x)) :=
  exteriorPowerStalkEquiv F n x

/-- `AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquiv_symm_ιMulti_germ` in the spelling
of `AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquivₗ`. -/
theorem exteriorPowerStalkEquivₗ_symm_ιMulti_germ (F : X.Modules) (n : ℕ) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Fin n → Γ(F, U)) :
    letI := stalkModule F x
    letI := stalkModule (exteriorPower F (n : ℤ)) x
    (exteriorPowerStalkEquivₗ F n x).symm
        (exteriorPower.ιMulti _ n fun i ↦ F.presheaf.germ U x hx (s i)) =
      (exteriorPower F (n : ℤ)).presheaf.germ U x hx
        ((exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i ↦ (exteriorGenerator F).val.app (op U) (s i)) :=
  exteriorPowerStalkEquiv_symm_ιMulti_germ F n x U hx s

/-- For a specialization `y ⤳ x`, under the identifications of
`AlgebraicGeometry.Scheme.Modules.exteriorPowerStalkEquivₗ` at the two points, the comparison
`(⋀ⁿ F)_x → (⋀ⁿ F)_y` of stalks is `exteriorPower.mapTower n` of the comparison `F_x → F_y`. -/
theorem stalkSpecializesₗ_comp_exteriorPowerStalkEquivₗ_symm (F : X.Modules) (n : ℕ) {x y : X}
    (h : y ⤳ x) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI := stalkModule F x
    letI := stalkModule F y
    letI := stalkSpecializesModule F h
    letI := stalkModule (exteriorPower F (n : ℤ)) x
    letI := stalkModule (exteriorPower F (n : ℤ)) y
    letI := stalkSpecializesModule (exteriorPower F (n : ℤ)) h
    haveI := isScalarTower_stalkSpecializes_stalk F h
    haveI := isScalarTower_stalkSpecializes_stalk (exteriorPower F (n : ℤ)) h
    stalkSpecializesₗ (exteriorPower F (n : ℤ)) h ∘ₗ
          (exteriorPowerStalkEquivₗ F n x).symm.toLinearMap =
      (exteriorPowerStalkEquivₗ F n y).symm.toLinearMap.restrictScalars
            (X.presheaf.stalk x) ∘ₗ
        exteriorPower.mapTower (S := X.presheaf.stalk y) n (stalkSpecializesₗ F h) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := stalkModule F x
  let := stalkModule F y
  let := stalkSpecializesModule F h
  let := stalkModule (exteriorPower F (n : ℤ)) x
  let := stalkModule (exteriorPower F (n : ℤ)) y
  let := stalkSpecializesModule (exteriorPower F (n : ℤ)) h
  have := isScalarTower_stalkSpecializes_stalk F h
  have := isScalarTower_stalkSpecializes_stalk (exteriorPower F (n : ℤ)) h
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  obtain ⟨U, hxU, s, hs⟩ := exists_germ_eq_of_fin F x v
  obtain rfl : (fun i ↦ F.presheaf.germ U x hxU (s i)) = v := funext hs
  show stalkSpecializesₗ (exteriorPower F (n : ℤ)) h
      ((exteriorPowerStalkEquivₗ F n x).symm
        (exteriorPower.ιMulti _ n fun i ↦ F.presheaf.germ U x hxU (s i))) =
    (exteriorPowerStalkEquivₗ F n y).symm
      (exteriorPower.mapTower (S := X.presheaf.stalk y) n (stalkSpecializesₗ F h)
        (exteriorPower.ιMulti _ n fun i ↦ F.presheaf.germ U x hxU (s i)))
  rw [exteriorPowerStalkEquivₗ_symm_ιMulti_germ, exteriorPower.mapTower_ιMulti]
  refine (germ_stalkSpecializes_apply (exteriorPower F (n : ℤ)) hxU h _).trans ?_
  have hgerm : (fun i ↦ stalkSpecializesₗ F h (F.presheaf.germ U x hxU (s i))) =
      fun i ↦ F.presheaf.germ U y (h.mem_open U.isOpen hxU) (s i) :=
    funext fun i ↦ germ_stalkSpecializes_apply F hxU h (s i)
  rw [hgerm, exteriorPowerStalkEquivₗ_symm_ιMulti_germ]

/-- The comparison along a specialization has the same image whether it is read as a morphism of
abelian groups or as `Stacks.ModuleStalkSpecialization.stalkSpecializesₗ`. -/
theorem range_stalkSpecializesₗ (F : X.Modules) {x y : X} (h : y ⤳ x) :
    letI := stalkModule F x
    letI := stalkSpecializesModule F h
    Set.range (stalkSpecializesₗ F h) = Set.range (F.presheaf.stalkSpecializes h) :=
  rfl

/-- For `y ⤳ x`, the identification at `y` carries the image of `(⋀ⁿ F)_x` in `(⋀ⁿ F)_y` onto
the image of `exteriorPower.mapTower n` of the comparison `F_x → F_y`. -/
theorem exteriorPowerStalkEquivₗ_image_range_stalkSpecializes (F : X.Modules) (n : ℕ) {x y : X}
    (h : y ⤳ x) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI := stalkModule F x
    letI := stalkModule F y
    letI := stalkSpecializesModule F h
    letI := stalkModule (exteriorPower F (n : ℤ)) y
    haveI := isScalarTower_stalkSpecializes_stalk F h
    exteriorPowerStalkEquivₗ F n y ''
          Set.range ((exteriorPower F (n : ℤ)).presheaf.stalkSpecializes h) =
      Set.range (exteriorPower.mapTower (S := X.presheaf.stalk y) n (stalkSpecializesₗ F h)) := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := stalkModule F x
  let := stalkModule F y
  let := stalkSpecializesModule F h
  let := stalkModule (exteriorPower F (n : ℤ)) x
  let := stalkModule (exteriorPower F (n : ℤ)) y
  let := stalkSpecializesModule (exteriorPower F (n : ℤ)) h
  have := isScalarTower_stalkSpecializes_stalk F h
  have := isScalarTower_stalkSpecializes_stalk (exteriorPower F (n : ℤ)) h
  rw [← range_stalkSpecializesₗ (exteriorPower F (n : ℤ)) h, ← Set.range_comp]
  have key : (exteriorPowerStalkEquivₗ F n y ∘ stalkSpecializesₗ (exteriorPower F (n : ℤ)) h) =
      exteriorPower.mapTower (S := X.presheaf.stalk y) n (stalkSpecializesₗ F h) ∘
        exteriorPowerStalkEquivₗ F n x :=
    funext fun ω ↦ (LinearEquiv.eq_symm_apply _).1 (by
      simpa using LinearMap.congr_fun (stalkSpecializesₗ_comp_exteriorPowerStalkEquivₗ_symm F n h)
        (exteriorPowerStalkEquivₗ F n x ω))
  rw [key, EquivLike.range_comp]

end Scheme.Modules

end AlgebraicGeometry

end
