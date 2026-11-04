module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderThickeningSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionSheaf

/-!
# The degree-one extension of the canonical connection, and its integrability

Fix a global crystalline situation of [Stacks, Tag 07MF], a crystal `F` in `𝒪_{X/S}`-modules on
`Cris(X/S)` and an object `(U, T, δ)` with second-order universal thickening `(U, T'', δ'')` of
[Stacks, Tag 07J3].  The degree-one extension of the canonical connection
(`...SmallSite.crystalConnectionExtensionApp`, and `...SmallSite.crystalConnectionExtension` as a
morphism of sheaves of abelian groups) is the alternating sum `q₀₁^* z + q₁₂^* z - q₀₂^* z` of the
three restrictions to `T''` of a section `z` of `F_T ⊗ Ω`, read in `F_T ⊗ Ω²` through the
retraction of the split monomorphism `F_T ⊗ Ω² ⟶ q₀_* F_{T''}`.  It is given by the rule
`∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` of [Stacks, Remark 07I0], the rule determines it, and
`∇ ∘ ∇ = 0`.  The two formulas of [Stacks, Tag 07J3], `q₀₁^* ω + q₁₂^* ω - q₀₂^* ω = d ω` and
`q₁₂^* ω · q₀₁^* ω' = ω' ∧ ω`, are `Crystalline.secondOrderThickening_alternatingSum_inr` and
`Crystalline.secondOrderThickeningQ₁₂_inr_mul_Q₀₁_inr`.

## Main definitions

* `Crystalline.dpWedgeSheafHom` and `Crystalline.tensorWedgeHom` — the exterior products
  `Ω ⊗ Ω ⟶ Ω²` and `(N ⊗ Ω) ⊗ Ω ⟶ N ⊗ Ω²`; `...SmallSite.crystalWedge` is `z ∧ ω`.
* `...SmallSite.crystalCurvatureApp` — the alternating sum.
* `...SmallSite.crystalConnectionExtensionApp`, `...SmallSite.crystalConnectionExtension` — the
  degree-one extension.

## Main results

* `...SmallSite.crystalConnectionExtensionApp_tmul` — the rule `∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω`.
* `...SmallSite.eq_crystalConnectionExtensionApp` — uniqueness of a family given by the rule.
* `...SmallSite.crystalConnection_comp_crystalConnectionExtension` — **integrability**.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

/-! ### The three maps `𝒪_{T'} ⟶ 𝒪_{T''}` on the ideal of the diagonal -/

section Formulas

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  (W : (Opens ↑T.scheme)ᵒᵖ)

/-- `q₀₁ : 𝒪_{T'} ⟶ 𝒪_{T''}` carries `(0, ω)` to `(0, ω, 0, 0)`. -/
theorem secondOrderThickeningQ₀₁_inr (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    ((secondOrderThickeningQ₀₁ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) =
      secondOrderExtMk (q := dpWedge T Y f) 0 ω 0 0 := rfl

/-- `q₀₂ : 𝒪_{T'} ⟶ 𝒪_{T''}` carries `(0, ω)` to `(0, ω, ω, 0)`. -/
theorem secondOrderThickeningQ₀₂_inr (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    ((secondOrderThickeningQ₀₂ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) =
      secondOrderExtMk (q := dpWedge T Y f) 0 ω ω 0 := rfl

/-- `q₁₂ : 𝒪_{T'} ⟶ 𝒪_{T''}` carries `(0, ω)` to `(0, 0, ω, d ω)`. -/
theorem secondOrderThickeningQ₁₂_inr (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    ((secondOrderThickeningQ₁₂ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) =
      secondOrderExtMk (q := dpWedge T Y f) 0 0 ω (dpDeRham T Y f W ω) :=
  secondOrderExt_ext rfl (map_zero (dpDerivationHom T Y f W)) rfl rfl

/-- **The first formula of [Stacks, Tag 07J3]**: `q₀₁^* ω + q₁₂^* ω - q₀₂^* ω = d ω` for a
section `ω` of the ideal of the diagonal of `T'`, read in the top summand of `𝒪_{T''}`. -/
theorem secondOrderThickening_alternatingSum_inr (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    ((secondOrderThickeningQ₀₁ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) +
        ((secondOrderThickeningQ₁₂ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) -
        ((secondOrderThickeningQ₀₂ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) =
      secondOrderExtMk (q := dpWedge T Y f) 0 0 0 (dpDeRham T Y f W ω) := by
  rw [secondOrderThickeningQ₀₁_inr, secondOrderThickeningQ₁₂_inr, secondOrderThickeningQ₀₂_inr]
  exact (congrArg (· - secondOrderExtMk (q := dpWedge T Y f) 0 ω ω 0)
    (secondOrderExt_inl_add_inr_eq ω ω (dpDeRham T Y f W ω))).trans (add_sub_cancel_left _ _)

/-- **The second formula of [Stacks, Tag 07J3]**: `q₁₂^* ω · q₀₁^* η = η ∧ ω` for sections of
the ideal of the diagonal of `T'`, read in the top summand of `𝒪_{T''}`. -/
theorem secondOrderThickeningQ₁₂_inr_mul_Q₀₁_inr
    (ω η : ↑((dpDifferentialsModules T Y f).obj W)) :
    ((secondOrderThickeningQ₁₂ T Y f).app W).hom (firstOrderThickeningInr T Y f W ω) *
        ((secondOrderThickeningQ₀₁ T Y f).app W).hom (firstOrderThickeningInr T Y f W η) =
      secondOrderExtMk (q := dpWedge T Y f) 0 0 0 ((dpWedge T Y f).app W η ω) := by
  rw [secondOrderThickeningQ₁₂_inr, secondOrderThickeningQ₀₁_inr]
  exact secondOrderExt_inr_mul_inl η ω (dpDeRham T Y f W ω)

end Formulas

/-! ### The exterior product as a morphism of sheaves -/

section Wedge

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- The exterior product `Crystalline.dpWedge`, as a bilinear map of sheaves of modules. -/
def dpWedgeBilinear : SheafOfModules.BilinearMap (R := Stacks.RingedSpace.structureRingSheaf
      T.scheme.toRingedSpace) (dpDifferentialsSheaf T Y f) (dpDifferentialsSheaf T Y f)
      (dpSecondExteriorPower T Y f) :=
  dpWedge T Y f

/-- The exterior product `Ω_{T/Y,δ} ⊗ Ω_{T/Y,δ} ⟶ Ω²_{T/Y,δ}`, out of the tensor product
sheaf at the `Stacks.RingedSpace.tensorSheaf` spelling. -/
def dpWedgeSheafHom' :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨T.scheme.toRingedSpace.presheaf, T.scheme.toRingedSpace.IsSheaf⟩)).obj
        (dpDifferentialsSheaf T Y f, dpDifferentialsSheaf T Y f) ⟶ dpSecondExteriorPower T Y f :=
  Stacks.RingedSpace.ofBilinearSheaf (dpWedgeBilinear T Y f)

/-- **The exterior product `Ω_{T/Y,δ} ⊗_{𝒪_T} Ω_{T/Y,δ} ⟶ Ω²_{T/Y,δ}`**, the bilinear map
`Crystalline.dpWedge` descended to the tensor product sheaf. -/
def dpWedgeSheafHom :
    dpDifferentialsSheaf T Y f ⊗ dpDifferentialsSheaf T Y f ⟶ dpSecondExteriorPower T Y f :=
  dpWedgeSheafHom' T Y f

/-- The exterior product on a local pure tensor: `ω ⊗ η ↦ ω ∧ η`. -/
theorem dpWedgeSheafHom_tmul (W : (Opens ↑T.scheme)ᵒᵖ)
    (ω η : (dpDifferentialsSheaf T Y f).val.obj W) :
    (dpWedgeSheafHom T Y f).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace (dpDifferentialsSheaf T Y f)
          (dpDifferentialsSheaf T Y f) W ω η) =
      (dpWedge T Y f).app W ω η :=
  Stacks.RingedSpace.ofBilinearSheaf_unit_tmul (dpWedge T Y f) W ω η

variable (N : T.scheme.Modules)

/-- **The exterior multiplication `(N ⊗ Ω) ⊗ Ω ⟶ N ⊗ Ω²`**, `(x ⊗ ω) ⊗ η ↦ x ⊗ (ω ∧ η)`: the
associator followed by `N` tensored with the exterior product.  This is the operation
`z ↦ z ∧ ω` of [Stacks, Remark 07I0] on `N ⊗ Ω`. -/
def tensorWedgeHom :
    (N ⊗ dpDifferentialsSheaf T Y f) ⊗ dpDifferentialsSheaf T Y f ⟶
      N ⊗ dpSecondExteriorPower T Y f :=
  (α_ N (dpDifferentialsSheaf T Y f) (dpDifferentialsSheaf T Y f)).hom ≫
    (N ◁ dpWedgeSheafHom T Y f)

/-- The exterior multiplication on a local triple pure tensor. -/
theorem tensorWedgeHom_tmul (W : (Opens ↑T.scheme)ᵒᵖ) (x : N.val.obj W)
    (ω η : (dpDifferentialsSheaf T Y f).val.obj W) :
    (tensorWedgeHom T Y f N).val.app W
        (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace
          (N ⊗ dpDifferentialsSheaf T Y f : T.scheme.Modules) (dpDifferentialsSheaf T Y f) W
          (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
            (dpDifferentialsSheaf T Y f) W x ω) η) =
      Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
        (dpSecondExteriorPower T Y f) W x ((dpWedge T Y f).app W ω η) := by
  have h1 := Stacks.PullbackTensorCoherence.associator_hom_tmul (Z := T.scheme.toRingedSpace)
    (A := N) (B := dpDifferentialsSheaf T Y f) (D := dpDifferentialsSheaf T Y f) W x ω η
  have hmap := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (R := (⟨T.scheme.toRingedSpace.presheaf, T.scheme.toRingedSpace.IsSheaf⟩ :
      Sheaf (Opens.grothendieckTopology T.scheme.toRingedSpace.carrier) CommRingCat.{u}))
    (𝟙 N) (dpWedgeSheafHom T Y f)
  have h2 := Stacks.RingedSpace.tensorSheaf_map_unit_tmul T.scheme.toRingedSpace (𝟙 N)
    (dpWedgeSheafHom T Y f) W x
    (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace (dpDifferentialsSheaf T Y f)
      (dpDifferentialsSheaf T Y f) W ω η)
  refine (Stacks.SheafOfModules.comp_val_app_apply _ _ W _).trans ?_
  refine (congrArg _ h1).trans ?_
  refine (congrArg (fun φ ↦ φ.val.app W
    (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
      (dpDifferentialsSheaf T Y f ⊗ dpDifferentialsSheaf T Y f : T.scheme.Modules) W x
      (Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace (dpDifferentialsSheaf T Y f)
        (dpDifferentialsSheaf T Y f) W ω η))) hmap.symm).trans ?_
  exact h2.trans (congrArg (fun w ↦ Stacks.PullbackTensorCoherence.tmul T.scheme.toRingedSpace N
    (dpSecondExteriorPower T Y f) W x w) (dpWedgeSheafHom_tmul T Y f W ω η))

end Wedge

namespace GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (M : SheafOfModules.{u} (structureSheaf S))
  (A : CrystallineThickening S)

section SecondOrder

/-- `q₀^* x`, a section of `F_{T''}`. -/
abbrev secondOrderQ₀Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) : SecondOrderSec M A W :=
  crystalRestrict M (secondOrderCrysRestrictQ₀ A W) x

/-- `q₁^* x`, a section of `F_{T''}`. -/
abbrev secondOrderQ₁Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) : SecondOrderSec M A W :=
  crystalRestrict M (secondOrderCrysRestrictQ₁ A W) x

/-- `q₂^* x`, a section of `F_{T''}`. -/
abbrev secondOrderQ₂Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) : SecondOrderSec M A W :=
  crystalRestrict M (secondOrderCrysRestrictQ₂ A W) x

/-- `q₀₁^* y` for a section `y` of `F_{T'}`. -/
abbrev secondOrderQ₀₁Sec (W : A.obj.thickening.target.scheme.Opens)
    (y : FirstOrderSec M A W) : SecondOrderSec M A W :=
  crystalRestrict M (secondOrderCrysRestrictQ₀₁ A W) y

/-- `q₁₂^* y` for a section `y` of `F_{T'}`. -/
abbrev secondOrderQ₁₂Sec (W : A.obj.thickening.target.scheme.Opens)
    (y : FirstOrderSec M A W) : SecondOrderSec M A W :=
  crystalRestrict M (secondOrderCrysRestrictQ₁₂ A W) y

/-- `q₀₂^* y` for a section `y` of `F_{T'}`. -/
abbrev secondOrderQ₀₂Sec (W : A.obj.thickening.target.scheme.Opens)
    (y : FirstOrderSec M A W) : SecondOrderSec M A W :=
  crystalRestrict M (secondOrderCrysRestrictQ₀₂ A W) y

variable {M}

/-- `q₀₁ : 𝒪_{T'} ⟶ 𝒪_{T''}` on sections over an open of `T`. -/
abbrev secondOrderQ₀₁Scalar (W : A.obj.thickening.target.scheme.Opens) (r : FirstOrderRing A W) :
    SecondOrderRing A W :=
  ((secondOrderThickeningQ₀₁ A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app
    (op W)).hom r

/-- `q₁₂ : 𝒪_{T'} ⟶ 𝒪_{T''}` on sections over an open of `T`. -/
abbrev secondOrderQ₁₂Scalar (W : A.obj.thickening.target.scheme.Opens) (r : FirstOrderRing A W) :
    SecondOrderRing A W :=
  ((secondOrderThickeningQ₁₂ A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app
    (op W)).hom r

/-- `q₀₂ : 𝒪_{T'} ⟶ 𝒪_{T''}` on sections over an open of `T`. -/
abbrev secondOrderQ₀₂Scalar (W : A.obj.thickening.target.scheme.Opens) (r : FirstOrderRing A W) :
    SecondOrderRing A W :=
  ((secondOrderThickeningQ₀₂ A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app
    (op W)).hom r

variable (M)

/-- `q₀₁^*` is semilinear over `q₀₁ : 𝒪_{T'} ⟶ 𝒪_{T''}`. -/
theorem secondOrderQ₀₁Sec_smul (W : A.obj.thickening.target.scheme.Opens)
    (r : FirstOrderRing A W) (y : FirstOrderSec M A W) :
    secondOrderQ₀₁Sec M A W (r • y) = secondOrderQ₀₁Scalar A W r • secondOrderQ₀₁Sec M A W y :=
  ((crysAmbientFMap M (secondOrderThickeningCrysQ₀₁ S A)).val.app
    (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W))).hom.map_smul r y

/-- `q₁₂^*` is semilinear over `q₁₂ : 𝒪_{T'} ⟶ 𝒪_{T''}`. -/
theorem secondOrderQ₁₂Sec_smul (W : A.obj.thickening.target.scheme.Opens)
    (r : FirstOrderRing A W) (y : FirstOrderSec M A W) :
    secondOrderQ₁₂Sec M A W (r • y) = secondOrderQ₁₂Scalar A W r • secondOrderQ₁₂Sec M A W y :=
  ((crysAmbientFMap M (secondOrderThickeningCrysQ₁₂ S A)).val.app
    (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W))).hom.map_smul r y

/-- `q₀₂^*` is semilinear over `q₀₂ : 𝒪_{T'} ⟶ 𝒪_{T''}`. -/
theorem secondOrderQ₀₂Sec_smul (W : A.obj.thickening.target.scheme.Opens)
    (r : FirstOrderRing A W) (y : FirstOrderSec M A W) :
    secondOrderQ₀₂Sec M A W (r • y) = secondOrderQ₀₂Scalar A W r • secondOrderQ₀₂Sec M A W y :=
  ((crysAmbientFMap M (secondOrderThickeningCrysQ₀₂ S A)).val.app
    (op ((firstOrderThickeningCrysP₀ S A).hom.targetHom.hom ⁻¹ᵁ W))).hom.map_smul r y

/-- Restricting twice along morphisms with composite `k` is restricting along `k`. -/
private theorem crystalRestrict_crystalRestrict_of_comp_eq {B C D : CrystallineThickening S}
    {g : B ⟶ C} {h : C ⟶ D} {k : B ⟶ D} (e : g ≫ h = k) (x : M.val.obj (op D)) :
    crystalRestrict M g (crystalRestrict M h x) = crystalRestrict M k x :=
  (crystalRestrict_comp M g h x).trans (congrArg (fun g ↦ crystalRestrict M g x) e)

/-- `q₀₁^* p₀^* = q₀^*`, from `p₀ ∘ q₀₁ = q₀`. -/
theorem secondOrderQ₀₁Sec_P₀Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) :
    secondOrderQ₀₁Sec M A W (firstOrderP₀Sec M A W x) = secondOrderQ₀Sec M A W x :=
  crystalRestrict_crystalRestrict_of_comp_eq M (secondOrderCrysRestrictQ₀₁_comp_P₀ A W) x

/-- `q₀₁^* p₁^* = q₁^*`, from `p₁ ∘ q₀₁ = q₁`. -/
theorem secondOrderQ₀₁Sec_P₁Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) :
    secondOrderQ₀₁Sec M A W (firstOrderP₁Sec M A W x) = secondOrderQ₁Sec M A W x :=
  crystalRestrict_crystalRestrict_of_comp_eq M (secondOrderCrysRestrictQ₀₁_comp_P₁ A W) x

/-- `q₁₂^* p₀^* = q₁^*`, from `p₀ ∘ q₁₂ = q₁`. -/
theorem secondOrderQ₁₂Sec_P₀Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) :
    secondOrderQ₁₂Sec M A W (firstOrderP₀Sec M A W x) = secondOrderQ₁Sec M A W x :=
  crystalRestrict_crystalRestrict_of_comp_eq M (secondOrderCrysRestrictQ₁₂_comp_P₀ A W) x

/-- `q₁₂^* p₁^* = q₂^*`, from `p₁ ∘ q₁₂ = q₂`. -/
theorem secondOrderQ₁₂Sec_P₁Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) :
    secondOrderQ₁₂Sec M A W (firstOrderP₁Sec M A W x) = secondOrderQ₂Sec M A W x :=
  crystalRestrict_crystalRestrict_of_comp_eq M (secondOrderCrysRestrictQ₁₂_comp_P₁ A W) x

/-- `q₀₂^* p₀^* = q₀^*`, from `p₀ ∘ q₀₂ = q₀`. -/
theorem secondOrderQ₀₂Sec_P₀Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) :
    secondOrderQ₀₂Sec M A W (firstOrderP₀Sec M A W x) = secondOrderQ₀Sec M A W x :=
  crystalRestrict_crystalRestrict_of_comp_eq M (secondOrderCrysRestrictQ₀₂_comp_P₀ A W) x

/-- `q₀₂^* p₁^* = q₂^*`, from `p₁ ∘ q₀₂ = q₂`. -/
theorem secondOrderQ₀₂Sec_P₁Sec (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W)) :
    secondOrderQ₀₂Sec M A W (firstOrderP₁Sec M A W x) = secondOrderQ₂Sec M A W x :=
  crystalRestrict_crystalRestrict_of_comp_eq M (secondOrderCrysRestrictQ₀₂_comp_P₁ A W) x

/-- `q₀₁^*` is additive. -/
theorem secondOrderQ₀₁Sec_add (W : A.obj.thickening.target.scheme.Opens)
    (y y' : FirstOrderSec M A W) :
    secondOrderQ₀₁Sec M A W (y + y') = secondOrderQ₀₁Sec M A W y + secondOrderQ₀₁Sec M A W y' :=
  map_add (crystalRestrict M (secondOrderCrysRestrictQ₀₁ A W)) y y'

/-- `q₀₁^*` commutes with subtraction. -/
theorem secondOrderQ₀₁Sec_sub (W : A.obj.thickening.target.scheme.Opens)
    (y y' : FirstOrderSec M A W) :
    secondOrderQ₀₁Sec M A W (y - y') = secondOrderQ₀₁Sec M A W y - secondOrderQ₀₁Sec M A W y' :=
  map_sub (crystalRestrict M (secondOrderCrysRestrictQ₀₁ A W)) y y'

/-- `q₁₂^*` is additive. -/
theorem secondOrderQ₁₂Sec_add (W : A.obj.thickening.target.scheme.Opens)
    (y y' : FirstOrderSec M A W) :
    secondOrderQ₁₂Sec M A W (y + y') = secondOrderQ₁₂Sec M A W y + secondOrderQ₁₂Sec M A W y' :=
  map_add (crystalRestrict M (secondOrderCrysRestrictQ₁₂ A W)) y y'

/-- `q₁₂^*` commutes with subtraction. -/
theorem secondOrderQ₁₂Sec_sub (W : A.obj.thickening.target.scheme.Opens)
    (y y' : FirstOrderSec M A W) :
    secondOrderQ₁₂Sec M A W (y - y') = secondOrderQ₁₂Sec M A W y - secondOrderQ₁₂Sec M A W y' :=
  map_sub (crystalRestrict M (secondOrderCrysRestrictQ₁₂ A W)) y y'

/-- `q₀₂^*` is additive. -/
theorem secondOrderQ₀₂Sec_add (W : A.obj.thickening.target.scheme.Opens)
    (y y' : FirstOrderSec M A W) :
    secondOrderQ₀₂Sec M A W (y + y') = secondOrderQ₀₂Sec M A W y + secondOrderQ₀₂Sec M A W y' :=
  map_add (crystalRestrict M (secondOrderCrysRestrictQ₀₂ A W)) y y'

/-- `q₀₂^*` commutes with subtraction. -/
theorem secondOrderQ₀₂Sec_sub (W : A.obj.thickening.target.scheme.Opens)
    (y y' : FirstOrderSec M A W) :
    secondOrderQ₀₂Sec M A W (y - y') = secondOrderQ₀₂Sec M A W y - secondOrderQ₀₂Sec M A W y' :=
  map_sub (crystalRestrict M (secondOrderCrysRestrictQ₀₂ A W)) y y'

/-! #### Naturality in the open -/

/-- `q₀₁^*` commutes with restriction to a smaller open. -/
theorem secondOrderQ₀₁Sec_restrict {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (y : FirstOrderSec M A W) :
    (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map (homOfLE h).op
        (secondOrderQ₀₁Sec M A W y) =
      secondOrderQ₀₁Sec M A W'
        ((crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.map
          (homOfLE h).op y) :=
  (PresheafOfModules.naturality_apply (crysAmbientFMap M (secondOrderThickeningCrysQ₀₁ S A)).val
    (homOfLE h).op y).symm

/-- `q₁₂^*` commutes with restriction to a smaller open. -/
theorem secondOrderQ₁₂Sec_restrict {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (y : FirstOrderSec M A W) :
    (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map (homOfLE h).op
        (secondOrderQ₁₂Sec M A W y) =
      secondOrderQ₁₂Sec M A W'
        ((crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.map
          (homOfLE h).op y) :=
  (PresheafOfModules.naturality_apply (crysAmbientFMap M (secondOrderThickeningCrysQ₁₂ S A)).val
    (homOfLE h).op y).symm

/-- `q₀₂^*` commutes with restriction to a smaller open. -/
theorem secondOrderQ₀₂Sec_restrict {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (y : FirstOrderSec M A W) :
    (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map (homOfLE h).op
        (secondOrderQ₀₂Sec M A W y) =
      secondOrderQ₀₂Sec M A W'
        ((crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.map
          (homOfLE h).op y) :=
  (PresheafOfModules.naturality_apply (crysAmbientFMap M (secondOrderThickeningCrysQ₀₂ S A)).val
    (homOfLE h).op y).symm

/-- The canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` commutes with restriction. -/
theorem firstOrderTensorSec_restrict {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    (crysAmbientSchemeModules M (firstOrderThickeningCrysObject S A)).val.map (homOfLE h).op
        (firstOrderTensorSec M A W z) =
      firstOrderTensorSec M A W'
        ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z) :=
  (PresheafOfModules.naturality_apply (firstOrderTensorInclusion M A).val (homOfLE h).op z).symm

/-! #### The alternating sum of [Stacks, Tag 07J6] -/

/-- **The alternating sum `q₀₁^* z + q₁₂^* z - q₀₂^* z`**: for a section `z` of
`F_T ⊗_{𝒪_T} Ω_{T/S,δ}` over an open, read in `F_{T'}` by the canonical morphism, the
combination of its three restrictions to the second-order universal thickening of
[Stacks, Tag 07J3]. -/
def crystalCurvatureApp (W : A.obj.thickening.target.scheme.Opens) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) →+
      SecondOrderSec M A W :=
  AddMonoidHom.mk'
    (fun z ↦ secondOrderQ₀₁Sec M A W (firstOrderTensorSec M A W z) +
      secondOrderQ₁₂Sec M A W (firstOrderTensorSec M A W z) -
        secondOrderQ₀₂Sec M A W (firstOrderTensorSec M A W z))
    (fun z z' ↦ by
      rw [firstOrderTensorSec_add, secondOrderQ₀₁Sec_add, secondOrderQ₁₂Sec_add,
        secondOrderQ₀₂Sec_add]
      abel)

/-- Unfolding of `...SmallSite.crystalCurvatureApp`. -/
theorem crystalCurvatureApp_apply (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    crystalCurvatureApp M A W z =
      secondOrderQ₀₁Sec M A W (firstOrderTensorSec M A W z) +
        secondOrderQ₁₂Sec M A W (firstOrderTensorSec M A W z) -
          secondOrderQ₀₂Sec M A W (firstOrderTensorSec M A W z) := rfl

/-- **The alternating sum commutes with restriction to a smaller open.** -/
theorem crystalCurvatureApp_restrict {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map (homOfLE h).op
        (crystalCurvatureApp M A W z) =
      crystalCurvatureApp M A W'
        ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z) := by
  have hs := ((crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map
    (homOfLE h).op).hom.map_sub
      (secondOrderQ₀₁Sec M A W (firstOrderTensorSec M A W z) +
        secondOrderQ₁₂Sec M A W (firstOrderTensorSec M A W z))
      (secondOrderQ₀₂Sec M A W (firstOrderTensorSec M A W z))
  have ha := ((crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map
    (homOfLE h).op).hom.map_add
      (secondOrderQ₀₁Sec M A W (firstOrderTensorSec M A W z))
      (secondOrderQ₁₂Sec M A W (firstOrderTensorSec M A W z))
  refine hs.trans ?_
  refine (congrArg₂ (· - ·) (ha.trans (congrArg₂ (· + ·)
    (secondOrderQ₀₁Sec_restrict M A h _) (secondOrderQ₁₂Sec_restrict M A h _)))
    (secondOrderQ₀₂Sec_restrict M A h _)).trans ?_
  exact congrArg (fun y ↦ secondOrderQ₀₁Sec M A W' y + secondOrderQ₁₂Sec M A W' y -
    secondOrderQ₀₂Sec M A W' y) (firstOrderTensorSec_restrict M A h z)

/-- The degree-two canonical morphism `F_T ⊗ Ω² ⟶ q₀_* F_{T''}` on sections, valued in
`F_{T''}`. -/
abbrev secondOrderTensorSec (W : A.obj.thickening.target.scheme.Opens)
    (w : (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) : SecondOrderSec M A W :=
  (secondOrderTensorComparison M A).val.app (op W) w

/-- The degree-two canonical morphism is additive on sections. -/
theorem secondOrderTensorSec_add (W : A.obj.thickening.target.scheme.Opens)
    (w w' : (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    secondOrderTensorSec M A W (w + w') =
      secondOrderTensorSec M A W w + secondOrderTensorSec M A W w' :=
  ((secondOrderTensorComparison M A).val.app (op W)).hom.map_add w w'

/-- The top inclusion `η ↦ (0, 0, 0, η)` into `𝒪_{T''}` over an open of `T`. -/
abbrev secondOrderTopSec (W : A.obj.thickening.target.scheme.Opens)
    (η : (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) : SecondOrderRing A W :=
  secondOrderIdealScalar A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) η

/-- The local pure tensor `x ⊗ η` of `F_T ⊗_{𝒪_T} Ω²_{T/S,δ}`. -/
abbrev secondOrderTensorTmul (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (η : (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) :=
  Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
    (crysAmbientSchemeModules M A)
    (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom) (op W) x η

/-- **The degree-two canonical morphism on a local pure tensor**:
`x ⊗ η ↦ (0, 0, 0, η) · q₀^* x`. -/
theorem secondOrderTensorSec_tmul (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (η : (dpSecondExteriorPower A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    secondOrderTensorSec M A W (secondOrderTensorTmul M A W x η) =
      secondOrderTopSec A W η • secondOrderQ₀Sec M A W x :=
  secondOrderTensorComparison_tmul M A (op W) x η

/-! #### The degree-one extension of the connection -/

variable {M}

/-- **The degree-one extension `∇ : F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ F_T ⊗_{𝒪_T} Ω²_{T/S,δ}` of the
connection, of [Stacks, Section 60.15, Tag 07J5]**, on the sections over an open: the
alternating sum `...SmallSite.crystalCurvatureApp` read in `F_T ⊗ Ω²` through the retraction of
the degree-two canonical morphism. -/
def crystalConnectionExtensionApp (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) →+
      (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) :=
  (schemeModulesValAppHom (secondOrderTensorRetraction M A hM) (op W)).comp
    (crystalCurvatureApp M A W)

/-- Unfolding of `...SmallSite.crystalConnectionExtensionApp`. -/
private theorem crystalConnectionExtensionApp_apply (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    crystalConnectionExtensionApp A hM W z =
      (secondOrderTensorRetraction M A hM).val.app (op W) (crystalCurvatureApp M A W z) := rfl

/-- The degree-two retraction commutes with restriction to a smaller open. -/
private theorem secondOrderTensorRetraction_restrict (hM : IsSheafCrystal M)
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) {y : SecondOrderSec M A W}
    {y' : SecondOrderSec M A W'}
    (hy : (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map
      (homOfLE h).op y = y') :
    (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op
      ((secondOrderTensorRetraction M A hM).val.app (op W) y) =
    (secondOrderTensorRetraction M A hM).val.app (op W') y' :=
  (PresheafOfModules.naturality_apply (secondOrderTensorRetraction M A hM).val
    (homOfLE h).op y).symm.trans (congrArg _ hy)

/-- **The degree-one extension commutes with restriction to a smaller open.** -/
theorem crystalConnectionExtensionApp_naturality (hM : IsSheafCrystal M)
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op
        (crystalConnectionExtensionApp A hM W z) =
      crystalConnectionExtensionApp A hM W'
        ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z) := by
  exact secondOrderTensorRetraction_restrict A hM h (crystalCurvatureApp_restrict M A h z)

/-- **The extension is the alternating sum wherever the alternating sum lies in the image of the
degree-two canonical morphism.** -/
theorem crystalConnectionExtensionApp_eq_of_tensorSec (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W))
    (w : (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W))
    (h : secondOrderTensorSec M A W w = crystalCurvatureApp M A W z) :
    crystalConnectionExtensionApp A hM W z = w := by
  rw [crystalConnectionExtensionApp_apply, ← h]
  exact secondOrderTensorRetraction_comparison_apply M A hM (op W) w

/-- **The alternating sum vanishes on the values of the connection.** -/
theorem crystalCurvatureApp_crystalConnectionApp (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    crystalCurvatureApp M A W (crystalConnectionApp A hM W s) = 0 := by
  rw [crystalCurvatureApp_apply, firstOrderTensorSec_crystalConnectionApp, sub_eq_zero]
  exact crystalConnectionRaw_cocycle M A W s

/-- **Stacks Project, Tag 07J6: the canonical connection is integrable**, on the sections over
every open: the composite of the connection with its degree-one extension vanishes. -/
theorem crystalConnectionExtensionApp_crystalConnectionApp (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (s : (crysAmbientSchemeModules M A).val.obj (op W)) :
    crystalConnectionExtensionApp A hM W (crystalConnectionApp A hM W s) = 0 := by
  rw [crystalConnectionExtensionApp_apply, crystalCurvatureApp_crystalConnectionApp]
  exact map_zero _

variable (M)

/-! #### The exterior multiplication `F_T ⊗ Ω × Ω ⟶ F_T ⊗ Ω²` -/

/-- **`z ∧ ω`** for a section `z` of `F_T ⊗_{𝒪_T} Ω_{T/S,δ}` and a differential `ω` over the
same open: the operation of [Stacks, Remark 07I0] by which the degree-one extension of a
connection is defined, `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)`. -/
abbrev crystalWedge (W : A.obj.thickening.target.scheme.Opens)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) :=
  (tensorWedgeHom A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (crysAmbientSchemeModules M A)).val.app (op W)
    (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
      (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A))
      (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom) (op W) z ω)

/-- **`(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)`** on local pure tensors. -/
theorem crystalWedge_tmul (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (η ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    crystalWedge M A W (firstOrderTensorTmul M A W x η) ω =
      secondOrderTensorTmul M A W x
        ((dpWedge A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op W) η ω) :=
  tensorWedgeHom_tmul A.obj.thickening.target S.S.scheme A.obj.toBase.hom
    (crysAmbientSchemeModules M A) (op W) x η ω

/-- `z ↦ z ∧ ω` is additive. -/
theorem crystalWedge_add (W : A.obj.thickening.target.scheme.Opens)
    (z z' : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    crystalWedge M A W (z + z') ω = crystalWedge M A W z ω + crystalWedge M A W z' ω := by
  unfold crystalWedge
  rw [tmul_add_left]
  exact ((tensorWedgeHom A.obj.thickening.target S.S.scheme A.obj.toBase.hom
      (crysAmbientSchemeModules M A)).val.app (op W)).hom.map_add _ _

/-- `z ∧ ω` commutes with restriction to a smaller open. -/
theorem crystalWedge_restrict {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op
        (crystalWedge M A W z ω) =
      crystalWedge M A W'
        ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z)
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE h).op ω) :=
  (PresheafOfModules.naturality_apply (tensorWedgeHom A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom (crysAmbientSchemeModules M A)).val (homOfLE h).op _).symm.trans
    (congrArg _ (tmul_restrict h z ω))

/-! #### The second formula of [Stacks, Tag 07J3] against the connection -/

variable {M}

/-- `z ↦ q₁₂^*(0, ω) · q₀₁^* z`, read back in `F_T ⊗ Ω²` through the retraction of the degree-two
canonical morphism, as an additive map. -/
abbrev crystalQ₁₂Action (hM : IsSheafCrystal M) (V : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op V)) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V) →+
      (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V) :=
  (schemeModulesValAppHom (secondOrderTensorRetraction M A hM) (op V)).comp
    (AddMonoidHom.mk'
      (fun z ↦ secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V ω) •
        secondOrderQ₀₁Sec M A V (firstOrderTensorSec M A V z))
      (fun z z' ↦ by
        rw [firstOrderTensorSec_add, secondOrderQ₀₁Sec_add]
        exact smul_add _ _ _) :
      (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V) →+ SecondOrderSec M A V)

/-- `z ↦ z ∧ ω`, as an additive map. -/
abbrev crystalWedgeHom (V : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op V)) :
    (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V) →+
      (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V) :=
  AddMonoidHom.mk' (fun z ↦ crystalWedge M A V z ω) (fun z z' ↦ crystalWedge_add M A V z z' ω)

/-- Unfolding of `...SmallSite.crystalQ₁₂Action`. -/
theorem crystalQ₁₂Action_apply (hM : IsSheafCrystal M) (V : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op V))
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op V)) :
    crystalQ₁₂Action A hM V ω z = (secondOrderTensorRetraction M A hM).val.app (op V)
      (secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V ω) •
        secondOrderQ₀₁Sec M A V (firstOrderTensorSec M A V z)) := rfl

/-- The two sides of `...SmallSite.crystalQ₁₂Action_eq` on a local pure tensor. -/
theorem crystalQ₁₂Action_tmul (hM : IsSheafCrystal M) (V : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op V))
    (a : (crysAmbientSchemeModules M A).val.obj (op V))
    (b : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op V)) :
    crystalQ₁₂Action A hM V ω (firstOrderTensorTmul M A V a b) =
      crystalWedge M A V (firstOrderTensorTmul M A V a b) ω := by
  have r2 : secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V ω) *
      secondOrderQ₀₁Scalar A V (firstOrderIdealSec A V b) =
      secondOrderTopSec A V
        ((dpWedge A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op V) b ω) :=
    secondOrderThickeningQ₁₂_inr_mul_Q₀₁_inr A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (op V) ω b
  have r3 : secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V ω) •
        secondOrderQ₀₁Sec M A V (firstOrderTensorSec M A V (firstOrderTensorTmul M A V a b)) =
      secondOrderTensorSec M A V (secondOrderTensorTmul M A V a
        ((dpWedge A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op V) b ω)) := by
    rw [firstOrderTensorSec_tmul, secondOrderQ₀₁Sec_smul, secondOrderQ₀₁Sec_P₀Sec, ← mul_smul,
      r2]
    exact (secondOrderTensorSec_tmul M A V a _).symm
  rw [crystalQ₁₂Action_apply, r3, crystalWedge_tmul]
  exact secondOrderTensorRetraction_comparison_apply M A hM (op V) _

/-- **`q₁₂^*(0, ω) · q₀₁^* z = z ∧ ω`**, read in `F_T ⊗ Ω²`, for every section `z` of `F_T ⊗ Ω`:
the second formula of [Stacks, Tag 07J3], `q₁₂^* ω · q₀₁^* ω' = ω' ∧ ω`, read on `F`. -/
theorem crystalQ₁₂Action_eq (hM : IsSheafCrystal M) (W : A.obj.thickening.target.scheme.Opens)
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W))
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W)) :
    crystalQ₁₂Action A hM W ω z = crystalWedge M A W z ω := by
  have h4 : ∀ {V V' : A.obj.thickening.target.scheme.Opens} (hV : V ≤ W) (hV' : V' ≤ W)
      (h : V' ≤ V),
      (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE h).op
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω) =
        (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV').op ω := fun _ _ _ ↦ by
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  have key := tensor_sections_ext (M := crysAmbientSchemeModules M A)
    (N := dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom)
    (G := secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)) (W := W)
    (fun V hV ↦ crystalQ₁₂Action A hM V
      ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE hV).op ω))
    (fun V hV ↦ crystalWedgeHom A V
      ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE hV).op ω)) ?_ ?_ ?_ z
  · have hω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE (le_refl W)).op ω = ω :=
      PresheafOfModules.map_id_apply _ _ ω
    exact (congrArg (fun ω' ↦ crystalQ₁₂Action A hM W ω' z) hω.symm).trans
      (key.trans (congrArg (fun ω' ↦ crystalWedge M A W z ω') hω))
  · intro V V' hV hV' h y
    have h3 := PresheafOfModules.naturality_apply
      (firstOrderThickeningInrSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val
      (homOfLE h).op
      ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω)
    have h2 := congrArg (fun φ ↦ φ.hom (firstOrderIdealSec A V
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω)))
      ((secondOrderThickeningQ₁₂ A.obj.thickening.target S.S.scheme A.obj.toBase.hom).naturality
        (homOfLE h).op)
    have h1 := (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map_smul
      (homOfLE h).op (secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V
        ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE hV).op ω)))
      (secondOrderQ₀₁Sec M A V (firstOrderTensorSec M A V y))
    have e1 :
        (secondOrderThickeningCrysObject S A).obj.thickening.target.scheme.ringCatSheaf.obj.map
          (homOfLE h).op (secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V
            ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
              (homOfLE hV).op ω))) =
        secondOrderQ₁₂Scalar A V' (firstOrderIdealSec A V'
          ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
            (homOfLE hV').op ω)) := by
      refine h2.symm.trans ?_
      refine congrArg (fun r ↦ ((secondOrderThickeningQ₁₂ A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom).app (op V')).hom r) ?_
      exact h3.symm.trans (congrArg (fun w ↦ (firstOrderThickeningInrSheaf
        A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.app (op V') w) (h4 hV hV' h))
    have h5 : (crysAmbientSchemeModules M (secondOrderThickeningCrysObject S A)).val.map
          (homOfLE h).op (secondOrderQ₁₂Scalar A V (firstOrderIdealSec A V
            ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
              (homOfLE hV).op ω)) • secondOrderQ₀₁Sec M A V (firstOrderTensorSec M A V y)) =
        secondOrderQ₁₂Scalar A V' (firstOrderIdealSec A V'
          ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
            (homOfLE hV').op ω)) • secondOrderQ₀₁Sec M A V' (firstOrderTensorSec M A V'
              ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
                A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op y)) := by
      refine h1.trans ?_
      rw [e1]
      exact congrArg (fun w : SecondOrderSec M A V' ↦ secondOrderQ₁₂Scalar A V'
          (firstOrderIdealSec A V'
            ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
              (homOfLE hV').op ω)) • w)
        ((secondOrderQ₀₁Sec_restrict M A h _).trans
          (congrArg (secondOrderQ₀₁Sec M A V') (firstOrderTensorSec_restrict M A h y)))
    exact secondOrderTensorRetraction_restrict A hM h h5
  · intro V V' hV hV' h y
    exact (crystalWedge_restrict M A h y _).trans (congrArg (crystalWedge M A V' _) (h4 hV hV' h))
  · intro V hV a b
    exact crystalQ₁₂Action_tmul A hM V _ a b

/-! #### The rule of [Stacks, Remark 07I0] -/

/-- **The alternating sum on a local pure tensor**: for `x ⊗ ω`,
`q₀₁^*(x ⊗ ω) + q₁₂^*(x ⊗ ω) - q₀₂^*(x ⊗ ω) = (0, 0, 0, d ω) · q₀^* x + q₁₂^*(0, ω) · q₀₁^* ∇(x)`.
-/
theorem crystalCurvatureApp_tmul (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    crystalCurvatureApp M A W (firstOrderTensorTmul M A W x ω) =
      secondOrderTopSec A W
          (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) ω) •
          secondOrderQ₀Sec M A W x +
        secondOrderQ₁₂Scalar A W (firstOrderIdealSec A W ω) •
          secondOrderQ₀₁Sec M A W (firstOrderTensorSec M A W (crystalConnectionApp A hM W x)) := by
  have hQ₁ : secondOrderQ₁Sec M A W x = secondOrderQ₀Sec M A W x +
      secondOrderQ₀₁Sec M A W (firstOrderTensorSec M A W (crystalConnectionApp A hM W x)) := by
    rw [firstOrderTensorSec_crystalConnectionApp, secondOrderQ₀₁Sec_sub, secondOrderQ₀₁Sec_P₁Sec,
      secondOrderQ₀₁Sec_P₀Sec]
    abel
  have hring := secondOrderThickening_alternatingSum_inr A.obj.thickening.target S.S.scheme
    A.obj.toBase.hom (op W) ω
  rw [crystalCurvatureApp_apply, firstOrderTensorSec_tmul, secondOrderQ₀₁Sec_smul,
    secondOrderQ₁₂Sec_smul, secondOrderQ₀₂Sec_smul, secondOrderQ₀₁Sec_P₀Sec,
    secondOrderQ₁₂Sec_P₀Sec, secondOrderQ₀₂Sec_P₀Sec, hQ₁]
  have htop : secondOrderTopSec A W
      (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) ω) =
      secondOrderQ₀₁Scalar A W (firstOrderIdealSec A W ω) +
        secondOrderQ₁₂Scalar A W (firstOrderIdealSec A W ω) -
          secondOrderQ₀₂Scalar A W (firstOrderIdealSec A W ω) := hring.symm
  rw [htop, sub_smul, add_smul, smul_add]
  abel

/-- **Stacks Project, Remark 07I0 / Section 07J5: the degree-one extension of the connection is
given by the rule `∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω`**, on local pure tensors over every open of the
ambient scheme. -/
theorem crystalConnectionExtensionApp_tmul (hM : IsSheafCrystal M)
    (W : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules M A).val.obj (op W))
    (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
      (op W)) :
    crystalConnectionExtensionApp A hM W (firstOrderTensorTmul M A W x ω) =
      crystalWedge M A W (crystalConnectionApp A hM W x) ω +
        secondOrderTensorTmul M A W x
          (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) ω) := by
  rw [crystalConnectionExtensionApp_apply, crystalCurvatureApp_tmul A hM W x ω]
  refine (((secondOrderTensorRetraction M A hM).val.app (op W)).hom.map_add _ _).trans ?_
  rw [add_comm]
  refine congrArg₂ (· + ·) ((crystalQ₁₂Action_apply A hM W ω _).symm.trans
    (crystalQ₁₂Action_eq A hM W ω _)) ?_
  exact (congrArg (fun y ↦ (secondOrderTensorRetraction M A hM).val.app (op W) y)
    (secondOrderTensorSec_tmul M A W x _).symm).trans
      (secondOrderTensorRetraction_comparison_apply M A hM (op W) _)

/-- **The degree-one extension is the only compatible family of additive maps given by the rule
of [Stacks, Remark 07I0]**: any family of additive maps `F_T ⊗ Ω ⟶ F_T ⊗ Ω²` over the opens of
`T` which commutes with restriction and satisfies `∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω` on local pure
tensors is `...SmallSite.crystalConnectionExtensionApp`. -/
theorem eq_crystalConnectionExtensionApp (hM : IsSheafCrystal M)
    (E : ∀ W : A.obj.thickening.target.scheme.Opens,
      (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W) →+
      (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj (op W))
    (hE : ∀ {W W' : A.obj.thickening.target.scheme.Opens} (h : W' ≤ W) z,
      (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op (E W z) =
        E W' ((firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.map (homOfLE h).op z))
    (hrule : ∀ (W : A.obj.thickening.target.scheme.Opens) x ω,
      E W (firstOrderTensorTmul M A W x ω) =
        crystalWedge M A W (crystalConnectionApp A hM W x) ω +
          secondOrderTensorTmul M A W x
            (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) ω))
    (W : A.obj.thickening.target.scheme.Opens) :
    E W = crystalConnectionExtensionApp A hM W := by
  ext z
  exact tensor_sections_ext (M := crysAmbientSchemeModules M A)
    (N := dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom)
    (G := secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
        A.obj.toBase.hom (crysAmbientSchemeModules M A)) (W := W)
    (fun V _ ↦ E V) (fun V _ ↦ crystalConnectionExtensionApp A hM V)
    (fun V V' _ _ h y ↦ hE h y)
    (fun V V' _ _ h y ↦ crystalConnectionExtensionApp_naturality A hM h y)
    (fun V _ a b ↦ (hrule V a b).trans (crystalConnectionExtensionApp_tmul A hM V a b).symm) z

/-! #### The degree-one extension as a morphism of sheaves -/

/-- **The degree-one extension `∇ : F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ F_T ⊗_{𝒪_T} Ω²_{T/S,δ}` of the
canonical connection**, of [Stacks, Section 60.15, Tag 07J5], as a morphism of sheaves of abelian
groups on the ambient scheme `T`; its value on sections over an open is
`...SmallSite.crystalConnectionExtensionApp`, given by the rule `∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω`
(`...SmallSite.crystalConnectionExtensionApp_tmul`). -/
def crystalConnectionExtension (hM : IsSheafCrystal M) :
    (SheafOfModules.toSheaf _).obj
        (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)) ⟶
      (SheafOfModules.toSheaf _).obj
        (secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom (crysAmbientSchemeModules M A)) :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom (crystalConnectionExtensionApp A hM W.unop)
      naturality := fun W W' i ↦ by
        ext z
        exact (crystalConnectionExtensionApp_naturality A hM (leOfHom i.unop) z).symm }

/-- The degree-one extension on the sections over an open. -/
@[simp]
theorem crystalConnectionExtension_app (hM : IsSheafCrystal M)
    (W : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (z : (firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom (crysAmbientSchemeModules M A)).val.obj W) :
    (crystalConnectionExtension A hM).hom.app W z = crystalConnectionExtensionApp A hM W.unop z :=
  rfl

/-- **The canonical connection composed with its degree-one extension vanishes**, as a morphism
of sheaves of abelian groups on `T`. -/
theorem crystalConnection_comp_crystalConnectionExtension (hM : IsSheafCrystal M) :
    crystalConnection A hM ≫ crystalConnectionExtension A hM = 0 := by
  ext W s
  exact crystalConnectionExtensionApp_crystalConnectionApp A hM W.unop s

end SecondOrder

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
