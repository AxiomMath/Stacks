module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleLocal

/-!
# The `ℓ`-th power map `μ_{N'} ⟶ μ_N`, `N' = ℓN`

The `ℓ`-th power of an `ℓN`-th root of unity is an `N`-th root of unity. This gives a morphism
`μ_{ℓN} ⟶ μ_N` of abelian sheaves on the small étale site
(`Stacks.Kummer.rootsOfUnityPowMap`). It is `ℤ/ℓN`-linear when `μ_N` is read as a
`ℤ/ℓN`-module through `ℤ/ℓN → ℤ/N`; that linear map is `Stacks.Kummer.rootsOfUnityModulePowMap`,
built on this one. These are the transition maps of the Tate module `ℤ_ℓ(1) = lim μ_{ℓⁿ}`. On a
root of unity `ζ` the map is `ζ ↦ ζ^ℓ` (`Stacks.Kummer.rootsOfUnityPowMap_sliceRootSection`).

## Main definitions

* `Stacks.Kummer.rootsOfUnityPowMap`: `μ_{ℓN} ⟶ μ_N`, `ζ ↦ ζ^ℓ`.

## Main results

* `Stacks.Kummer.rootsOfUnityPowMap_sliceRootSection`: on a slice carrying a primitive `ℓN`-th
  root of unity `ζ`, the map takes `ζ^m` to `(ζ^ℓ)^m`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable (X : Scheme.{u}) (ℓ N N' : ℕ) (hN : ℓ * N = N')

/-- **The `ℓ`-th power map `μ_{N'} ⟶ μ_N`**, for `N' = ℓN`. -/
def rootsOfUnityPowMap : rootsOfUnitySheaf.{u, v} X N' ⟶ rootsOfUnitySheaf.{u, v} X N :=
  kernel.lift (powMap.{u, v} X N) (rootsOfUnityι.{u, v} X N' ≫ powMap.{u, v} X ℓ) (by
    subst hN
    rw [Category.assoc, powMap, powMap, Preadditive.nsmul_comp, Category.id_comp, smul_smul]
    exact rootsOfUnityι_comp_powMap X (ℓ * N))

/-- The `ℓ`-th power map followed by the inclusion of `μ_N` into `𝐆_m` is the inclusion of
`μ_{N'}` followed by the `ℓ`-th power map of `𝐆_m`. -/
theorem rootsOfUnityPowMap_comp_ι :
    rootsOfUnityPowMap.{u, v} X ℓ N N' hN ≫ rootsOfUnityι.{u, v} X N =
      rootsOfUnityι.{u, v} X N' ≫ powMap.{u, v} X ℓ :=
  kernel.lift_ι _ _ _

/-- The `ℓ`-th power map on sections, through the inclusion into `𝐆_m`. -/
theorem rootsOfUnityι_rootsOfUnityPowMap_apply (U : (X.Etale)ᵒᵖ)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X N').obj.obj U)) :
    (rootsOfUnityι.{u, v} X N).hom.app U ((rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app U s) =
      (powMap.{u, v} X ℓ).hom.app U ((rootsOfUnityι.{u, v} X N').hom.app U s) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg InducedCategory.Hom.hom (rootsOfUnityPowMap_comp_ι.{u, v} X ℓ N N' hN)) U) s

variable {X} in
/-- **The `ℓ`-th power map takes `ζ^m` to `(ζ^ℓ)^m`** on an object of a slice carrying a
primitive `ℓN`-th root of unity `ζ`. -/
theorem rootsOfUnityPowMap_sliceRootSection [NeZero N] [NeZero N'] (V : X.Etale)
    {k : Type u} [Field k] (κ : k →+* Γ(V.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N')
    (hζ' : IsPrimitiveRoot (ζ ^ ℓ) N) (W : Over V) (m : ℕ) :
    (rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app (op W.left)
        (sliceRootSection.{u, v} V κ hζ W (m : ZMod N')) =
      sliceRootSection.{u, v} V κ hζ' W (m : ZMod N) := by
  apply rootsOfUnityι_app_injective.{u, v} N W.left
  rw [rootsOfUnityι_rootsOfUnityPowMap_apply, rootsOfUnityι_sliceRootSection, powMap_app_ofUnit,
    rootsOfUnityι_sliceRootSection]
  congr 1
  have hr : sliceRootOn V κ hζ' W = sliceRootOn V κ hζ W ^ ℓ := by
    apply Units.ext
    simp [sliceRootOn, map_pow]
  rw [ZMod.val_natCast, ZMod.val_natCast, ← pow_eq_pow_mod_of_pow_eq_one (sliceRootOn_pow V κ hζ W),
    ← pow_eq_pow_mod_of_pow_eq_one (sliceRootOn_pow V κ hζ' W), hr, ← pow_mul, ← pow_mul,
    Nat.mul_comm m ℓ]

end Stacks.Kummer

end
