module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension of scalars to a localization is localization of modules

Let `R` be a commutative ring and let `T` be a submonoid of `R`. Extension of scalars along
`R → Localization T` is the base change `M ↦ Localization T ⊗[R] M`, and base change along a
localization of rings is localization of modules. The two functors
`ModuleCat R ⥤ ModuleCat (Localization T)` therefore agree, naturally in the module.

## Main definitions

* `extendScalars_iso_localizedModuleFunctor` — extension of scalars along `R → Localization T`
  is the localized-module functor at `T`.

## Implementation notes

The comparison at a module `M` is the base-change identification
`Localization T ⊗[R] M ≅ M_T` provided by `IsLocalizedModule.isBaseChange`, which applies because
the localization map `M → M_T` exhibits `M_T` as a base change. Extension of scalars forms its
tensor product over the restriction of `Localization T` to an `R`-module rather than over the
ambient algebra; the two carriers are identified by the identity map, which is done inside the
proof here and stated in general as `StacksDraft.PseudoCoherence.extendScalarsTensorIso`.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory TensorProduct
open scoped ChangeOfRings

/-- **Extension of scalars to a localization is localization of modules.** Base change along
`R → Localization T` agrees with the localized-module functor at the submonoid `T`, naturally in
the module. -/
@[ega "0 1.5.4" "partial"]
def extendScalars_iso_localizedModuleFunctor {R : Type u} [CommRing R] (T : Submonoid R) :
    ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization T)) ≅
      ModuleCat.localizedModuleFunctor.{max v u} T := by
  let S := Localization T
  -- Extension of scalars tensors with `S` restricted to an `R`-module; the identity identifies
  -- that factor with `S` itself, hence the carrier with the ambient base change `S ⊗[R] M`.
  let X := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  have hst : IsScalarTower R S X := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let e : X ≃ₗ[S] S := LinearEquiv.refl S S
  let b : ∀ M : ModuleCat.{max v u} R,
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).obj M ≅
        ModuleCat.of S (S ⊗[R] M) := fun M =>
    (AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso
  let E : ∀ M : ModuleCat.{max v u} R, (S ⊗[R] M) ≃ₗ[S] M.localizedModule T := fun M =>
    (IsLocalizedModule.isBaseChange T S (M.localizedModuleMkLinearMap T)).equiv
  refine NatIso.ofComponents (fun M => b M ≪≫ (E M).toModuleIso)
    fun {M N} f => ModuleCat.ExtendScalars.hom_ext fun m => ?_
  -- Both sides send `1 ⊗ₜ m` to the image of `m` in `N_T`. Stating that in the spellings of
  -- the localized modules keeps the base-change carrier out of the rewrites.
  change E N ((1 : S) ⊗ₜ[R] (f.hom m)) =
    ((ModuleCat.localizedModuleFunctor.{max v u} T).map f).hom (E M ((1 : S) ⊗ₜ[R] m))
  simp only [E, IsBaseChange.equiv_tmul, one_smul]
  exact (IsLocalizedModule.map_apply T (M.localizedModuleMkLinearMap T)
    (N.localizedModuleMkLinearMap T) f.hom m).symm

/-- The comparison of extension of scalars with localization of modules carries the pure tensor
`s ⊗ₜ m` to `s • (m / 1)`. -/
theorem extendScalars_iso_localizedModuleFunctor_hom_app_tmul {R : Type u} [CommRing R]
    (T : Submonoid R) (M : ModuleCat.{max v u} R) (s : Localization T) (m : M) :
    ((extendScalars_iso_localizedModuleFunctor.{u, v} T).hom.app M).hom
        (s ⊗ₜ[R, algebraMap R (Localization T)] m) = s • M.localizedModuleMkLinearMap T m :=
  (IsLocalizedModule.isBaseChange T (Localization T)
    (M.localizedModuleMkLinearMap T)).equiv_tmul s m

end
