module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineEvalDualSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ModuleReflexivePower
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerSystem

/-!
# The reflexive powers of an associated sheaf

Let `R` be a Noetherian ring and `M` a finite `R`-module. The reflexive powers of `M^~` on
`Spec R` [Stacks, Tag 0EBN] are the associated sheaves of the reflexive powers of `M`:

`(M^~)^{[n]} ≅ (M^{[n]})^~`.

## Main definitions

* `AlgebraicGeometry.tildeGlobalSection`: the global section of `M^~` attached to an element
  of `M`.
* `AlgebraicGeometry.reflexivePowerTildeIso`: the comparison `(M^~)^{[n]} ≅ (M^{[n]})^~`.

## Main results

* `AlgebraicGeometry.tilde_unit_hom_ext`: a morphism out of `R^~` is determined by its value on
  the global section `1`.
* `AlgebraicGeometry.reflexivePowerTildeIso_transition_zero`: the comparison is compatible with
  the transition out of degree `0`, which is multiplication by `s`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBQ](https://stacks.math.columbia.edu/tag/0EBQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexivePowers

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-! ### Global sections of an associated sheaf -/

/-- The global section of `M^~` attached to `m : M`: over an open `U` it is the canonical image
of `m` in `Γ(M^~, U)`. -/
def tildeGlobalSection (M : ModuleCat.{u} R) (m : M) : (tilde M).sections :=
  PresheafOfModules.sectionsMk (fun U => StructureSheaf.toOpenₗ R M U.unop m) fun _ _ _ => rfl

/-- The morphism `𝒪_{Spec R} ⟶ M^~` attached to `tildeGlobalSection M m` carries the unit
section to `m`. -/
theorem tildeGlobalSection_unitHom_app_one (M : ModuleCat.{u} R) (m : M) :
    (((tilde M).unitHomEquiv.symm (tildeGlobalSection M m)).val.app
        (op (⊤ : (Spec R).Opens))).hom (1 : Γ(Spec R, (⊤ : (Spec R).Opens))) =
      (tilde.toOpen M ⊤).hom m := by
  have h := SheafOfModules.unitHomEquiv_apply_coe (tilde M)
    ((tilde M).unitHomEquiv.symm (tildeGlobalSection M m)) (op (⊤ : (Spec R).Opens))
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The associated sheaf of `R` carries `1` to the unit section. -/
theorem toOpen_one : (tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R) =
    (1 : Γ(Spec R, (⊤ : (Spec R).Opens))) :=
  StructureSheaf.const_self 1 ⊤ (by simp)

/-- A morphism out of `R^~` is determined by its value on the global section `1`. -/
theorem tilde_unit_hom_ext {F : SheafOfModules (structureSheaf (Spec R).sheaf)}
    {φ ψ : tilde (ModuleCat.of R R) ⟶ F}
    (h : φ.val.app (op ⊤) ((tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R)) =
      ψ.val.app (op ⊤) ((tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R))) :
    φ = ψ :=
  ((tilde.adjunction (R := R)).homEquiv (ModuleCat.of R R) F).injective <|
    ModuleCat.hom_ext <| LinearMap.ext_ring h

/-! ### The comparison of the reflexive powers -/

variable (R) [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M]

/-- **The reflexive powers of an associated sheaf.** The isomorphism `(M^~)^{[n]} ≅ (M^{[n]})^~`,
the identity in degrees `0` and `1` and `AlgebraicGeometry.doubleDualTensorTildeIso` in each
higher degree. -/
def reflexivePowerTildeIso : (n : ℕ) →
    (Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePower (X := Spec R) (tilde M) n ≅
      tilde (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePower M n))
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | n + 2 => doubleDualTensorTildeIso R (Iso.refl (tilde M)) (reflexivePowerTildeIso (n + 1))

/-- **The comparison is compatible with the transition out of degree `0`**, the morphism
`𝒪_{Spec R} ⟶ M^~` attached to the global section `s`. -/
theorem reflexivePowerTildeIso_transition_zero (s : M) :
    Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerTransition (X := Spec R) (tilde M)
          (tildeGlobalSection M s) 0 ≫ (reflexivePowerTildeIso R M 1).hom =
      (reflexivePowerTildeIso R M 0).hom ≫
        tilde.map
          (Stacks.AlgebraicGeometry.ModuleReflexivePower.reflexivePowerTransition M s 0) := by
  have key : (tilde M).unitHomEquiv.symm (tildeGlobalSection M s) =
      tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M s)) := by
    refine tilde_unit_hom_ext ?_
    refine Eq.trans ?_ (congrArg (fun g => g.hom (1 : R))
      (tilde.toOpen_map_app (ModuleCat.ofHom (LinearMap.toSpanSingleton R M s)) ⊤)).symm
    rw [toOpen_one]
    exact (tildeGlobalSection_unitHom_app_one M s).trans
      (congrArg (fun m => (tilde.toOpen M ⊤).hom m) (one_smul R s).symm)
  show (tilde M).unitHomEquiv.symm (tildeGlobalSection M s) ≫ 𝟙 _ =
    𝟙 _ ≫ tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M s))
  exact (Category.comp_id _).trans (key.trans (Category.id_comp _).symm)

end AlgebraicGeometry

end
