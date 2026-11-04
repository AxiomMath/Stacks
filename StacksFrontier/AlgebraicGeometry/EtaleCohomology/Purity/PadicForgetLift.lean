module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing

/-!
# Additive maps of `ℓ`-power torsion sheaves of `ℤ_ℓ`-modules are `ℤ_ℓ`-linear

On a group killed by `ℓᵐ`, a `ℤ_ℓ`-module structure is that of `ℤ/ℓᵐ`: the scalar `a` acts as
its residue modulo `ℓᵐ` (`Stacks.EtaleCohomology.padicInt_smul_eq_val_nsmul`). Hence a morphism of
the underlying abelian sheaves of two sheaves of `ℤ_ℓ`-modules on `X_étale` killed by `ℓᵐ` is a
morphism of sheaves of `ℤ_ℓ`-modules (`Stacks.EtaleCohomology.etaleModulePadicLift`).

This is used to build the purity maps `𝓗om(μ_{ℓⁿ⁺¹}, Gₙ) ⟶ R¹ j_*(j⁻¹ Gₙ)` of a tower of
`ℤ_ℓ`-sheaves on underlying abelian sheaves, in the tower form of cohomological purity
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.etaleModulePadicLift`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetAb_map_etaleModulePadicLift`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-- **A sheaf of modules killed by `N` has its sections killed by `N`.** -/
theorem etaleModule_nsmul_section_eq_zero {Λ : Type} [Ring Λ] {X : Scheme.{u}}
    {P : EtaleModules.{u, 0} Λ X} {N : ℕ} (hP : N • 𝟙 P = 0) (U : X.Etaleᵒᵖ)
    (x : ((etaleModuleForgetAb.{u, 0} Λ X).obj P).obj.obj U) : N • x = 0 := by
  have h1 : N • 𝟙 ((etaleModuleForgetAb.{u, 0} Λ X).obj P) = 0 := by
    rw [← (etaleModuleForgetAb.{u, 0} Λ X).map_id, ← (etaleModuleForgetAb.{u, 0} Λ X).map_nsmul,
      hP, Functor.map_zero]
  have h2 := congrArg (fun f => (f.hom.app U).hom x) h1
  simp only [abelianSheaf_nsmul_app] at h2
  exact h2

variable {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}

/-- **An additive map of `ℓᵐ`-torsion sheaves of `ℤ_ℓ`-modules is `ℤ_ℓ`-linear**: the morphism of
sheaves of `ℤ_ℓ`-modules with a given underlying morphism of abelian sheaves. -/
def etaleModulePadicLift (m : ℕ) {M M' : EtaleModules.{u, 0} ℤ_[ℓ] X}
    (hM : ℓ ^ m • 𝟙 M = 0) (hM' : ℓ ^ m • 𝟙 M' = 0)
    (φ : (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] X).obj M ⟶ (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] X).obj M') :
    M ⟶ M' :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (φ.hom.app U).hom x
          map_add' := fun x y => map_add (φ.hom.app U).hom x y
          map_smul' := fun a x => by
            rw [RingHom.id_apply, padicInt_smul_eq_val_nsmul m a x
                (etaleModule_nsmul_section_eq_zero hM U x),
              padicInt_smul_eq_val_nsmul (M := M'.obj.obj U) m a ((φ.hom.app U).hom x)
                (etaleModule_nsmul_section_eq_zero hM' U _)]
            exact map_nsmul (φ.hom.app U).hom _ x }
     naturality := fun U V f => by
        ext x
        exact congrArg (fun g => g.hom x) (φ.hom.naturality f) }⟩

/-- The underlying morphism of abelian sheaves of `Stacks.EtaleCohomology.etaleModulePadicLift` is
the given one. -/
@[simp]
theorem etaleModuleForgetAb_map_etaleModulePadicLift (m : ℕ) {M M' : EtaleModules.{u, 0} ℤ_[ℓ] X}
    (hM : ℓ ^ m • 𝟙 M = 0) (hM' : ℓ ^ m • 𝟙 M' = 0)
    (φ : (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] X).obj M ⟶ (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] X).obj M') :
    (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] X).map (etaleModulePadicLift m hM hM' φ) = φ :=
  rfl

end Stacks.EtaleCohomology

end
