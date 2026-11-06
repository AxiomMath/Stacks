module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# Lifting morphisms along restriction of scalars of étale sheaves of modules

Let `ρ : Λ →+* Λ'`. A morphism `φ : ρ_* A ⟶ ρ_* B` between the restrictions of scalars of two
sheaves of `Λ'`-modules on the small étale site of `X` whose components are `Λ'`-linear on
sections is the restriction of scalars of a morphism `A ⟶ B`
(`Stacks.EtaleCohomology.exists_etaleModuleRestrictScalars_map_eq`): the components are the same
maps. This is how a `ℤ_ℓ`-linear isogeny commuting with the action of the coefficient ring
`O''/ℓ^{N+1}` becomes `O''/ℓ^{N+1}`-linear in the comparison of the levels of the Fourier family
in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (step R1 of S7C2).

## Main results

* `Stacks.EtaleCohomology.exists_etaleModuleRestrictScalars_map_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-- **A sectionwise `Λ'`-linear morphism of restrictions of scalars is a restriction of
scalars.** -/
theorem exists_etaleModuleRestrictScalars_map_eq {X : Scheme.{u}} {A B : EtaleModules.{u, 0} Λ' X}
    (φ : (etaleModuleRestrictScalars ρ X).obj A ⟶ (etaleModuleRestrictScalars ρ X).obj B)
    (hφ : ∀ U (l : Λ') (x : A.obj.obj U), (φ.hom.app U).hom (l • x) =
      l • (show B.obj.obj U from (φ.hom.app U).hom x)) :
    ∃ ψ : A ⟶ B, (etaleModuleRestrictScalars ρ X).map ψ = φ := by
  refine ⟨ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := (φ.hom.app U).hom
          map_add' := map_add (φ.hom.app U).hom
          map_smul' := hφ U }
      naturality := fun U V f => by
        ext x
        exact ConcreteCategory.congr_hom (φ.hom.naturality f) x }, ?_⟩
  ext U x
  rfl

end Stacks.EtaleCohomology

end
