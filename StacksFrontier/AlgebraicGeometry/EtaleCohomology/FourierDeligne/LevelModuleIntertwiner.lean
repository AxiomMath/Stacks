module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality

/-!
# Intertwiners on the level modules

A matrix `A` intertwining two continuous representations `ρ : G → GL_r(ℤ_ℓ)` and
`ρ' : G → GL_{r'}(ℤ_ℓ)` (`A ρ(g) = ρ'(g) A`) induces, by multiplication by its reduction modulo
`ℓᵏ`, a morphism `(ℤ/ℓᵏ)^r → (ℤ/ℓᵏ)^{r'}` of the level modules, which are finite `ℤ/ℓᵏ`-modules
with continuous `G`-action.

## Main definitions

* `Stacks.EtaleCohomology.levelModuleHom`: the morphism of level modules induced by an intertwiner
  `A`, given by multiplication by `A` modulo `ℓᵏ`.

## Main results

* `Stacks.EtaleCohomology.levelModuleHom_apply`: the formula `y ↦ (A mod ℓᵏ) *ᵥ y` for this
  morphism.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupCohomology

universe u

open scoped Matrix

namespace Stacks.EtaleCohomology

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ} {G : Type (u + 1)} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ρ : G →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : G →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

/-- **The morphism of level modules `(ℤ/ℓᵏ)^r → (ℤ/ℓᵏ)^{r'}` induced by an intertwiner** `A` of
`ρ` and `ρ'` (`A ρ(g) = ρ'(g) A`): multiplication by `A` modulo `ℓᵏ`. -/
def levelModuleHom (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    levelModule.{u + 1, u + 1} ρ hρ k ⟶ levelModule.{u + 1, u + 1} ρ' hρ' k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun y => ULift.up (A.map (PadicInt.toZModPow k) *ᵥ y.down)
          map_add' := fun a b => ULift.ext _ _ (Matrix.mulVec_add _ a.down b.down)
          map_smul' := fun c a => ULift.ext _ _ (Matrix.mulVec_smul _ c a.down) }
      comm := fun g => by
        ext y
        exact ULift.ext _ _ (mulVec_levelRepresentation A hA k g y.down) }))

/-- The morphism `levelModuleHom hρ hρ' A hA k` sends `y` to the product of the reduction of `A`
modulo `ℓᵏ` with `y`. -/
@[simp]
theorem levelModuleHom_apply (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ)
    (y : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :
    ((levelModuleHom hρ hρ' A hA k).hom.hom.hom.hom y).down =
      A.map (PadicInt.toZModPow k) *ᵥ y.down :=
  rfl

end Stacks.EtaleCohomology

end
