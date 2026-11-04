module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.EtaleModuleRestrictScalarsLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.HigherDirectImageExtendScalars

/-!
# Lifting almost linear isogenies along restriction of scalars

Let `ρ : Λ →+* Λ'` and `A`, `B` sheaves of `Λ'`-modules on the small étale site of `X`. Suppose
`F : ρ_* A ⟶ ρ_* B` and `G : ρ_* B ⟶ ρ_* A` form an `ℓᶜ`-isogeny (`F ≫ G = ℓᶜ`, `G ≫ F = ℓᶜ`)
and commute with every `l ∈ Λ'` up to `ℓᵗ`-torsion:
`ℓᵗ (ρ_*(l) ≫ F) = ℓᵗ (F ≫ ρ_*(l))`. Then `ℓᵗ F` and `ℓᵗ G` are `Λ'`-linear on sections, hence
restrictions of scalars of morphisms `f : A ⟶ B`, `g : B ⟶ A`
(`Stacks.EtaleCohomology.exists_etaleModuleRestrictScalars_map_eq`), and these form an
`ℓ^{c+2t}`-isogeny (`Stacks.EtaleCohomology.exists_isogeny_of_etaleModuleRestrictScalars`). This is
the last step of the comparison of the levels in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): the comparison maps are built over `ℤ_ℓ`
and only commute with the coefficients `O/ℓ^{N+1}` up to a bounded power of `ℓ`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleRestrictScalars_map_injective`.
* `Stacks.EtaleCohomology.exists_isogeny_of_etaleModuleRestrictScalars`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}

/-- **Restriction of scalars is faithful**: it does not change the underlying maps. -/
theorem etaleModuleRestrictScalars_map_injective {A B : EtaleModules.{u, 0} Λ' X} {a b : A ⟶ B}
    (h : (etaleModuleRestrictScalars ρ X).map a = (etaleModuleRestrictScalars ρ X).map b) :
    a = b := by
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun φ : (etaleModuleRestrictScalars ρ X).obj A ⟶
    (etaleModuleRestrictScalars ρ X).obj B => (φ.hom.app U).hom x) h

/-- An `ℓᵗ`-almost linear morphism becomes linear on sections after multiplication by `ℓᵗ`. -/
theorem pow_nsmul_smul_of_almostLinear {A B : EtaleModules.{u, 0} Λ' X} {ℓ t : ℕ}
    (F : (etaleModuleRestrictScalars ρ X).obj A ⟶ (etaleModuleRestrictScalars ρ X).obj B)
    (hF : ∀ l : Λ',
      ℓ ^ t • ((etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X l).app A) ≫ F) =
        ℓ ^ t • (F ≫ (etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X l).app B)))
    (U : X.Etaleᵒᵖ) (l : Λ') (x : A.obj.obj U) :
    ((ℓ ^ t • F).hom.app U).hom (l • x) =
      l • (show B.obj.obj U from ((ℓ ^ t • F).hom.app U).hom x) := by
  have h := congrArg (fun φ : (etaleModuleRestrictScalars ρ X).obj A ⟶
    (etaleModuleRestrictScalars ρ X).obj B => (φ.hom.app U).hom x) (hF l)
  change ℓ ^ t • (F.hom.app U).hom (l • x) =
    ℓ ^ t • (l • (show B.obj.obj U from (F.hom.app U).hom x)) at h
  show ℓ ^ t • (F.hom.app U).hom (l • x) =
    l • (show B.obj.obj U from ℓ ^ t • (F.hom.app U).hom x)
  rw [h, smul_comm]
  rfl

/-- **An `ℓᵗ`-almost `Λ'`-linear `ℓᶜ`-isogeny of restrictions of scalars gives an
`ℓ^{c+2t}`-isogeny of sheaves of `Λ'`-modules.** -/
theorem exists_isogeny_of_etaleModuleRestrictScalars {A B : EtaleModules.{u, 0} Λ' X}
    {ℓ c t : ℕ}
    (F : (etaleModuleRestrictScalars ρ X).obj A ⟶ (etaleModuleRestrictScalars ρ X).obj B)
    (G : (etaleModuleRestrictScalars ρ X).obj B ⟶ (etaleModuleRestrictScalars ρ X).obj A)
    (hFG : F ≫ G = ℓ ^ c • 𝟙 _) (hGF : G ≫ F = ℓ ^ c • 𝟙 _)
    (hF : ∀ l : Λ',
      ℓ ^ t • ((etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X l).app A) ≫ F) =
        ℓ ^ t • (F ≫ (etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X l).app B)))
    (hG : ∀ l : Λ',
      ℓ ^ t • ((etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X l).app B) ≫ G) =
        ℓ ^ t • (G ≫ (etaleModuleRestrictScalars ρ X).map ((etaleModuleSMul X l).app A))) :
    ∃ (f : A ⟶ B) (g : B ⟶ A), f ≫ g = ℓ ^ (c + 2 * t) • 𝟙 _ ∧ g ≫ f = ℓ ^ (c + 2 * t) • 𝟙 _ := by
  obtain ⟨f, hf⟩ := exists_etaleModuleRestrictScalars_map_eq ρ (ℓ ^ t • F)
    (pow_nsmul_smul_of_almostLinear ρ F hF)
  obtain ⟨g, hg⟩ := exists_etaleModuleRestrictScalars_map_eq ρ (ℓ ^ t • G)
    (pow_nsmul_smul_of_almostLinear ρ G hG)
  have key : ∀ {P Q : EtaleModules.{u, 0} Λ' X}
      (F₁ : (etaleModuleRestrictScalars ρ X).obj P ⟶ (etaleModuleRestrictScalars ρ X).obj Q)
      (G₁ : (etaleModuleRestrictScalars ρ X).obj Q ⟶ (etaleModuleRestrictScalars ρ X).obj P)
      (f₁ : P ⟶ Q) (g₁ : Q ⟶ P), (etaleModuleRestrictScalars ρ X).map f₁ = ℓ ^ t • F₁ →
      (etaleModuleRestrictScalars ρ X).map g₁ = ℓ ^ t • G₁ → F₁ ≫ G₁ = ℓ ^ c • 𝟙 _ →
        f₁ ≫ g₁ = ℓ ^ (c + 2 * t) • 𝟙 _ := by
    intro P Q F₁ G₁ f₁ g₁ hf₁ hg₁ h₁
    apply etaleModuleRestrictScalars_map_injective ρ
    rw [Functor.map_comp, hf₁, hg₁, Functor.map_nsmul, CategoryTheory.Functor.map_id,
      Preadditive.nsmul_comp, Preadditive.comp_nsmul, h₁, smul_smul, smul_smul, ← pow_add,
      ← pow_add]
    congr 2
    omega
  exact ⟨f, g, key F G f g hf hg hFG, key G F g f hg hf hGF⟩

end Stacks.EtaleCohomology

end
