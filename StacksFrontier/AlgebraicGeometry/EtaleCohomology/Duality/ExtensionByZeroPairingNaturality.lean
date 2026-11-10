module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLevelPairingRepresentationExtension

/-!
# Adjoint morphisms for pairings extended by zero

Let `j : U ⟶ X` be an open immersion, `p₁ : A₁ ⊗ B₁ ⟶ ℤ/N`, `p₂ : A₂ ⊗ B₂ ⟶ ℤ/N` pairings on `U`
and `a : A₁ ⟶ A₂`, `b : B₂ ⟶ B₁` adjoint for them: `p₂ ∘ (a ⊗ 1) = p₁ ∘ (1 ⊗ b)`. Then `j_! a` and
`j_! b` are adjoint for the pairings extended by zero
(`Stacks.EtaleCohomology.extensionByZeroPairing_whisker`): the tensor comparison of `j_!` is
natural. For the coefficient pairing of `ℱ_{ρ₀}` and `ℱ_{ρ₀^∨}` on `X ⊂ X̄`
(`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`) this turns adjointness of
morphisms of the levels on `X` into the hypothesis of
`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_map`
(`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing_whisker`), the adjointness of
the intertwiners of a representation and of its contragredient for the cup product pairing on an
open curve, in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.extensionByZeroPairing_whisker`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing_whisker`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Functor.OplaxMonoidal

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory moduleCat_hasLimitsOfSize
  isMonoidal_W_etaleModules

/-- Sheafification of étale sheaves of modules at the coefficient universe `u + 1`, pinned so that
instance search does not get stuck on a universe-polymorphic instance. -/
local instance hasSheafify_smallEtale_pairingNaturality (Λ : Type) [CommRing Λ]
    (S : Scheme.{u}) : HasSheafify S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} S.smallEtaleTopology Λ

section Generic

variable (N : ℕ) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Adjoint morphisms stay adjoint after extension by zero**: if
`p₂ ∘ (a ⊗ 1) = p₁ ∘ (1 ⊗ b)` on `U` then the same holds on `X` for `j_! a`, `j_! b` and the
pairings extended by zero (`Stacks.EtaleCohomology.extensionByZeroPairing`), by naturality of the
tensor comparison of `j_!`. -/
theorem extensionByZeroPairing_whisker {A₁ A₂ B₁ B₂ : EtaleModules.{u, 0} (ZMod N) U}
    (a : A₁ ⟶ A₂) (b : B₂ ⟶ B₁) (p₁ : A₁ ⊗ B₁ ⟶ 𝟙_ (EtaleModules.{u, 0} (ZMod N) U))
    (p₂ : A₂ ⊗ B₂ ⟶ 𝟙_ (EtaleModules.{u, 0} (ZMod N) U)) (h : a ▷ B₂ ≫ p₂ = A₁ ◁ b ≫ p₁) :
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).map a ▷
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj B₂ ≫ extensionByZeroPairing N j p₂ =
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj A₁ ◁
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).map b ≫ extensionByZeroPairing N j p₁ := by
  let := etaleModuleExtensionByZeroOplaxMonoidal (ZMod N) j
  let L := etaleModuleExtensionByZero.{u, 0} (ZMod N) j
  change L.map a ▷ L.obj B₂ ≫ inv (δ L A₂ B₂) ≫ L.map p₂ ≫ η L =
    L.obj A₁ ◁ L.map b ≫ inv (δ L A₁ B₁) ≫ L.map p₁ ≫ η L
  rw [← cancel_epi (δ L A₁ B₂), δ_natural_left_assoc, δ_natural_right_assoc,
    IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc, ← L.map_comp_assoc, ← L.map_comp_assoc, h]

end Generic

section Representation

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1] (n : ℕ)
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f))

/-- **Adjoint morphisms of the levels of `ℱ_{ρ₀}` and `ℱ_{ρ₀^∨}` are adjoint for the coefficient
pairing on `X̄`**: if `a : Fₙ ⟶ Fₙ` and `b : F'ₙ ⟶ F'ₙ` satisfy `μ_X ∘ (a ⊗ 1) = μ_X ∘ (1 ⊗ b)` for
the pairing of the levels on `X` (`Stacks.EtaleCohomology.representationLevelEtalePairing`), then
`j_! a` and `j_! b` are adjoint for
`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`, the hypothesis of
`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_map`. -/
theorem LAdicSheaf.representationCurveLevelPairing_whisker
    (a : LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n ⟶
      LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n)
    (b : LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
          (continuous_contragredient hρ₀)) n ⟶
      LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
          (continuous_contragredient hρ₀)) n)
    (h : a ▷ _ ≫ representationLevelEtalePairing B X x ρ₀ hρ₀ n =
      _ ◁ b ≫ representationLevelEtalePairing B X x ρ₀ hρ₀ n) :
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map a ▷ _ ≫
        LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j =
      _ ◁ (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map b ≫
        LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j := by
  have : IsOpenImmersion j.immersion := j.property.1
  exact extensionByZeroPairing_whisker (ℓ ^ (n + 1)) j.immersion a b _ _ h

end Representation

end Stacks.EtaleCohomology

end
