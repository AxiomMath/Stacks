module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroPairingNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseEtaleSheafTensorNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantsMatrixMap

/-!
# The intertwiners `A` and `Aᵀ` are adjoint for the pairing of the levels

Let `ρ₀ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous and `A ∈ M_r(ℤ_ℓ)` commute with `ρ₀`. Then `Aᵀ`
commutes with the contragredient `ρ₀^∨ = (ρ₀⁻¹)ᵀ`
(`Stacks.EtaleCohomology.transpose_mul_contragredient`), and the morphisms of ℓ-adic sheaves
`ℱ_A : ℱ_{ρ₀} ⟶ ℱ_{ρ₀}`, `ℱ_{Aᵀ} : ℱ_{ρ₀^∨} ⟶ ℱ_{ρ₀^∨}` are adjoint for the pairing of the levels
`Fₙ ⊗ F'ₙ ⟶ ℤ/ℓⁿ⁺¹` (`Stacks.EtaleCohomology.representationLevelEtalePairing`, the dot product):
`(A v) · w = v · (Aᵀ w)` (`Stacks.EtaleCohomology.representationLevelEtalePairing_adjoint`).
Extended by zero to a compactification `X ⊂ X̄`, they are adjoint for the coefficient pairing of
Poincaré duality on `X̄`
(`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing_adjoint`).

## Main results

* `Stacks.EtaleCohomology.transpose_mul_contragredient`: `Aᵀ` commutes with `ρ^∨` when `A`
  commutes with `ρ`.
* `Stacks.EtaleCohomology.representationLevelEtalePairing_adjoint`: `ℱ_A` and `ℱ_{Aᵀ}` are adjoint
  for the pairing of the levels on `X`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing_adjoint`: `ℱ_A` and `ℱ_{Aᵀ}`
  are adjoint for the coefficient pairing of Poincaré duality on `X̄`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **The transpose of an intertwiner of `ρ` intertwines the contragredient** `ρ^∨ = (ρ⁻¹)ᵀ`. -/
theorem transpose_mul_contragredient {G : Type*} [Group G] {r : ℕ} {R : Type*} [CommRing R]
    {ρ : G →* GL (Fin r) R} {A : Matrix (Fin r) (Fin r) R}
    (hA : ∀ g, A * (ρ g).val = (ρ g).val * A) (g : G) :
    Aᵀ * (contragredient ρ g).val = (contragredient ρ g).val * Aᵀ := by
  rw [contragredient_val, ← map_inv, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hA]

attribute [local instance] moduleCat_hasLimitsOfSize Sheaf.monoidalCategory
  isMonoidal_W_etaleModules

section Levels

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)

/-- **The dot product is balanced for `A` and `Aᵀ`**: `(A v) · w = v · (Aᵀ w)` on the level
modules of `ρ₀` and of its contragredient. -/
theorem levelDotPairing_levelModuleMap (A : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ₀ g).val = (ρ₀ g).val * A) (k : ℕ) [NeZero (ℓ ^ k)] (v w) :
    levelDotPairing ρ₀ hρ₀ k ((levelModuleMap hρ₀ A hA k).hom.hom.hom.hom.hom v) w =
      levelDotPairing ρ₀ hρ₀ k v
        ((levelModuleMap (continuous_contragredient hρ₀) Aᵀ (transpose_mul_contragredient hA)
          k).hom.hom.hom.hom.hom w) := by
  refine ULift.ext _ _ ?_
  change (A.map (PadicInt.toZModPow k) *ᵥ (v : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down) ⬝ᵥ
      (w : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down =
    (v : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down ⬝ᵥ
      (Aᵀ.map (PadicInt.toZModPow k) *ᵥ (w : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))).down)
  rw [Matrix.dotProduct_mulVec, Matrix.transpose_map, Matrix.vecMul_transpose,
    dotProduct_comm]

end Levels

section Sheaves

/-- Sheafification of étale sheaves of modules at the coefficient universe `u + 1`. -/
local instance hasSheafify_smallEtale_levelPairingAdjoint (Λ : Type) [CommRing Λ]
    (S : Scheme.{u}) : HasSheafify S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} S.smallEtaleTopology Λ

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1] (n : ℕ)

/-- The powers of `ℓ` are nonzero. -/
local instance neZero_pow_levelPairingAdjoint (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- **The level of `ℱ_A` is the lisse sheaf of `A` on the level module**, through the
identification of the levels of `ℱ_{ρ₀}` with the lisse sheaves of the level modules. -/
theorem etaleLevelMap_representationLAdicSheafMap_comp_representationLevelEtaleIso
    (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ₀ g).val = (ρ₀ g).val * A) :
    LAdicSheaf.etaleLevelMap B X ℓ (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ A hA) n ≫
      (representationLevelEtaleIso B X x ρ₀ hρ₀ n).hom =
    (representationLevelEtaleIso B X x ρ₀ hρ₀ n).hom ≫
      (lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).map (levelModuleMap hρ₀ A hA (n + 1)) := by
  let E := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  have hmap : ∀ {P Q : Sheaf (SmallEtale.topology B X.1 X.2)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))}
      (_ : P = Q) (φ : P ⟶ P) (ψ : Q ⟶ Q), HEq φ ψ → HEq (E.functor.map φ) (E.functor.map ψ) := by
    rintro P _ rfl φ ψ hh
    rw [eq_of_heq hh]
  have h₁ : HEq (LAdicSheaf.etaleLevelMap B X ℓ (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ A hA) n)
      ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).map (levelModuleMap hρ₀ A hA (n + 1))) :=
    hmap (lisseSheaf_obj_levelModule B X x ρ₀ hρ₀ (n + 1)).symm _ _
      (heq_of_eq (lisseSheaf_map_levelModuleMap B X x hρ₀ A hA (n + 1))).symm
  have hi : (representationLevelEtaleIso B X x ρ₀ hρ₀ n).hom =
      eqToHom (congrArg E.functor.obj (lisseSheaf_obj_levelModule B X x ρ₀ hρ₀ (n + 1)).symm) :=
    eqToHom_map E.functor (lisseSheaf_obj_levelModule B X x ρ₀ hρ₀ (n + 1)).symm
  rw [hi]
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (h₁.trans (eqToHom_comp_heq _ _).symm))

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [AlgebraicGeometry.IsNoetherian X.1] in
/-- **`A` and `Aᵀ` are adjoint for the dot product pairing of lisse sheaves.** -/
theorem levelTensorHom_adjoint (A : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ₀ g).val = (ρ₀ g).val * A) (k : ℕ) [NeZero (ℓ ^ k)] :
    (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).map (levelModuleMap hρ₀ A hA k) ▷ _ ≫
        levelTensorHom B X x ρ₀ hρ₀ k =
      _ ◁ (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).map
          (levelModuleMap (continuous_contragredient hρ₀) Aᵀ (transpose_mul_contragredient hA) k) ≫
        levelTensorHom B X x ρ₀ hρ₀ k := by
  have hadj := lisseEtaleSheafTensorHom_adjoint B X x (ZMod (ℓ ^ k))
    (levelDotPairing ρ₀ hρ₀ k) (levelDotPairing_equivariant ρ₀ hρ₀ k)
    (levelModuleMap hρ₀ A hA k)
    (levelModuleMap (continuous_contragredient hρ₀) Aᵀ (transpose_mul_contragredient hA) k)
    (levelDotPairing ρ₀ hρ₀ k) (levelDotPairing_equivariant ρ₀ hρ₀ k)
    (levelDotPairing_levelModuleMap B X x ρ₀ hρ₀ A hA k)
  simp only [levelTensorHom]
  exact (reassoc_of% hadj) _

/-- **`ℱ_A` and `ℱ_{Aᵀ}` are adjoint for the pairing of the levels** of `ℱ_{ρ₀}` and
`ℱ_{ρ₀^∨}` on `X`: `μ(A v, w) = μ(v, Aᵀ w)`, the dot product being balanced. -/
theorem representationLevelEtalePairing_adjoint (A : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ₀ g).val = (ρ₀ g).val * A) :
    LAdicSheaf.etaleLevelMap B X ℓ (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ A hA) n ▷ _ ≫
        representationLevelEtalePairing B X x ρ₀ hρ₀ n =
      _ ◁ LAdicSheaf.etaleLevelMap B X ℓ (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (continuous_contragredient hρ₀) (continuous_contragredient hρ₀) Aᵀ
          (transpose_mul_contragredient hA)) n ≫
        representationLevelEtalePairing B X x ρ₀ hρ₀ n := by
  simp only [representationLevelEtalePairing]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    etaleLevelMap_representationLAdicSheafMap_comp_representationLevelEtaleIso B X x ρ₀ hρ₀ n A hA,
    comp_whiskerRight_assoc, levelTensorHom_adjoint B X x ρ₀ hρ₀ A hA (n + 1),
    ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    ← etaleLevelMap_representationLAdicSheafMap_comp_representationLevelEtaleIso B X x
      (contragredient ρ₀) (continuous_contragredient hρ₀) n Aᵀ (transpose_mul_contragredient hA),
    whiskerLeft_comp_assoc]

variable {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f))

/-- **`ℱ_A` and `ℱ_{Aᵀ}` are adjoint for the coefficient pairing of Poincaré duality on `X̄`**
(`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`). -/
theorem LAdicSheaf.representationCurveLevelPairing_adjoint (A : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ₀ g).val = (ρ₀ g).val * A) :
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map
        (LAdicSheaf.etaleLevelMap B X ℓ (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ A hA) n) ▷ _ ≫
        LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j =
      _ ◁ (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).map
          (LAdicSheaf.etaleLevelMap B X ℓ (representationLAdicSheafMap B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
            (continuous_contragredient hρ₀) (continuous_contragredient hρ₀) Aᵀ
            (transpose_mul_contragredient hA)) n) ≫
        LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j :=
  haveI := Fintype.ofFinite k
  LAdicSheaf.representationCurveLevelPairing_whisker B X x ρ₀ hρ₀ n f j _ _
    (representationLevelEtalePairing_adjoint B X x ρ₀ hρ₀ n A hA)

end Sheaves

end Stacks.EtaleCohomology
