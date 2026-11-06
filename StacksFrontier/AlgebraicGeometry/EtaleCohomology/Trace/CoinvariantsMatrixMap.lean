module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality

/-!
# Intertwiners on coinvariants and on level modules

A matrix `A` commuting with a matrix representation `τ : Γ → GL_m(R)` induces an endomorphism of
the coinvariants under any subgroup `H` (`Stacks.EtaleCohomology.coinvariantsMatrixMap`). For an
integral representation `ρ` and an integral intertwiner `A`, these endomorphisms are compatible
with the reduction of coinvariants modulo `ℓ ^ k`, with their rationalization and with conjugation,
and `A` acts on the level modules and on the level coinvariants as finite continuous modules,
compatibly with the quotient map; on the level sheaves this action is the morphism of sheaves
induced by `A` (`Stacks.EtaleCohomology.lisseSheaf_map_levelModuleMap`).

## Main definitions

* `Stacks.EtaleCohomology.coinvariantsMatrixMap`: the endomorphism of the coinvariants induced by
  a matrix commuting with a representation.
* `Stacks.EtaleCohomology.levelModuleMap`: the endomorphism of the level module `(ℤ/ℓ^k)^r` given
  by an intertwiner.
* `Stacks.EtaleCohomology.levelCoinvariantsMap`: the endomorphism of the level coinvariants given
  by an intertwiner.

## Main results

* `Stacks.EtaleCohomology.lisseSheaf_map_levelModuleMap`: on the level sheaves, the action of an
  intertwiner is the morphism of sheaves it induces.
-/

@[expose] public noncomputable section

open CategoryTheory Representation Matrix AlgebraicGeometry Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

/-! ### Intertwiners on coinvariants -/

section Coinvariants

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ) {R : Type*} [CommRing R] {m : ℕ}
  (τ : Γ →* GL (Fin m) R) (A : Matrix (Fin m) (Fin m) R) (hA : ∀ g, A * (τ g).val = (τ g).val * A)

include hA in
/-- A matrix commuting with `τ` commutes with the action of `τ g` on vectors. -/
theorem mulVec_matrixRepresentation_of_commute (g : Γ) (v : Fin m → R) :
    A *ᵥ matrixRepresentation τ g v = matrixRepresentation τ g (A *ᵥ v) := by
  rw [matrixRepresentation_apply, matrixRepresentation_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hA]

/-- **The endomorphism of the `H`-coinvariants of `τ` induced by a matrix commuting with `τ`.** -/
def coinvariantsMatrixMap :
    Module.End R (Coinvariants ((matrixRepresentation τ).comp H.subtype)) :=
  Coinvariants.lift _ (Coinvariants.mk _ ∘ₗ Matrix.mulVecLin A) fun h => LinearMap.ext fun v => by
    change Coinvariants.mk _ (A *ᵥ matrixRepresentation τ h v) = Coinvariants.mk _ (A *ᵥ v)
    rw [mulVec_matrixRepresentation_of_commute τ A hA]
    exact Coinvariants.mk_self_apply ((matrixRepresentation τ).comp H.subtype) h _

/-- The endomorphism `coinvariantsMatrixMap` sends the class of `v` to the class of `A *ᵥ v`. -/
theorem coinvariantsMatrixMap_mk (v : Fin m → R) :
    coinvariantsMatrixMap H τ A hA (Coinvariants.mk _ v) = Coinvariants.mk _ (A *ᵥ v) :=
  rfl

/-- The induced endomorphism commutes with the action of `Γ` on the coinvariants. -/
theorem coinvariantsMatrixMap_coinvariantsFrobenius [H.Normal] (φ : Γ)
    (x : Coinvariants ((matrixRepresentation τ).comp H.subtype)) :
    coinvariantsMatrixMap H τ A hA (coinvariantsFrobenius H τ φ x) =
      coinvariantsFrobenius H τ φ (coinvariantsMatrixMap H τ A hA x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  change Coinvariants.mk _ (A *ᵥ matrixRepresentation τ φ v) =
    Coinvariants.mk _ (matrixRepresentation τ φ (A *ᵥ v))
  rw [mulVec_matrixRepresentation_of_commute τ A hA]

end Coinvariants

/-! ### Integral intertwiners: reduction, rationalization, conjugation -/

section Integral

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ) {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : Γ →* GL (Fin r) ℤ_[ℓ]) (A : Matrix (Fin r) (Fin r) ℤ_[ℓ])
  (hA : ∀ g, A * (ρ g).val = (ρ g).val * A)

include hA in
/-- The reduction of an intertwiner modulo `ℓ ^ k` intertwines the level representation. -/
theorem map_toZModPow_commute (k : ℕ) (g : Γ) :
    A.map (PadicInt.toZModPow k) * (levelMatrixRepresentation ρ k g).val =
      (levelMatrixRepresentation ρ k g).val * A.map (PadicInt.toZModPow k) := by
  exact (show Commute A (ρ g).val from hA g).map (RingHom.mapMatrix (PadicInt.toZModPow k))

include hA in
/-- An intertwiner read over `ℚ_ℓ` intertwines the representation read over `ℚ_ℓ`. -/
theorem map_coe_commute (g : Γ) :
    A.map (PadicInt.Coe.ringHom (p := ℓ)) * (rationalGL ρ g).val =
      (rationalGL ρ g).val * A.map (PadicInt.Coe.ringHom (p := ℓ)) := by
  exact (show Commute A (ρ g).val from hA g).map
    (RingHom.mapMatrix (PadicInt.Coe.ringHom (p := ℓ)))

/-- Reduction modulo `ℓ ^ k` carries `A *ᵥ v` to the reduction of `A` applied to the reduction
of `v`. -/
theorem padicVecReduction_mulVec (k : ℕ) (v : Fin r → ℤ_[ℓ]) :
    padicVecReduction k (A *ᵥ v) = A.map (PadicInt.toZModPow k) *ᵥ padicVecReduction k v := by
  funext i
  simp only [padicVecReduction_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

/-- The inclusion `ℤ_ℓ^r → ℚ_ℓ^r` carries `A *ᵥ v` to `A` read over `ℚ_ℓ` applied to the image
of `v`. -/
theorem padicVecInclusion_mulVec (v : Fin r → ℤ_[ℓ]) :
    padicVecInclusion (A *ᵥ v) = A.map (PadicInt.Coe.ringHom (p := ℓ)) *ᵥ padicVecInclusion v := by
  funext i
  simp only [padicVecInclusion, LinearMap.compLeft_apply, Function.comp_apply,
    Algebra.linearMap_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

/-- The reduction of coinvariants carries the endomorphism of an intertwiner to that of its
reduction. -/
theorem integralCoinvariantsReduction_coinvariantsMatrixMap (k : ℕ) (x : integralCoinvariants H ρ) :
    integralCoinvariantsReduction H ρ k (coinvariantsMatrixMap H ρ A hA x) =
      coinvariantsMatrixMap H (levelMatrixRepresentation ρ k) (A.map (PadicInt.toZModPow k))
        (map_toZModPow_commute ρ A hA k) (integralCoinvariantsReduction H ρ k x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  change Coinvariants.mk _ (padicVecReduction k (A *ᵥ v)) =
    Coinvariants.mk _ (A.map (PadicInt.toZModPow k) *ᵥ padicVecReduction k v)
  rw [padicVecReduction_mulVec]

/-- The rationalization of coinvariants carries the endomorphism of an intertwiner to that of the
intertwiner read over `ℚ_ℓ`. -/
theorem integralCoinvariantsRationalization_coinvariantsMatrixMap (x : integralCoinvariants H ρ) :
    integralCoinvariantsRationalization H ρ (coinvariantsMatrixMap H ρ A hA x) =
      coinvariantsMatrixMap H (rationalGL ρ) (A.map (PadicInt.Coe.ringHom (p := ℓ)))
        (map_coe_commute ρ A hA) (integralCoinvariantsRationalization H ρ x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  change Coinvariants.mk _ (padicVecInclusion (A *ᵥ v)) =
    Coinvariants.mk _ (A.map (PadicInt.Coe.ringHom (p := ℓ)) *ᵥ padicVecInclusion v)
  rw [padicVecInclusion_mulVec]

variable {ρ} in
/-- Conjugation by `P` carries the endomorphism of an intertwiner `A'` of `P⁻¹ τ P` to that of
`P A' P⁻¹`. -/
theorem rationalCoinvariantsConjEquiv_coinvariantsMatrixMap (τ : Γ →* GL (Fin r) ℚ_[ℓ])
    (P : GL (Fin r) ℚ_[ℓ]) (hP : ∀ g, rationalGL ρ g = P⁻¹ * τ g * P)
    (A' : Matrix (Fin r) (Fin r) ℚ_[ℓ])
    (hA' : ∀ g, A' * (rationalGL ρ g).val = (rationalGL ρ g).val * A')
    (B' : Matrix (Fin r) (Fin r) ℚ_[ℓ]) (hB' : ∀ g, B' * (τ g).val = (τ g).val * B')
    (hAB : P.val * A' = B' * P.val) (x : rationalCoinvariants H ρ) :
    rationalCoinvariantsConjEquiv H τ P hP (coinvariantsMatrixMap H (rationalGL ρ) A' hA' x) =
      coinvariantsMatrixMap H τ B' hB' (rationalCoinvariantsConjEquiv H τ P hP x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  change Coinvariants.mk _ (P.val *ᵥ (A' *ᵥ v)) = Coinvariants.mk _ (B' *ᵥ (P.val *ᵥ v))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAB]

end Integral

/-! ### Intertwiners on the level modules -/

section Level

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) [H.Normal] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {ρ : G →* GL (Fin r) ℤ_[ℓ]}
  (hρ : Continuous ρ) (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ g).val * A)

/-- **The endomorphism of the level module `(ℤ/ℓ^k)^r` given by an intertwiner of `ρ`.** -/
def levelModuleMap (k : ℕ) :
    levelModule.{u + 1, u + 1} ρ hρ k ⟶ levelModule.{u + 1, u + 1} ρ hρ k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun y => ULift.up (A.map (PadicInt.toZModPow k) *ᵥ y.down)
          map_add' := fun a b => ULift.ext (Matrix.mulVec_add _ a.down b.down)
          map_smul' := fun c a => ULift.ext (Matrix.mulVec_smul _ c a.down) }
      comm := fun g => by
        ext y
        exact ULift.ext (mulVec_levelRepresentation A hA k g y.down) }))

/-- **The endomorphism of the level coinvariants given by an intertwiner of `ρ`.** -/
def levelCoinvariantsMap (k : ℕ) [NeZero (ℓ ^ k)] :
    levelCoinvariantsModule H ρ hρ k ⟶ levelCoinvariantsModule H ρ hρ k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        ((ULift.moduleEquiv (R := ZMod (ℓ ^ k)) (M := levelCoinvariants H ρ k)).symm.toLinearMap ∘ₗ
          coinvariantsMatrixMap H (levelMatrixRepresentation ρ k) (A.map (PadicInt.toZModPow k))
            (map_toZModPow_commute ρ A hA k) ∘ₗ
          (ULift.moduleEquiv (R := ZMod (ℓ ^ k)) (M := levelCoinvariants H ρ k)).toLinearMap)
      comm := fun g => by
        ext ⟨y⟩
        exact ULift.ext (coinvariantsMatrixMap_coinvariantsFrobenius H
          (levelMatrixRepresentation ρ k) (A.map (PadicInt.toZModPow k))
          (map_toZModPow_commute ρ A hA k) g y) }))

/-- On underlying elements, `levelCoinvariantsMap` is the endomorphism `coinvariantsMatrixMap` of
the reduction of `A` modulo `ℓ ^ k`. -/
theorem levelCoinvariantsMap_apply (k : ℕ) [NeZero (ℓ ^ k)]
    (y : ULift.{u + 1} (levelCoinvariants H ρ k)) :
    ((levelCoinvariantsMap H hρ A hA k).hom.hom.hom.hom.hom y).down =
      coinvariantsMatrixMap H (levelMatrixRepresentation ρ k) (A.map (PadicInt.toZModPow k))
        (map_toZModPow_commute ρ A hA k) y.down :=
  rfl

/-- The quotient onto the level coinvariants carries the endomorphism of an intertwiner on the
level module to its endomorphism of the level coinvariants. -/
theorem levelModuleMap_comp_levelCoinvariantsQuotient (k : ℕ) [NeZero (ℓ ^ k)] :
    levelModuleMap hρ A hA k ≫ levelCoinvariantsQuotient H ρ hρ k =
      levelCoinvariantsQuotient H ρ hρ k ≫ levelCoinvariantsMap H hρ A hA k := by
  ext
  rfl

end Level

/-! ### On the level sheaves -/

section Sheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]}
  (hρ : Continuous ρ) (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ g).val * A)

/-- **On the level sheaves, the lisse sheaf of the endomorphism of the level module given by an
intertwiner is the morphism of level sheaves induced by it.** -/
theorem lisseSheaf_map_levelModuleMap (k : ℕ) [NeZero (ℓ ^ k)] :
    (lisseSheaf B X x (ZMod (ℓ ^ k))).map (levelModuleMap hρ A hA k) =
      representationLevelMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        hρ hρ A hA k :=
  rfl

end Sheaf

end Stacks.EtaleCohomology

end
