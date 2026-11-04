module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicSheafPreadditive

/-!
# Functoriality of `ℱ_ρ` in the representation

A matrix `A` intertwining two continuous representations `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` and
`ρ' : π₁(X, x̄) → GL_{r'}(ℤ_ℓ)` (`A ρ(g) = ρ'(g) A`) induces a morphism of ℓ-adic sheaves
`ℱ_ρ → ℱ_{ρ'}`: on level `n` it is the image under the equivalence `e` of Tag 0DV5 (2) of
multiplication by `A` modulo `ℓⁿ⁺¹` on the level modules.  The construction is functorial and
additive in `A`.  In particular the commutant of `ρ` acts on `ℱ_ρ`, which is how a representation
with coefficients in a finite `ℤ_ℓ`-algebra `O` (e.g. an `O^×`-valued character, as for
Artin–Schreier sheaves) gives an `O`-sheaf.

## Main definitions

* `Stacks.EtaleCohomology.levelAbelianMap`: multiplication by `A` on the level modules.
* `Stacks.EtaleCohomology.representationLevelMap`: the induced morphism of level sheaves.
* `Stacks.EtaleCohomology.representationLAdicSheafMap`: the induced morphism `ℱ_ρ → ℱ_{ρ'}`.

## Main results

* `Stacks.EtaleCohomology.representationLAdicSheafMap_one`, `.._mul`, `.._add`: functoriality
  and additivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r r' r'' : ℕ}

section Abelian

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : G →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ) {ρ' : G →* GL (Fin r') ℤ_[ℓ]}
  (hρ' : Continuous ρ') {ρ'' : G →* GL (Fin r'') ℤ_[ℓ]} (hρ'' : Continuous ρ'')

omit [IsTopologicalGroup G] in
/-- An intertwiner commutes with the level representations. -/
public theorem mulVec_levelRepresentation (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) (g : G) (y : Fin r → ZMod (ℓ ^ k)) :
    (A.map (PadicInt.toZModPow k)) *ᵥ levelRepresentation ρ k g y =
      levelRepresentation ρ' k g ((A.map (PadicInt.toZModPow k)) *ᵥ y) := by
  rw [levelRepresentation_apply, levelRepresentation_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hA]

omit [Fact ℓ.Prime] in
/-- Multiplication by the reduction of a matrix, on the level modules. -/
public def levelMapHom (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (k : ℕ) :
    ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) →+ ULift.{u + 1} (Fin r' → ZMod (ℓ ^ k)) where
  toFun y := ULift.up ((A.map (PadicInt.toZModPow k)) *ᵥ y.down)
  map_zero' := ULift.ext _ _ (Matrix.mulVec_zero (A.map (PadicInt.toZModPow k)))
  map_add' a b := ULift.ext _ _ (Matrix.mulVec_add (A.map (PadicInt.toZModPow k)) a.down b.down)

/-- **The map of level modules `(ℤ/ℓ^kℤ)^r → (ℤ/ℓ^kℤ)^{r'}` induced by an intertwiner** `A` of
`ρ` and `ρ'` (`A ρ(g) = ρ'(g) A`), as a morphism of finite discrete `G`-modules. -/
public def levelAbelianMap (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    levelAbelian ρ hρ k ⟶ levelAbelian ρ' hρ' k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (levelMapHom A k)
      comm := fun g => by
        ext y
        exact ULift.ext _ _ (mulVec_levelRepresentation A hA k g y.down) }))

@[simp]
public theorem levelAbelianMap_apply (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) (y : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :
    ((levelAbelianMap hρ hρ' A hA k).hom.hom.hom.hom.hom y).down =
      (A.map (PadicInt.toZModPow k)) *ᵥ y.down :=
  rfl

public theorem levelAbelianMap_one (k : ℕ) :
    levelAbelianMap hρ hρ 1 (fun g => by rw [one_mul, mul_one]) k = 𝟙 _ := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show ((1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (PadicInt.toZModPow k)) *ᵥ y.down = y.down
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

public theorem levelAbelianMap_mul (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (A' : Matrix (Fin r'') (Fin r') ℤ_[ℓ])
    (hA' : ∀ g, A' * (ρ' g).val = (ρ'' g).val * A') (k : ℕ) :
    levelAbelianMap hρ hρ'' (A' * A)
      (fun g => by rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hA', Matrix.mul_assoc]) k =
      levelAbelianMap hρ hρ' A hA k ≫ levelAbelianMap hρ' hρ'' A' hA' k := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show ((A' * A).map (PadicInt.toZModPow k)) *ᵥ y.down =
    (A'.map (PadicInt.toZModPow k)) *ᵥ ((A.map (PadicInt.toZModPow k)) *ᵥ y.down)
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

public theorem levelAbelianMap_add (A B : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hB : ∀ g, B * (ρ g).val = (ρ' g).val * B)
    (k : ℕ) :
    levelAbelianMap hρ hρ' (A + B) (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hA, hB]) k =
      levelAbelianMap hρ hρ' A hA k + levelAbelianMap hρ hρ' B hB k := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show ((A + B).map (PadicInt.toZModPow k)) *ᵥ y.down =
    (A.map (PadicInt.toZModPow k)) *ᵥ y.down + (B.map (PadicInt.toZModPow k)) *ᵥ y.down
  rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]

/-- The map of level modules commutes with the scalar operations. -/
public theorem finiteContinuousScalarFunctor_map_comp_levelAbelianMap
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ)
    (a : ZMod (ℓ ^ k)) :
    (finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _ (levelModule.{u + 1, u + 1} ρ hρ k)).map
        (X := SingleObj.star _) (Y := SingleObj.star _) a ≫ levelAbelianMap hρ hρ' A hA k =
      levelAbelianMap hρ hρ' A hA k ≫
        (finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _ (levelModule.{u + 1, u + 1} ρ' hρ' k)).map
          (X := SingleObj.star _) (Y := SingleObj.star _) a := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show (A.map (PadicInt.toZModPow k)) *ᵥ (a • y.down) = a • ((A.map (PadicInt.toZModPow k)) *ᵥ
    y.down)
  rw [Matrix.mulVec_smul]

/-- The map of level modules commutes with reduction. -/
public theorem levelAbelianReduction_comp_levelAbelianMap (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    levelAbelianReduction ρ hρ k ≫ levelAbelianMap hρ hρ' A hA k =
      levelAbelianMap hρ hρ' A hA (k + 1) ≫ levelAbelianReduction ρ' hρ' k := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show (A.map (PadicInt.toZModPow k)) *ᵥ (levelReduction k y.down) =
    levelReduction k ((A.map (PadicInt.toZModPow (k + 1))) *ᵥ y.down)
  funext i
  simp only [levelReduction_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul, levelRingHom_toZModPow]

end Abelian

/-! ### The induced morphisms of level sheaves and of ℓ-adic sheaves -/

section Sheaves

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')
  {ρ'' : EtaleFundamentalGroup X.1 x →* GL (Fin r'') ℤ_[ℓ]} (hρ'' : Continuous ρ'')

/-- The image under `e` of the map of level modules, as a morphism of abelian sheaves with scalar
operations. -/
public def representationLevelScalarsMap (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    representationLevelScalars B X x e ρ hρ k ⟶ representationLevelScalars B X x e ρ' hρ' k :=
  ObjectProperty.homMk
    { app := fun _ => (e.inverse.map (levelAbelianMap hρ hρ' A hA k)).hom
      naturality := fun _ _ a => congrArg (fun g => g.hom)
        ((e.inverse.map_comp _ _).symm.trans ((congrArg e.inverse.map
          (finiteContinuousScalarFunctor_map_comp_levelAbelianMap hρ hρ' A hA k a)).trans
            (e.inverse.map_comp _ _))) }

/-- **The morphism of `k`-th level sheaves `ℱ_{ρ,k} → ℱ_{ρ',k}` induced by an intertwiner.** -/
public def representationLevelMap (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k :=
  (scalarActionToModuleSheaf (SmallEtale.topology B X.1 X.2) (ZMod (ℓ ^ k))).map
    (representationLevelScalarsMap B X x e hρ hρ' A hA k)

/-- On sections, the morphism of level sheaves is the image of the map of level modules. -/
public theorem representationLevelMap_hom_app_apply (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) (U)
    (y : (representationLevelSheaf B X x e ρ hρ k).obj.obj U) :
    (((representationLevelMap B X x e hρ hρ' A hA k).hom.app U).hom y) =
      ((e.inverse.map (levelAbelianMap hρ hρ' A hA k)).hom.hom.app U).hom y :=
  rfl

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **The morphism of ℓ-adic sheaves `ℱ_ρ → ℱ_{ρ'}` induced by an intertwiner** `A` of `ρ` and
`ρ'`: on each level, the image under `e` of multiplication by `A` modulo `ℓ ^ (n + 1)`. -/
public def representationLAdicSheafMap (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) :
    representationLAdicSheaf B X x e ρ hρ ⟶ representationLAdicSheaf B X x e ρ' hρ' where
  app n := representationLevelMap B X x e hρ hρ' A hA (n + 1)
  naturality n := by
    ext U y
    have h := congrArg (fun g => (g.hom.hom.app U).hom y)
      ((e.inverse.map_comp _ _).symm.trans ((congrArg e.inverse.map
        (levelAbelianReduction_comp_levelAbelianMap hρ hρ' A hA (n + 1))).trans
          (e.inverse.map_comp _ _)))
    exact h.symm

/-- The level components of the induced morphism, on sections. -/
public theorem representationLAdicSheafMap_app_apply (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (n : ℕ) (U)
    (y : (representationLevelSheaf B X x e ρ hρ (n + 1)).obj.obj U) :
    ((((representationLAdicSheafMap B X x e hρ hρ' A hA).app n).hom.app U).hom y) =
      ((e.inverse.map (levelAbelianMap hρ hρ' A hA (n + 1))).hom.hom.app U).hom y :=
  rfl

public theorem representationLAdicSheafMap_one :
    representationLAdicSheafMap B X x e hρ hρ 1 (fun g => by rw [one_mul, mul_one]) =
      𝟙 (representationLAdicSheaf B X x e ρ hρ) := by
  refine AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext B X ℓ fun n => ?_
  ext U y
  have h := congrArg (fun g => (g.hom.hom.app U).hom y)
    ((congrArg e.inverse.map (levelAbelianMap_one hρ (n + 1))).trans (e.inverse.map_id _))
  exact h

public theorem representationLAdicSheafMap_mul (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (A' : Matrix (Fin r'') (Fin r') ℤ_[ℓ])
    (hA' : ∀ g, A' * (ρ' g).val = (ρ'' g).val * A') :
    representationLAdicSheafMap B X x e hρ hρ'' (A' * A)
      (fun g => by rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hA', Matrix.mul_assoc]) =
      representationLAdicSheafMap B X x e hρ hρ' A hA ≫
        representationLAdicSheafMap B X x e hρ' hρ'' A' hA' := by
  refine AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext B X ℓ fun n => ?_
  ext U y
  have h := congrArg (fun g => (g.hom.hom.app U).hom y)
    ((congrArg e.inverse.map (levelAbelianMap_mul hρ hρ' hρ'' A hA A' hA' (n + 1))).trans
      (e.inverse.map_comp _ _))
  exact h

public theorem representationLAdicSheafMap_add (A B' : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hB : ∀ g, B' * (ρ g).val = (ρ' g).val * B') :
    representationLAdicSheafMap B X x e hρ hρ' (A + B')
      (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hA, hB]) =
      representationLAdicSheafMap B X x e hρ hρ' A hA +
        representationLAdicSheafMap B X x e hρ hρ' B' hB := by
  refine AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext B X ℓ fun n => ?_
  ext U y
  have h := congrArg (fun g => (g.hom.hom.app U).hom y)
    ((congrArg e.inverse.map (levelAbelianMap_add hρ hρ' A B' hA hB (n + 1))).trans
      (e.inverse.map_add))
  exact h

end Sheaves

end Stacks.EtaleCohomology
