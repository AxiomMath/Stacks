module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BasePointChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality

/-!
# The sheaf `ℱ_ρ` at two base points

Let `e`, `e'` be equivalences of the finite locally constant abelian sheaves on `X_étale` with the
finite continuous modules of two groups `G`, `G'`, and `φ : G' →ₜ* G` with
`β : res_φ ⋙ e'⁻¹ ≅ e⁻¹`. Then for a continuous `τ : G → GL_r(ℤ_ℓ)` the components of `β` at the
level modules give morphisms `ℱ_τ → ℱ_{τ ∘ φ}` and back, inverse to each other and natural in
intertwiners (`Stacks.EtaleCohomology.representationLAdicSheafResIso`).

For the canonical equivalences of Tag 0DV5 (2) at two geometric points `x̄`, `x̄'` of a connected
`X` and an isomorphism `t : F_x̄ ≅ F_x̄'` of fibre functors, `β` is the conjugate of
`Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso`: so `ℱ_τ` built
at `x̄` is `ℱ_{τ ∘ φ_t}` built at `x̄'`
(`Stacks.EtaleCohomology.representationLAdicSheafBasePointIso`), the base-point change of the
sheaves of the notation preceding [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `representationLAdicSheafResIso`.
* `canonicalFiniteLocallyConstantAbelianSheafEquivalenceBasePointInverseIso`.
* `representationLAdicSheafBasePointIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.ConstantSheaf
open scoped Stacks.DiscreteModuleTopology

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}

section Res

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]
  (e' : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x')).FullSubcategory)
  [e'.functor.Additive]
  (φ : EtaleFundamentalGroup X.1 x' →ₜ* EtaleFundamentalGroup X.1 x)
  (β : ContinuousGAddCommGrp.resIsFinite φ ⋙ e'.inverse ≅ e.inverse)
  {τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hτ : Continuous τ)

include β

/-- The components of `β⁻¹` at the level modules, as a morphism of abelian sheaves with scalar
operations. -/
public def representationLevelScalarsResHom (k : ℕ) :
    representationLevelScalars B X x e τ hτ k ⟶
      representationLevelScalars B X x' e' (τ.comp φ.toMonoidHom) (hτ.comp φ.continuous) k :=
  ObjectProperty.homMk
    { app := fun _ => (β.inv.app (levelAbelian τ hτ k)).hom
      naturality := fun _ _ a => congrArg (fun g => g.hom) (β.inv.naturality
        ((Stacks.GroupCohomology.finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _
          (levelModule.{u + 1, u + 1} τ hτ k)).map a)) }

/-- The components of `β` at the level modules, as a morphism of abelian sheaves with scalar
operations. -/
public def representationLevelScalarsResInv (k : ℕ) :
    representationLevelScalars B X x' e' (τ.comp φ.toMonoidHom) (hτ.comp φ.continuous) k ⟶
      representationLevelScalars B X x e τ hτ k :=
  ObjectProperty.homMk
    { app := fun _ => (β.hom.app (levelAbelian τ hτ k)).hom
      naturality := fun _ _ a => congrArg (fun g => g.hom) (β.hom.naturality
        ((Stacks.GroupCohomology.finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _
          (levelModule.{u + 1, u + 1} τ hτ k)).map a)) }

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **`ℱ_τ → ℱ_{τ ∘ φ}`**, levelwise the components of `β⁻¹`. -/
public def representationLAdicSheafResHom :
    representationLAdicSheaf B X x e τ hτ ⟶
      representationLAdicSheaf B X x' e' (τ.comp φ.toMonoidHom) (hτ.comp φ.continuous) where
  app n := (scalarActionToModuleSheaf (SmallEtale.topology B X.1 X.2) (ZMod (ℓ ^ (n + 1)))).map
    (representationLevelScalarsResHom B X e e' φ β hτ (n + 1))
  naturality n := by
    ext U y
    exact (congrArg (fun g => (g.hom.hom.app U).hom y)
      (β.inv.naturality (levelAbelianReduction τ hτ (n + 1)))).symm

/-- **`ℱ_{τ ∘ φ} → ℱ_τ`**, levelwise the components of `β`. -/
public def representationLAdicSheafResInv :
    representationLAdicSheaf B X x' e' (τ.comp φ.toMonoidHom) (hτ.comp φ.continuous) ⟶
      representationLAdicSheaf B X x e τ hτ where
  app n := (scalarActionToModuleSheaf (SmallEtale.topology B X.1 X.2) (ZMod (ℓ ^ (n + 1)))).map
    (representationLevelScalarsResInv B X e e' φ β hτ (n + 1))
  naturality n := by
    ext U y
    exact (congrArg (fun g => (g.hom.hom.app U).hom y)
      (β.hom.naturality (levelAbelianReduction τ hτ (n + 1)))).symm

/-- **`ℱ_τ ≅ ℱ_{τ ∘ φ}`** for `β : res_φ ⋙ e'⁻¹ ≅ e⁻¹`. -/
public def representationLAdicSheafResIso :
    representationLAdicSheaf B X x e τ hτ ≅
      representationLAdicSheaf B X x' e' (τ.comp φ.toMonoidHom) (hτ.comp φ.continuous) where
  hom := representationLAdicSheafResHom B X e e' φ β hτ
  inv := representationLAdicSheafResInv B X e e' φ β hτ
  hom_inv_id := by
    refine AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext.{u, u + 1} B X ℓ fun n => ?_
    ext U y
    exact congrArg (fun g => (g.hom.hom.app U).hom y) (β.inv_hom_id_app (levelAbelian τ hτ (n + 1)))
  inv_hom_id := by
    refine AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext.{u, u + 1} B X ℓ fun n => ?_
    ext U y
    exact congrArg (fun g => (g.hom.hom.app U).hom y) (β.hom_inv_id_app (levelAbelian τ hτ (n + 1)))

/-- **The isomorphism `ℱ_τ ≅ ℱ_{τ ∘ φ}` is natural in intertwiners**: it commutes with the
morphisms induced by `A τ₁(g) = τ₂(g) A`. -/
public theorem representationLAdicSheafResIso_hom_naturality
    {τ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hτ' : Continuous τ')
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (τ g).val = (τ' g).val * A) :
    (representationLAdicSheafResIso B X e e' φ β hτ).hom ≫
        representationLAdicSheafMap B X x' e' (hτ.comp φ.continuous) (hτ'.comp φ.continuous) A
          (fun g => hA (φ g)) =
      representationLAdicSheafMap B X x e hτ hτ' A hA ≫
        (representationLAdicSheafResIso B X e e' φ β hτ').hom := by
  refine AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext.{u, u + 1} B X ℓ fun n => ?_
  ext U y
  exact congrArg (fun g => (g.hom.hom.app U).hom y)
    (β.inv.naturality (levelAbelianMap hτ hτ' A hA (n + 1))).symm

end Res

section BasePoint

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {x x' : GeometricPoint X.1}

/-- **Tag 0DV5 (2) at two base points, on the inverse functors**:
`res_{φ_t} ⋙ E_{x̄'}⁻¹ ≅ E_{x̄}⁻¹`, the conjugate of
`Stacks.EtaleCohomology.finiteLocallyConstantAbelianSheafEquivalenceBasePointIso`. -/
public def canonicalFiniteLocallyConstantAbelianSheafEquivalenceBasePointInverseIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x') :
    ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupBasePointHom t) ⋙
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x').inverse ≅
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse :=
  let EX := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let EY := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x'
  let α : EX.functor ⋙ ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupBasePointHom t) ≅
      𝟭 _ ⋙ EY.functor := finiteLocallyConstantAbelianSheafEquivalenceBasePointIso B X t
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight EX.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EX.inverse
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α EY.inverse ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (𝟭 _) EY.unitIso.symm ≪≫
        Functor.leftUnitor _) ≪≫ Functor.rightUnitor _

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **`ℱ_τ` at `x̄` is `ℱ_{τ ∘ φ_t}` at `x̄'`** for an isomorphism `t : F_x̄ ≅ F_x̄'` of geometric
fibre functors, as ℓ-adic sheaves; it is natural in intertwiners
(`Stacks.EtaleCohomology.representationLAdicSheafResIso_hom_naturality`). -/
public def representationLAdicSheafBasePointIso
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x')
    {τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hτ : Continuous τ) :
    representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        τ hτ ≅
      representationLAdicSheaf B X x' (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x')
        (τ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)
        (hτ.comp (etaleFundamentalGroupBasePointHom t).continuous) :=
  representationLAdicSheafResIso B X _ _ (etaleFundamentalGroupBasePointHom t)
    (canonicalFiniteLocallyConstantAbelianSheafEquivalenceBasePointInverseIso B X t) hτ

end BasePoint

end Stacks.EtaleCohomology

end
