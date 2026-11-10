module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality

/-!
# Every morphism `ℱ_ρ → ℱ_{ρ'}` acts on stalks by an intertwiner

Let `X` be connected with a geometric point `x̄`, and let `ρ`, `ρ'` be continuous representations
of `π₁(X, x̄)` on `ℤ_ℓ^r` and `ℤ_ℓ^{r'}`. An intertwiner `A` gives a morphism `ℱ_ρ → ℱ_{ρ'}` that
acts on stalks by `A`
(`Stacks.EtaleCohomology.representationLevelTrivialization_stalkEquiv_stalkMap`). This file goes
the other way. **Any** morphism `Φ : ℱ_ρ → ℱ_{ρ'}` of ℓ-adic sheaves acts on the stalks at a
geometric point `s̄`, trivialised along a path to `x̄`, by an integral matrix `A`, and `A`
intertwines `ρ` and `ρ'`.

The level-`k` component of `Φ` is a morphism of finite locally constant abelian sheaves. The
equivalence of Tag 0DV5 (2) carries it to a morphism of the finite `π₁(X, x̄)`-modules
`(ℤ/ℓ^kℤ)^r → (ℤ/ℓ^kℤ)^{r'}`, which is `π₁`-equivariant
(`Stacks.EtaleCohomology.representationLevelHomModuleMap`). Under the comparison of stalks with
fibres it is the map of stalks of `Φ`. The matrix of the map of ℓ-adic stalks therefore reduces
modulo every `ℓ^k` to an equivariant map, so it intertwines `ρ` and `ρ'`.

## Main definitions

* `Stacks.EtaleCohomology.representationLevelHomModuleMap`: the morphism of level modules attached
  to a morphism of level sheaves.

## Main results

* `Stacks.EtaleCohomology.representationLevelStalkIso_hom_naturality_of_hom`: it is the map of
  stalks.
* `Stacks.EtaleCohomology.exists_intertwiner_stalkEquiv_stalkMap`: a morphism `ℱ_ρ → ℱ_{ρ'}` acts
  on trivialised stalks by an integral intertwiner.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

section Equivalence

variable {C D : Type*} [Category C] [Category D]

/-- Conjugating the image of a morphism `f : e⁻¹ A ⟶ e⁻¹ B` under `e` by the counit and applying
`e⁻¹` gives back `f`. -/
public theorem Equivalence.inverse_map_counitIso_conj (e : C ≌ D) {A B : D}
    (f : e.inverse.obj A ⟶ e.inverse.obj B) :
    e.inverse.map (e.counitIso.inv.app A ≫ e.functor.map f ≫ e.counitIso.hom.app B) = f := by
  apply e.functor.map_injective
  rw [Equivalence.fun_inv_map]
  simp

end Equivalence

section Levels

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

section Generic

variable (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]

/-- The morphism of finite locally constant abelian sheaves underlying a morphism of level sheaves
of `ℱ_ρ` and `ℱ_{ρ'}`. -/
public def representationLevelHomAbelian (k : ℕ)
    (φ : representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k) :
    e.inverse.obj (levelAbelian ρ hρ k) ⟶ e.inverse.obj (levelAbelian ρ' hρ' k) :=
  ObjectProperty.homMk ((sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map φ)

/-- **The morphism of level modules attached to a morphism of level sheaves**: the image of the
underlying morphism of finite locally constant abelian sheaves under the equivalence `e` of
Tag 0DV5 (2), read on the level modules through the counit. -/
@[irreducible]
public def representationLevelHomModuleMap (k : ℕ)
    (φ : representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k) :
    levelAbelian ρ hρ k ⟶ levelAbelian ρ' hρ' k :=
  e.counitIso.inv.app (levelAbelian ρ hρ k) ≫
    e.functor.map (representationLevelHomAbelian B X x hρ hρ' e k φ) ≫
    e.counitIso.hom.app (levelAbelian ρ' hρ' k)

/-- The defining property of `representationLevelHomModuleMap`. -/
public theorem functor_map_representationLevelHomAbelian_comp_counit (k : ℕ)
    (φ : representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k) :
    e.functor.map (representationLevelHomAbelian B X x hρ hρ' e k φ) ≫
        e.counitIso.hom.app (levelAbelian ρ' hρ' k) =
      e.counitIso.hom.app (levelAbelian ρ hρ k) ≫
        representationLevelHomModuleMap B X x hρ hρ' e k φ := by
  rw [representationLevelHomModuleMap]
  exact (e.counitIso.hom_inv_id_app_assoc _ _).symm

/-- The morphism of level modules attached to a morphism of level sheaves, as an additive map
`(ℤ/ℓ^kℤ)^r → (ℤ/ℓ^kℤ)^{r'}`. -/
public def representationLevelHomVec (k : ℕ)
    (φ : representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k) :
    (Fin r → ZMod (ℓ ^ k)) →+ (Fin r' → ZMod (ℓ ^ k)) :=
  AddEquiv.ulift.toAddMonoidHom.comp
    (((representationLevelHomModuleMap B X x hρ hρ' e k φ).hom.hom.hom.hom.hom :
        ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) →+ ULift.{u + 1} (Fin r' → ZMod (ℓ ^ k))).comp
      AddEquiv.ulift.symm.toAddMonoidHom)

/-- **The morphism of level modules attached to a morphism of level sheaves is equivariant**:
it commutes with the level representations of `ρ` and `ρ'`. -/
public theorem representationLevelHomVec_levelRepresentation (k : ℕ)
    (φ : representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k)
    (g : EtaleFundamentalGroup X.1 x) (w : Fin r → ZMod (ℓ ^ k)) :
    representationLevelHomVec B X x hρ hρ' e k φ (levelRepresentation ρ k g w) =
      levelRepresentation ρ' k g (representationLevelHomVec B X x hρ hρ' e k φ w) :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    ((representationLevelHomModuleMap B X x hρ hρ' e k φ).hom.hom.hom.comm g) (ULift.up w))


/-- The equivalence carries the attached morphism of level modules back to the underlying
morphism of abelian sheaves. -/
public theorem inverse_map_representationLevelHomModuleMap (k : ℕ)
    (φ : representationLevelSheaf B X x e ρ hρ k ⟶ representationLevelSheaf B X x e ρ' hρ' k) :
    e.inverse.map (representationLevelHomModuleMap B X x hρ hρ' e k φ) =
      representationLevelHomAbelian B X x hρ hρ' e k φ := by
  rw [representationLevelHomModuleMap]
  exact Stacks.EtaleCohomology.Equivalence.inverse_map_counitIso_conj e
    (representationLevelHomAbelian B X x hρ hρ' e k φ)

end Generic

/-- The morphism of level sheaves on underlying abelian sheaves is the image under the
equivalence of the attached morphism of level modules. -/
public theorem forget₂_map_eq_inverse_map_representationLevelHomModuleMap (k : ℕ)
    (φ : representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k ⟶
      representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ' k) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map φ =
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
        (representationLevelHomModuleMap B X x hρ hρ'
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) k φ)).hom :=
  (congrArg (fun f => f.hom)
    (inverse_map_representationLevelHomModuleMap B X x hρ hρ' _ k φ)).symm

/-- `representationLevelStalkIso` as the composite of its three constituents. -/
public theorem representationLevelStalkIso_hom_eq {r₀ : ℕ}
    {ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r₀) ℤ_[ℓ]} (hρ₀ : Continuous ρ₀)
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ) :
    (representationLevelStalkIso B X x ρ₀ hρ₀ t k).hom =
      (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀ k)).hom ≫
        (finiteLocallyConstantAbelianStalkIso B X t).hom.app
          ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
            (levelAbelian ρ₀ hρ₀ k)) ≫
        (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map
          ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.app
            (levelAbelian ρ₀ hρ₀ k)) :=
  rfl

/-- **A morphism of level sheaves of `ℱ_ρ` and `ℱ_{ρ'}` acts on stalks by the attached
morphism of level modules**, under `representationLevelStalkIso`, as a commutative square. -/
public theorem representationLevelStalkIso_hom_naturality_of_hom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ)
    (φ : representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k ⟶
      representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ' k) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
        (colim.map (Functor.whiskerLeft
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op) φ.hom)) ≫
        (representationLevelStalkIso B X x ρ' hρ' t k).hom =
      (representationLevelStalkIso B X x ρ hρ t k).hom ≫
        (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map
          (representationLevelHomModuleMap B X x hρ hρ'
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) k φ) := by
  have h1 := etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s (ZMod (ℓ ^ k)) φ
  rw [forget₂_map_eq_inverse_map_representationLevelHomModuleMap] at h1
  have h2 := (finiteLocallyConstantAbelianStalkIso B X t).hom.naturality
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
      (representationLevelHomModuleMap B X x hρ hρ'
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) k φ))
  have h3 := (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.naturality
    (representationLevelHomModuleMap B X x hρ hρ'
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) k φ)
  have h3' := congrArg (fun g => (ObjectProperty.ι _ ⋙
    ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map g) h3
  simp only [Functor.map_comp] at h3'
  rw [representationLevelStalkIso_hom_eq, representationLevelStalkIso_hom_eq]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h3'))))).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

/-- **A morphism of level sheaves of `ℱ_ρ` and `ℱ_{ρ'}` acts on stalks by the attached map of
level modules**, on elements. -/
public theorem representationLevelStalkIso_hom_map_of_hom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ)
    (φ : representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k ⟶
      representationLevelSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ' k)
    (y : (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj)) :
    ((representationLevelStalkIso B X x ρ' hρ' t k).hom
        ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
          (colim.map (Functor.whiskerLeft
            ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op) φ.hom)) y)).down =
      representationLevelHomVec B X x hρ hρ'
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) k φ
        ((representationLevelStalkIso B X x ρ hρ t k).hom y).down :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (representationLevelStalkIso_hom_naturality_of_hom B X x hρ hρ' t k φ) y)

/-- Reducing `ρ g *ᵥ w` modulo `ℓ ^ k` is the level representation applied to `w` reduced. -/
private theorem toZModPow_mulVec_eq_levelRepresentation {r : ℕ}
    {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (k : ℕ)
    (g : EtaleFundamentalGroup X.1 x) (w : Fin r → ℤ_[ℓ]) :
    (fun i => PadicInt.toZModPow k (((ρ g).val *ᵥ w) i)) =
      levelRepresentation ρ k g (fun i => PadicInt.toZModPow k (w i)) := by
  rw [levelRepresentation_apply]
  funext j
  exact RingHom.map_mulVec (PadicInt.toZModPow k) (ρ g).val w j

end Levels

section LAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- A morphism `ℱ_ρ → ℱ_{ρ'}` acts on the level trivialisations of the stalks by the attached
equivariant map of level modules. -/
public theorem representationLevelTrivialization_finiteLevelStalkMap_of_hom
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (Φ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ') (n : ℕ)
    (y : finiteLevelStalk B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s n) :
    (representationLevelTrivialization B X x ρ' hρ' t).equiv n
        ((finiteLevelStalkMap Φ s n).hom y) =
      representationLevelHomVec B X x hρ hρ'
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (Φ.app n)
        ((representationLevelTrivialization B X x ρ hρ t).equiv n y) :=
  representationLevelStalkIso_hom_map_of_hom B X x hρ hρ' t (n + 1) (Φ.app n) y

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **Every morphism `ℱ_ρ → ℱ_{ρ'}` acts on stalks by an integral intertwiner**: on the ℓ-adic
stalks at `s̄`, trivialised along a path `t` from `s̄` to `x̄`, it is multiplication by a matrix
`A` with `A ρ(g) = ρ'(g) A` for every `g ∈ π₁(X, x̄)`. -/
public theorem exists_intertwiner_stalkEquiv_stalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (Φ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ') :
    ∃ A : Matrix (Fin r') (Fin r) ℤ_[ℓ], (∀ g, A * (ρ g).val = (ρ' g).val * A) ∧
      ∀ v, (representationLevelTrivialization B X x ρ' hρ' t).stalkEquiv
          (LAdicSheaf.stalkMap Φ s v) =
        A *ᵥ (representationLevelTrivialization B X x ρ hρ t).stalkEquiv v := by
  classical
  set T := representationLevelTrivialization B X x ρ hρ t
  set T' := representationLevelTrivialization B X x ρ' hρ' t
  let L : (Fin r → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] (Fin r' → ℤ_[ℓ]) :=
    T'.stalkEquiv.toLinearMap ∘ₗ LAdicSheaf.stalkMap Φ s ∘ₗ T.stalkEquiv.symm.toLinearMap
  have hL : ∀ w, (LinearMap.toMatrix' L) *ᵥ w = L w := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  -- the level maps
  have hlev : ∀ (w : Fin r → ℤ_[ℓ]) (n : ℕ),
      (fun i => PadicInt.toZModPow (n + 1) (L w i)) =
        representationLevelHomVec B X x hρ hρ'
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (Φ.app n)
          (fun i => PadicInt.toZModPow (n + 1) (w i)) := fun w n => by
    have hw :
        T.equiv n ((T.stalkEquiv.symm w).1 n) = fun i => PadicInt.toZModPow (n + 1) (w i) := by
      funext i
      rw [← LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv, LinearEquiv.apply_symm_apply]
    funext i
    change PadicInt.toZModPow (n + 1) (T'.stalkEquiv (LAdicSheaf.stalkMap Φ s
      (T.stalkEquiv.symm w)) i) = _
    rw [LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]
    change T'.equiv n ((finiteLevelStalkMap Φ s n).hom ((T.stalkEquiv.symm w).1 n)) i = _
    rw [representationLevelTrivialization_finiteLevelStalkMap_of_hom, hw]
  refine ⟨LinearMap.toMatrix' L, fun g => ?_, fun v => ?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hL, hL]
    funext i
    apply eq_of_toZModPow_succ_eq
    intro n
    rw [congrFun (hlev ((ρ g).val *ᵥ w) n) i]
    rw [toZModPow_mulVec_eq_levelRepresentation B X x,
      representationLevelHomVec_levelRepresentation B X x hρ hρ' _ (n + 1) (Φ.app n), ← hlev,
      ← toZModPow_mulVec_eq_levelRepresentation B X x]
  · rw [hL]
    change T'.stalkEquiv (LAdicSheaf.stalkMap Φ s v) =
      T'.stalkEquiv (LAdicSheaf.stalkMap Φ s (T.stalkEquiv.symm (T.stalkEquiv v)))
    rw [LinearEquiv.symm_apply_apply]

end LAdic

end Stacks.EtaleCohomology

end
