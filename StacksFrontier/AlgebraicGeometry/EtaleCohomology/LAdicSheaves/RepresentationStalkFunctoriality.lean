module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFunctoriality

/-!
# The morphism `ℱ_ρ → ℱ_{ρ'}` of an intertwiner on stalks

Under the trivialisation `representationLevelTrivialization` of the stalks of `ℱ_ρ` along a path,
the morphism `representationLAdicSheafMap A` induced by an intertwiner `A` acts on stalks as
multiplication by `A`: `ℤ_ℓ^r → ℤ_ℓ^{r'}`.

## Main results

* `Stacks.EtaleCohomology.representationLevelStalkIso_map`: at each finite level.
* `Stacks.EtaleCohomology.representationLevelTrivialization_stalkEquiv_stalkMap`: on the ℓ-adic
  stalks.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

section ModuleStalk

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (R : Type) [Ring R]

/-- `etaleStalkForget₂Iso` is natural in the sheaf of modules. -/
public theorem etaleStalkForget₂Iso_hom_naturality
    {M N : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} R)} (φ : M ⟶ N) :
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
        (colim.map (Functor.whiskerLeft
          ((Functor.Elements.π (geometricPointFiber B S hS s)).op) φ.hom)) ≫
        (etaleStalkForget₂Iso B S hS s R N).hom =
      (etaleStalkForget₂Iso B S hS s R M).hom ≫
        (abelianEtaleStalkFunctor.{u, u + 1} B S hS s).map
          ((sheafCompose (SmallEtale.topology B S hS)
            (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map φ) := by
  let π := (Functor.Elements.π (geometricPointFiber B S hS s)).op
  let f := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let D := π ⋙ M.obj
  let D' := π ⋙ N.obj
  refine (isColimitOfPreserves f (colimit.isColimit D)).hom_ext fun j => ?_
  change f.map (colimit.ι D j) ≫ _ = f.map (colimit.ι D j) ≫ _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((f.map_comp _ _).symm.trans ((congrArg f.map
    (colimit.ι_map (Functor.whiskerLeft π φ.hom) j)).trans (f.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (_ ≫ ·) (ι_preservesColimitIso_hom f D' j)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) (ι_preservesColimitIso_hom f D j)).symm
  exact (colimit.ι_map (Functor.whiskerLeft π
    ((sheafCompose (SmallEtale.topology B S hS) f).map φ).hom) j).symm

end ModuleStalk

section Levels

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')

/-- The morphism of level sheaves on underlying abelian sheaves is the image of the map of level
modules under the inverse of `canonicalFiniteLocallyConstantAbelianSheafEquivalence`. -/
public theorem forget₂_representationLevelMap (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map
      (representationLevelMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA k) =
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
        (levelAbelianMap hρ hρ' A hA k)).hom :=
  rfl

/-- **The morphism of level sheaves induced by an intertwiner `A` acts on stalks by `A`**, under
`representationLevelStalkIso`, as a commutative square of abelian groups. -/
public theorem representationLevelStalkIso_hom_naturality {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
        (colim.map (Functor.whiskerLeft
          ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op)
          (representationLevelMap B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA k).hom)) ≫
        (representationLevelStalkIso B X x ρ' hρ' t k).hom =
      (representationLevelStalkIso B X x ρ hρ t k).hom ≫
        (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map
          (levelAbelianMap hρ hρ' A hA k) := by
  have h1 := etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s (ZMod (ℓ ^ k))
      (representationLevelMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA k)
  rw [forget₂_representationLevelMap] at h1
  have h2 := (finiteLocallyConstantAbelianStalkIso B X t).hom.naturality
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
      (levelAbelianMap hρ hρ' A hA k))
  have h3 := (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.naturality
    (levelAbelianMap hρ hρ' A hA k)
  have h3' := congrArg (fun g => (ObjectProperty.ι _ ⋙
    ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).map g) h3
  simp only [Functor.map_comp] at h3'
  simp only [representationLevelStalkIso, Iso.trans_hom]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h3'))))).trans ?_
  simp only [Functor.id_map]
  rfl

/-- **The morphism of level sheaves induced by an intertwiner `A` acts on stalks by `A`**, on
elements. -/
public theorem representationLevelStalkIso_map {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ)
    (y : (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (representationLevelSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k).obj)) :
    ((representationLevelStalkIso B X x ρ' hρ' t k).hom
        ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
          (colim.map (Functor.whiskerLeft
            ((Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op)
            (representationLevelMap B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA k).hom))
          y)).down =
      (A.map (PadicInt.toZModPow k)) *ᵥ ((representationLevelStalkIso B X x ρ hρ t k).hom y).down :=
  (congrArg ULift.down (ConcreteCategory.congr_hom
    (representationLevelStalkIso_hom_naturality B X x hρ hρ' t A hA k) y)).trans
    (levelAbelianMap_apply hρ hρ' A hA k _)

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
/-- The morphism `ℱ_ρ → ℱ_{ρ'}` of an intertwiner `A` acts on the level trivialisations of the
stalks by `A`. -/
public theorem representationLevelTrivialization_finiteLevelStalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (n : ℕ)
    (y : finiteLevelStalk B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s n) :
    (representationLevelTrivialization B X x ρ' hρ' t).equiv n
        ((finiteLevelStalkMap (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA) s n).hom y) =
      (A.map (PadicInt.toZModPow (n + 1))) *ᵥ
        (representationLevelTrivialization B X x ρ hρ t).equiv n y :=
  representationLevelStalkIso_map B X x hρ hρ' t A hA (n + 1) y

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The morphism `ℱ_ρ → ℱ_{ρ'}` of an intertwiner `A` is multiplication by `A`** on the ℓ-adic
stalks `ℤ_ℓ^r → ℤ_ℓ^{r'}` trivialised along a path `t`. -/
public theorem representationLevelTrivialization_stalkEquiv_stalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A)
    (v : LAdicSheaf.stalk B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s) :
    (representationLevelTrivialization B X x ρ' hρ' t).stalkEquiv
        (LAdicSheaf.stalkMap (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA) s v) =
      A *ᵥ (representationLevelTrivialization B X x ρ hρ t).stalkEquiv v := by
  funext i
  apply eq_of_toZModPow_succ_eq
  intro n
  rw [LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]
  change (representationLevelTrivialization B X x ρ' hρ' t).equiv n
    ((finiteLevelStalkMap _ s n).hom (v.1 n)) i = _
  rw [representationLevelTrivialization_finiteLevelStalkMap, RingHom.map_mulVec]
  congr 2
  funext j
  rw [Function.comp_apply, LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]

/-- **An endomorphism `a` of the geometric point acts on the trivialised stalk of `ℱ_ρ` by
`ρ(g)`**, `g` the transport along `t` of the automorphism `σ` of the fibre functor given by
precomposition with `a`. -/
public theorem representationLevelTrivialization_stalkEquiv_stalkEnd {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a)
    (v : LAdicSheaf.stalk B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s) :
    (representationLevelTrivialization B X x ρ hρ t).stalkEquiv (LAdicSheaf.stalkEnd B X ℓ _ a v) =
      (ρ (etaleFundamentalGroupMulEquiv t σ)).val *ᵥ
        (representationLevelTrivialization B X x ρ hρ t).stalkEquiv v := by
  set T := representationLevelTrivialization B X x ρ hρ t
  funext i
  apply eq_of_toZModPow_succ_eq
  intro n
  rw [LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]
  change T.equiv n ((finiteLevelStalkEnd B X ℓ _ a n).hom (v.1 n)) i = _
  have hl := congrArg ULift.down (ULift.ext
    (representationLevelStalkIso_geometricPointStalkMap B X x ρ hρ t a σ hσ (n + 1) (v.1 n)))
  change T.equiv n ((finiteLevelStalkEnd B X ℓ _ a n).hom (v.1 n)) =
    levelRepresentation _ (n + 1) _ (T.equiv n (v.1 n)) at hl
  rw [hl, levelRepresentation_apply, RingHom.map_mulVec]
  congr 2
  funext j
  exact (LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv T v n j).symm

end LAdic

end Stacks.EtaleCohomology
