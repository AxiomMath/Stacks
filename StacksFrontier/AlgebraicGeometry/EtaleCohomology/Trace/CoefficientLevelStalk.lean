module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatOfFlatStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.Modules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible

/-!
# The stalks of the levels of the `O`-sheaf of a representation over `ℤ/ℓᵏ ⊗ O`

The `k`-th level of the `O`-sheaf `ℱ_σ` of a representation `σ : π₁(X, x̄) → GL_m(O)` is a sheaf
of modules over the finite ring `Λ'_k = ℤ/ℓᵏ ⊗ O`. Its stalk at a geometric point `s̄` is, along
a path from `s̄` to `x̄`, the level module `(ℤ/ℓᵏ)^{md}` with `Λ'_k` acting through
`Stacks.EtaleCohomology.coeffLevelMatrix`, which is free of rank `m` over `Λ'_k`. Hence the level
is a constructible flat sheaf of `Λ'_k`-modules: it is finite locally constant because its
underlying abelian sheaf is.

## Main definitions

* `Stacks.EtaleCohomology.coeffLevelStacksSheaf`: the `k`-th level as a sheaf of `Λ'_k`-modules
  on the small étale site of Stacks 021B.
* `Stacks.EtaleCohomology.coeffLevelStalkIso`: its stalk is `(ℤ/ℓᵏ)^{md}`.

## Main results

* `Stacks.EtaleCohomology.coeffLevelStalkIso_smul`: the identification is linear over `Λ'_k`.
* `Stacks.EtaleCohomology.isConstructibleFlatEtaleModule_coeffLevelEtaleSheaf`: the `n`-th
  level on Mathlib's small étale site is constructible flat over `Λ'_{n+1}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

open scoped Matrix

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-! ### Scalars on colimits of modules -/

section Colim

variable {R : Type} [CommRing R] {J : Type*} [Category J] (F : J ⥤ ModuleCat.{u + 1} R)
  [HasColimit F]

/-- Multiplication by `c` on the values of a functor to modules, as a natural endomorphism. -/
public def smulNatEnd (c : R) : F ⟶ F where
  app j := ModuleCat.ofHom (c • LinearMap.id)
  naturality _ _ f := by
    ext y
    exact ((F.map f).hom.map_smul c y).symm

/-- **On a colimit of modules, the map induced by multiplication by `c` is multiplication by
`c`.** -/
public theorem colimMap_smulNatEnd_apply (c : R) (v : (colimit F : ModuleCat.{u + 1} R)) :
    (colimMap (smulNatEnd F c)).hom v = c • v := by
  have h : colimMap (smulNatEnd F c) = ModuleCat.ofHom (c • LinearMap.id) := by
    refine colimit.hom_ext fun j => ?_
    rw [ι_colimMap]
    ext y
    exact (colimit.ι F j).hom.map_smul c y
  rw [h]
  rfl

end Colim

/-- A module carried bijectively and linearly onto a flat module is flat. -/
public theorem flat_of_bijective_smul {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [Module.Flat R W] (f : V → W)
    (hadd : ∀ v w, f (v + w) = f v + f w) (hsmul : ∀ (c : R) v, f (c • v) = c • f v)
    (hf : Function.Bijective f) : Module.Flat R V :=
  Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective { toFun := f, map_add' := hadd, map_smul' := hsmul } hf)

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ}
  (b : Module.Basis (Fin d) ℤ_[ℓ] O) {m : ℕ}

section Stalks

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

/-- The action of `Λ'_k` on the abelian sheaf underlying the `k`-th level of `ℱ_ρ`, on the small
étale site of Stacks 021B. -/
public def coeffLevelStacksRingHom (k : ℕ) :
    coeffLevelRing ℓ O k →+* End ((sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).obj
        (representationLevelSheaf B X x e₀
          ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k)) :=
  (Stacks.ModuleCatLift.mapEndRingHom (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})) _).comp
    (coeffLevelSheafRingHom b B X x e₀ σ hρ k)

/-- **The `k`-th level of `ℱ_ρ` as a sheaf of `Λ'_k`-modules** on the small étale site of
Stacks 021B. -/
public def coeffLevelStacksSheaf (k : ℕ) :
    Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) :=
  Stacks.ModuleCatLift.sheafOfEndAction (coeffLevelRing ℓ O k) (SmallEtale.topology B X.1 X.2)
    _ (coeffLevelStacksRingHom b B X x σ hρ k)

/-- Multiplication by `c` on the `Λ'_k`-sheaf, as an endomorphism of sheaves of modules. -/
public def coeffLevelStacksSMul (k : ℕ) (c : coeffLevelRing ℓ O k) :
    coeffLevelStacksSheaf b B X x σ hρ k ⟶ coeffLevelStacksSheaf b B X x σ hρ k :=
  ObjectProperty.homMk (smulNatEnd _ c)

/-- On underlying abelian sheaves, multiplication by `c` is the action of `c`. -/
public theorem forget₂_coeffLevelStacksSMul (k : ℕ) (c : coeffLevelRing ℓ O k) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) AddCommGrpCat.{u + 1})).map
      (coeffLevelStacksSMul b B X x σ hρ k c) =
      (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map
        (coeffLevelSheafMap b B X x e₀ σ hρ k c) := by
  ext U y
  show c • (show (coeffLevelStacksSheaf b B X x σ hρ k).obj.obj U from y) = _
  exact (ModuleCat.mkOfSMul'_smul _ c _).trans rfl

/-- **The stalk of the `Λ'_k`-sheaf at `s̄` is `(ℤ/ℓᵏ)^{md}`**, as abelian groups, along a path
`t` from `s̄` to `x̄`: through the stalk of the common underlying abelian sheaf. -/
public def coeffLevelStalkIso {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj) ≅
      AddCommGrpCat.of (ULift.{u + 1} (Fin (m * d) → ZMod (ℓ ^ k))) :=
  etaleStalkForget₂Iso B X.1 X.2 s (coeffLevelRing ℓ O k) _ ≪≫
    (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) _).symm ≪≫
      representationLevelStalkIso B X x _ hρ t k

/-- The stalk identification `coeffLevelStalkIso`, as an additive map to `(ℤ/ℓᵏ)^{md}`. -/
private def coeffLevelStalkAddHom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ) :
    (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) →+ (Fin (m * d) → ZMod (ℓ ^ k)) where
  toFun v := ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down
  map_zero' := congrArg ULift.down ((coeffLevelStalkIso b B X x σ hρ t k).hom.hom.map_zero)
  map_add' v w := congrArg ULift.down ((coeffLevelStalkIso b B X x σ hρ t k).hom.hom.map_add v w)

/-- **The identification of the stalk is linear over `Λ'_k` for the elements `1 ⊗ o`.** -/
public theorem coeffLevelStalkIso_smul_of {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ) (o : O)
    (v : (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k))) :
    ((coeffLevelStalkIso b B X x σ hρ t k).hom (coeffLevelRing.of ℓ O k o • v)).down =
      ((coefficientScalarRingHom b m o).map (PadicInt.toZModPow k)) *ᵥ
        ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down := by
  have hA : ∀ g, coefficientScalarRingHom b m o *
      (((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) g).val =
      (((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) g).val *
        coefficientScalarRingHom b m o :=
    fun g => coefficientScalarRingHom_commute b m o (σ g).val
  have hof : coeffLevelSheafMap b B X x e₀ σ hρ k (coeffLevelRing.of ℓ O k o) =
      representationLevelMap B X x e₀ hρ hρ (coefficientScalarRingHom b m o) hA k :=
    coeffLevelSheafMap_of b B X x e₀ σ hρ k o
  have h1 := etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s (coeffLevelRing ℓ O k)
    (coeffLevelStacksSMul b B X x σ hρ k (coeffLevelRing.of ℓ O k o))
  rw [forget₂_coeffLevelStacksSMul, hof] at h1
  have h2 := etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s (ZMod (ℓ ^ k))
    (representationLevelMap B X x e₀ hρ hρ (coefficientScalarRingHom b m o) hA k)
  have hsm : (coeffLevelRing.of ℓ O k o • v :
      (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
        ModuleCat.{u + 1} (coeffLevelRing ℓ O k))) =
      (forget₂ (ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) AddCommGrpCat.{u + 1}).map
        (colim.map (Functor.whiskerLeft
          ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op)
          (coeffLevelStacksSMul b B X x σ hρ k (coeffLevelRing.of ℓ O k o)).hom)) v :=
    (colimMap_smulNatEnd_apply _ _ v).symm
  set Φ₁ := etaleStalkForget₂Iso B X.1 X.2 s (coeffLevelRing ℓ O k)
    (coeffLevelStacksSheaf b B X x σ hρ k) with hΦ₁
  set ΦZ := etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k))
    (representationLevelSheaf B X x e₀
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k) with hΦZ
  set z := ΦZ.inv (Φ₁.hom v) with hz
  have e1 := ConcreteCategory.congr_hom h1 v
  have e2 := ConcreteCategory.congr_hom h2 z
  have e3 : ΦZ.hom z = Φ₁.hom v := Iso.inv_hom_id_apply ΦZ (Φ₁.hom v)
  show ((representationLevelStalkIso B X x _ hρ t k).hom
      (ΦZ.inv (Φ₁.hom (coeffLevelRing.of ℓ O k o • v)))).down = _
  rw [hsm]
  have e4 : ΦZ.inv (Φ₁.hom ((forget₂ (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))
      AddCommGrpCat.{u + 1}).map (colim.map (Functor.whiskerLeft
        ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op)
        (coeffLevelStacksSMul b B X x σ hρ k (coeffLevelRing.of ℓ O k o)).hom)) v)) =
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
        (colim.map (Functor.whiskerLeft
          ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op)
          (representationLevelMap B X x e₀ hρ hρ (coefficientScalarRingHom b m o) hA k).hom))
            z := by
    refine (congrArg ΦZ.inv (e1.trans ?_)).trans (Iso.hom_inv_id_apply ΦZ _)
    exact (congrArg _ e3.symm).trans e2.symm
  rw [e4]
  exact representationLevelStalkIso_map B X x hρ hρ t (coefficientScalarRingHom b m o) hA k z

/-- **The identification of the stalk is linear over `Λ'_k`**: `c` acts through
`coeffLevelMatrix`. -/
public theorem coeffLevelStalkIso_smul {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ)
    (c : coeffLevelRing ℓ O k)
    (v : (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k))) :
    ((coeffLevelStalkIso b B X x σ hρ t k).hom (c • v)).down =
      coeffLevelMatrix ℓ b m k c *ᵥ ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down := by
  let : Module (ZMod (ℓ ^ k)) (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) :=
    Module.compHom _ (algebraMap (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k))
  let Ψ := coeffLevelStalkAddHom b B X x σ hρ t k
  let L : coeffLevelRing ℓ O k →ₗ[ZMod (ℓ ^ k)] (Fin (m * d) → ZMod (ℓ ^ k)) :=
    { toFun := fun c => Ψ (c • v) - coeffLevelMatrix ℓ b m k c *ᵥ Ψ v
      map_add' := fun c c' => by
        rw [add_smul, map_add, map_add, Matrix.add_mulVec]
        abel
      map_smul' := fun a c => by
        have h1 : (a • c) • v = a • (c • v) := by
          show (a • c) • v = algebraMap (ZMod (ℓ ^ k)) (coeffLevelRing ℓ O k) a • (c • v)
          rw [smul_smul, Algebra.smul_def]
        rw [h1, ZMod.map_smul Ψ, map_smul (coeffLevelMatrix ℓ b m k) a c, Matrix.smul_mulVec,
          ← smul_sub]
        rfl }
  have hL : L = 0 := (coeffLevelBasis ℓ b k).ext fun i => by
    show Ψ (coeffLevelBasis ℓ b k i • v) - coeffLevelMatrix ℓ b m k (coeffLevelBasis ℓ b k i) *ᵥ
      Ψ v = 0
    rw [coeffLevelBasis_apply, sub_eq_zero, coeffLevelMatrix_of]
    exact coeffLevelStalkIso_smul_of b B X x σ hρ t k (b i) v
  exact sub_eq_zero.1 (LinearMap.congr_fun hL c)

/-- **The stalks of the `Λ'_k`-sheaf are flat over `Λ'_k`**: along a path `t`, the stalk is
`(ℤ/ℓᵏ)^{md} ≃ (Λ'_k)^m`, linearly over `Λ'_k`. -/
public theorem flat_etaleStalk_coeffLevelStacksSheaf (k : ℕ) (s : GeometricPoint X.1) :
    Module.Flat (coeffLevelRing ℓ O k)
      (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
        ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso X.1 s x
  have hb := ConcreteCategory.bijective_of_isIso (coeffLevelStalkIso b B X x σ hρ t k).hom
  let Ψ := coeffLevelStalkAddHom b B X x σ hρ t k
  refine flat_of_bijective_smul (W := Fin m → coeffLevelRing ℓ O k)
    (fun v => coeffLevelVecEquiv ℓ b m k (Ψ v))
    (fun v w => by rw [map_add, map_add]) (fun c v => ?_) ⟨fun v w h => ?_, fun w => ?_⟩
  · exact (congrArg (coeffLevelVecEquiv ℓ b m k)
        (coeffLevelStalkIso_smul b B X x σ hρ t k c v)).trans
      (coeffLevelVecEquiv_mulVec ℓ b m k c _)
  · exact hb.1 (ULift.ext _ _ ((coeffLevelVecEquiv ℓ b m k).injective h))
  · obtain ⟨v, hv⟩ := hb.2 (ULift.up ((coeffLevelVecEquiv ℓ b m k).symm w))
    refine ⟨v, ?_⟩
    show coeffLevelVecEquiv ℓ b m k ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down = w
    rw [hv, LinearEquiv.apply_symm_apply]

/-- **The stalks of the `Λ'_k`-sheaf are flat over `Λ'_k`.** -/
public theorem flat_etaleModuleStalk_coeffLevelStacksSheaf (k : ℕ) (s : GeometricPoint X.1) :
    Module.Flat (coeffLevelRing ℓ O k)
      ((etaleModuleStalkFunctor.{u, u + 1, 0} B X (coeffLevelRing ℓ O k) s).obj
        (coeffLevelStacksSheaf b B X x σ hρ k)) :=
  flat_etaleStalk_coeffLevelStacksSheaf b B X x σ hρ k s

/-- **The `Λ'_k`-sheaf is finite locally constant**, its underlying abelian sheaf being so. -/
public theorem isFiniteLocallyConstant_coeffLevelStacksSheaf (k : ℕ) [NeZero (ℓ ^ k)]
    [Module.Finite ℤ_[ℓ] O] :
    IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2)
      (coeffLevelStacksSheaf b B X x σ hρ k) :=
  (isFiniteLocallyConstant_moduleSheaf_iff_forget₂ _ _ _).2
    ((e₀).inverse.obj (levelAbelian ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ)
      hρ k)).property

/-- **The `Λ'_k`-sheaf is constructible flat.** -/
public theorem isConstructibleFlatModuleSheaf_coeffLevelStacksSheaf (k : ℕ) [NeZero (ℓ ^ k)]
    [Module.Finite ℤ_[ℓ] O] :
    IsConstructibleFlatModuleSheaf B X (coeffLevelRing ℓ O k)
      (coeffLevelStacksSheaf b B X x σ hρ k) := by
  have h := congrFun (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B X
    (coeffLevelRing ℓ O k)) (coeffLevelStacksSheaf b B X x σ hρ k)
  exact isConstructibleFlatModuleSheaf_of_flat_etaleModuleStalk B X _ _
    (isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X _ _
      (h ▸ isFiniteLocallyConstant_coeffLevelStacksSheaf b B X x σ hρ k))
    (flat_etaleModuleStalk_coeffLevelStacksSheaf b B X x σ hρ k)

end Stalks

section Comparison

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

attribute [local instance] sheafEquiv_functor_additive

/-- The unit of the comparison of the small étale sites, at the `n`-th level of `ℱ_ρ`. -/
abbrev coeffLevelUnit (n : ℕ) :=
  (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unitIso.app
    (representationLevelSheaf B X x e₀
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ (n + 1))

/-- The unit commutes with the action of `Λ'_{n+1}`, on sections. -/
theorem coeffLevelUnit_hom_smul (n : ℕ) (c : coeffLevelRing ℓ O (n + 1))
    (V : (SmallEtale B X.1 X.2)ᵒᵖ)
    (y : (representationLevelSheaf B X x e₀
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ (n + 1)).obj.obj V) :
    ((coeffLevelUnit b B X x σ hρ n).hom.hom.app V).hom
        (((coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c).hom.app V).hom y) =
      (((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map
          (coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c))).hom.app V).hom
        (((coeffLevelUnit b B X x σ hρ n).hom.hom.app V).hom y) := by
  have h := (SmallEtale.sheafEquiv B X.1 X.2
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unit.naturality
      (coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c)
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.hom.app V) h) y

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The inverse of the unit commutes with the action of `Λ'_{n+1}`, on sections. -/
theorem coeffLevelUnit_inv_smul (n : ℕ) (c : coeffLevelRing ℓ O (n + 1))
    (V : (SmallEtale B X.1 X.2)ᵒᵖ)
    (y : ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.obj
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj
        (representationLevelSheaf B X x e₀
          ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ (n + 1)))).obj.obj V) :
    ((coeffLevelUnit b B X x σ hρ n).inv.hom.app V).hom
        ((((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.map
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map
            (coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c))).hom.app V).hom y) =
      ((coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c).hom.app V).hom
        (((coeffLevelUnit b B X x σ hρ n).inv.hom.app V).hom y) := by
  have h := (SmallEtale.sheafEquiv B X.1 X.2
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).unitInv.naturality
      (coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c)
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.hom.app V) h) y

/-- **The comparison of the two constructions of the `n`-th level of `ℱ_ρ` as a sheaf of
`Λ'_{n+1}`-modules**: the one on the small étale site of Stacks 021B, and the one on Mathlib's
small étale site read back on Stacks 021B, through the unit of the comparison of the sites. -/
public def coeffLevelStacksSheafHom (n : ℕ) :
    coeffLevelStacksSheaf b B X x σ hρ (n + 1) ⟶
      (etaleModulesToSmallEtale B X (coeffLevelRing ℓ O (n + 1))).obj
        (coeffLevelEtaleSheaf b B X x e₀ σ hρ n) :=
  ObjectProperty.homMk
    { app := fun V => ModuleCat.ofHom
        (X := (coeffLevelStacksSheaf b B X x σ hρ (n + 1)).obj.obj V)
        (Y := ((etaleModulesToSmallEtale B X (coeffLevelRing ℓ O (n + 1))).obj
          (coeffLevelEtaleSheaf b B X x e₀ σ hρ n)).obj.obj V)
        { toFun := fun y => ((coeffLevelUnit b B X x σ hρ n).hom.hom.app V).hom y
          map_add' := fun y z => map_add _ y z
          map_smul' := fun c y => by
            change ((coeffLevelUnit b B X x σ hρ n).hom.hom.app V).hom
                (((coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c).hom.app V).hom y) =
              (((SmallEtale.sheafEquiv B X.1 X.2
                  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).inverse.map
                ((SmallEtale.sheafEquiv B X.1 X.2
                    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map
                  (coeffLevelSheafMap b B X x e₀ σ hρ (n + 1) c))).hom.app V).hom
                (((coeffLevelUnit b B X x σ hρ n).hom.hom.app V).hom y)
            exact coeffLevelUnit_hom_smul b B X x σ hρ n c V y }
      naturality := fun V W f => by
        ext y
        have h := ConcreteCategory.congr_hom
          ((coeffLevelUnit b B X x σ hρ n).hom.hom.naturality f) y
        exact h }

/-- The comparison is an isomorphism, componentwise the unit. -/
public theorem isIso_coeffLevelStacksSheafHom (n : ℕ) :
    IsIso (coeffLevelStacksSheafHom b B X x σ hρ n) := by
  have : IsIso ((sheafToPresheaf _ _).map (coeffLevelStacksSheafHom b B X x σ hρ n)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun V => ?_)
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    exact ConcreteCategory.bijective_of_isIso ((coeffLevelUnit b B X x σ hρ n).hom.hom.app V)
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **The `n`-th level of `ℱ_ρ` is a constructible flat sheaf of `Λ'_{n+1}`-modules** on Mathlib's
small étale site. -/
public theorem isConstructibleFlatEtaleModule_coeffLevelEtaleSheaf (n : ℕ)
    [Module.Finite ℤ_[ℓ] O] :
    IsConstructibleFlatEtaleModule B X (coeffLevelRing ℓ O (n + 1))
      (coeffLevelEtaleSheaf b B X x e₀ σ hρ n) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have := isIso_coeffLevelStacksSheafHom b B X x σ hρ n
  exact isConstructibleFlatModuleSheaf_congr B X _ (asIso (coeffLevelStacksSheafHom b B X x σ hρ n))
    (isConstructibleFlatModuleSheaf_coeffLevelStacksSheaf b B X x σ hρ (n + 1))

end Comparison

end Stacks.EtaleCohomology

end
