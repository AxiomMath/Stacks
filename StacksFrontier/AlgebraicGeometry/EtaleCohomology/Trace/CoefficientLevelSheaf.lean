module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower

/-!
# The levels of the `O`-sheaf of a representation as sheaves of `ℤ/ℓᵏ ⊗ O`-modules

Let `O` be a finite free `ℤ_ℓ`-algebra with basis `b` and `σ : π₁(X, x̄) → GL_m(O)` a
representation whose restriction of scalars `ρ = Res_b σ : π₁ → GL_{md}(ℤ_ℓ)` is continuous. The
`k`-th level of the `O`-sheaf `ℱ_σ` is the sheaf attached to `(ℤ/ℓᵏ)^{md}` with the action of
`π₁` through `ρ` modulo `ℓᵏ`; the finite ring `Λ'_k = ℤ/ℓᵏ ⊗ O` acts on `(ℤ/ℓᵏ)^{md}` by matrices
commuting with `ρ` (`Stacks.EtaleCohomology.coeffLevelMatrix`), hence by endomorphisms of the
level sheaf. This file constructs that action and the resulting sheaf of `Λ'_k`-modules on the
small étale site of `X`.

## Main definitions

* `Stacks.EtaleCohomology.coeffLevelAbelianMap`: the action of `c ∈ Λ'_k` on the finite discrete
  `π₁`-module `(ℤ/ℓᵏ)^{md}`.
* `Stacks.EtaleCohomology.coeffLevelSheafRingHom`: the action of `Λ'_k` on the `k`-th level
  sheaf of `ℱ_ρ`.
* `Stacks.EtaleCohomology.coeffLevelEtaleSheaf`: the `(n + 1)`-st level of `ℱ_ρ` as a sheaf of
  `Λ'_{n+1}`-modules on the small étale site of `X`.

## Main results

* `Stacks.EtaleCohomology.coeffLevelSheafMap_of`: `1 ⊗ o` acts as the morphism of the
  intertwiner of `o`.
* `Stacks.EtaleCohomology.coeffLevelEtaleSheafRestrictIso`: restricting the scalars of
  `coeffLevelEtaleSheaf` to `ℤ/ℓⁿ⁺¹` gives back the level of `ℱ_ρ`.
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

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ}
  (b : Module.Basis (Fin d) ℤ_[ℓ] O) {m : ℕ}

/-! ### Commutation with the representation -/

section Commute

variable {G : Type*} [Group G] (σ : G →* GL (Fin m) O)

/-- **The action of `ℤ/ℓᵏ ⊗ O` commutes with the reduction of `Res_b σ`.** -/
public theorem coeffLevelMatrix_commute (k : ℕ) (c : coeffLevelRing ℓ O k) (g : G) :
    coeffLevelMatrix ℓ b m k c *
        (coefficientMatrixRingHom b m (σ g).val).map (PadicInt.toZModPow k) =
      (coefficientMatrixRingHom b m (σ g).val).map (PadicInt.toZModPow k) *
        coeffLevelMatrix ℓ b m k c := by
  set R := (coefficientMatrixRingHom b m (σ g).val).map (PadicInt.toZModPow k)
  let L : coeffLevelRing ℓ O k →ₗ[ZMod (ℓ ^ k)] Matrix (Fin (m * d)) (Fin (m * d)) (ZMod (ℓ ^ k)) :=
    { toFun := fun c => coeffLevelMatrix ℓ b m k c * R - R * coeffLevelMatrix ℓ b m k c
      map_add' := fun c c' => by
        rw [map_add, Matrix.add_mul, Matrix.mul_add]
        abel
      map_smul' := fun a c => by
        rw [map_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
        rfl }
  have h : L = 0 := (coeffLevelBasis ℓ b k).ext fun i => by
    show coeffLevelMatrix ℓ b m k (coeffLevelBasis ℓ b k i) * R -
      R * coeffLevelMatrix ℓ b m k (coeffLevelBasis ℓ b k i) = 0
    rw [coeffLevelBasis_apply, coeffLevelMatrix_of, sub_eq_zero]
    show (PadicInt.toZModPow k).mapMatrix (coefficientScalarRingHom b m (b i)) *
        (PadicInt.toZModPow k).mapMatrix (coefficientMatrixRingHom b m (σ g).val) =
      (PadicInt.toZModPow k).mapMatrix (coefficientMatrixRingHom b m (σ g).val) *
        (PadicInt.toZModPow k).mapMatrix (coefficientScalarRingHom b m (b i))
    rw [← map_mul, ← map_mul, coefficientScalarRingHom_commute]
  exact sub_eq_zero.1 (LinearMap.congr_fun h c)

end Commute

/-! ### The action on the finite discrete `π₁`-module `(ℤ/ℓᵏ)^{md}` -/

section Abelian

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : G →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))

/-- Multiplication by a matrix with entries in `ℤ/ℓᵏ` on `(ℤ/ℓᵏ)^r`. -/
public def zmodLevelMapHom {r : ℕ} (k : ℕ) (C : Matrix (Fin r) (Fin r) (ZMod (ℓ ^ k))) :
    ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) →+ ULift.{u + 1} (Fin r → ZMod (ℓ ^ k)) where
  toFun y := ULift.up (C *ᵥ y.down)
  map_zero' := ULift.ext _ _ (Matrix.mulVec_zero C)
  map_add' a b := ULift.ext _ _ (Matrix.mulVec_add C a.down b.down)

/-- **The action of `c ∈ ℤ/ℓᵏ ⊗ O` on the level module `(ℤ/ℓᵏ)^{md}`**, as a morphism of finite
discrete `G`-modules. -/
public def coeffLevelAbelianMap (k : ℕ) (c : coeffLevelRing ℓ O k) :
    levelAbelian ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k ⟶
      levelAbelian ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (zmodLevelMapHom k (coeffLevelMatrix ℓ b m k c))
      comm := fun g => by
        ext y
        apply ULift.ext
        change coeffLevelMatrix ℓ b m k c *ᵥ
            (((coefficientMatrixRingHom b m (σ g).val).map (PadicInt.toZModPow k)) *ᵥ y.down) =
          ((coefficientMatrixRingHom b m (σ g).val).map (PadicInt.toZModPow k)) *ᵥ
            (coeffLevelMatrix ℓ b m k c *ᵥ y.down)
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, coeffLevelMatrix_commute] }))

/-- The action of `c` on `(ℤ/ℓᵏ)^{md}` is multiplication by the matrix
`coeffLevelMatrix ℓ b m k c`. -/
@[simp]
public theorem coeffLevelAbelianMap_apply (k : ℕ) (c : coeffLevelRing ℓ O k)
    (y : ULift.{u + 1} (Fin (m * d) → ZMod (ℓ ^ k))) :
    ((coeffLevelAbelianMap b σ hρ k c).hom.hom.hom.hom.hom y).down =
      coeffLevelMatrix ℓ b m k c *ᵥ y.down :=
  rfl

/-- **The action of `ℤ/ℓᵏ ⊗ O` on `(ℤ/ℓᵏ)^{md}`**, as a ring map to the endomorphisms of the
finite discrete `G`-module. -/
public def coeffLevelAbelianRingHom (k : ℕ) :
    coeffLevelRing ℓ O k →+*
      End (levelAbelian ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k) where
  toFun := coeffLevelAbelianMap b σ hρ k
  map_one' := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ (by
      change coeffLevelMatrix ℓ b m k 1 *ᵥ y.down = y.down
      rw [map_one, Matrix.one_mulVec])
  map_mul' c c' := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ (by
      change coeffLevelMatrix ℓ b m k (c * c') *ᵥ y.down =
        coeffLevelMatrix ℓ b m k c *ᵥ (coeffLevelMatrix ℓ b m k c' *ᵥ y.down)
      rw [map_mul, Matrix.mulVec_mulVec])
  map_zero' := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ (by
      change coeffLevelMatrix ℓ b m k 0 *ᵥ y.down = 0
      rw [map_zero, Matrix.zero_mulVec])
  map_add' c c' := by
    apply finiteContinuousAbelianHom_ext
    ext y
    exact ULift.ext _ _ (by
      change coeffLevelMatrix ℓ b m k (c + c') *ᵥ y.down =
        coeffLevelMatrix ℓ b m k c *ᵥ y.down + coeffLevelMatrix ℓ b m k c' *ᵥ y.down
      rw [map_add, Matrix.add_mulVec])

/-- `1 ⊗ o` acts as the intertwiner `Res_b(o · 1)`. -/
public theorem coeffLevelAbelianMap_of (k : ℕ) (o : O) :
    coeffLevelAbelianMap b σ hρ k (coeffLevelRing.of ℓ O k o) =
      levelAbelianMap hρ hρ (coefficientScalarRingHom b m o)
        (fun g => coefficientScalarRingHom_commute b m o (σ g).val) k := by
  apply finiteContinuousAbelianHom_ext
  ext y
  exact ULift.ext _ _ (by
    show coeffLevelMatrix ℓ b m k (coeffLevelRing.of ℓ O k o) *ᵥ y.down =
      ((coefficientScalarRingHom b m o).map (PadicInt.toZModPow k)) *ᵥ y.down
    rw [coeffLevelMatrix_of])

/-- The action commutes with the scalar operations of `ℤ/ℓᵏ`. -/
public theorem finiteContinuousScalarFunctor_map_comp_coeffLevelAbelianMap (k : ℕ)
    (c : coeffLevelRing ℓ O k) (a : ZMod (ℓ ^ k)) :
    (finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _ (levelModule.{u + 1, u + 1}
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k)).map
        (X := SingleObj.star _) (Y := SingleObj.star _) a ≫ coeffLevelAbelianMap b σ hρ k c =
      coeffLevelAbelianMap b σ hρ k c ≫
        (finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _ (levelModule.{u + 1, u + 1}
          ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k)).map
          (X := SingleObj.star _) (Y := SingleObj.star _) a := by
  apply finiteContinuousAbelianHom_ext
  ext y
  refine ULift.ext _ _ ?_
  show coeffLevelMatrix ℓ b m k c *ᵥ (a • y.down) = a • (coeffLevelMatrix ℓ b m k c *ᵥ y.down)
  rw [Matrix.mulVec_smul]

end Abelian

/-! ### Multiplication by a scalar as an endomorphism of restriction of scalars -/

/-- **Multiplication by `c ∈ S`, as a natural endomorphism of restriction of scalars along
`f : R →+* S`** (`S` commutative). -/
public def restrictScalarsSMulNatTrans {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (c : S) : ModuleCat.restrictScalars.{u + 1} f ⟶ ModuleCat.restrictScalars.{u + 1} f where
  app M := ModuleCat.ofHom (X := (ModuleCat.restrictScalars.{u + 1} f).obj M)
      (Y := (ModuleCat.restrictScalars.{u + 1} f).obj M)
    { toFun := fun y => (c • (y : M) : M)
      map_add' := fun a b => smul_add c (a : M) (b : M)
      map_smul' := fun r y => by
        change c • (f r • (y : M)) = f r • (c • (y : M))
        rw [smul_smul, smul_smul, mul_comm] }
  naturality M N g := by
    ext y
    exact (g.hom.map_smul c y).symm

/-! ### The action on the level sheaves -/

section Sheaves

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive]
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))

/-- The image under `e` of the action of `c`, as a morphism of abelian sheaves with scalar
operations. -/
public def coeffLevelScalarsMap (k : ℕ) (c : coeffLevelRing ℓ O k) :
    representationLevelScalars B X x e
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k ⟶
      representationLevelScalars B X x e
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k :=
  ObjectProperty.homMk
    { app := fun _ => (e.inverse.map (coeffLevelAbelianMap b σ hρ k c)).hom
      naturality := fun _ _ a => congrArg (fun g => g.hom)
        ((e.inverse.map_comp _ _).symm.trans ((congrArg e.inverse.map
          (finiteContinuousScalarFunctor_map_comp_coeffLevelAbelianMap b σ hρ k c a)).trans
            (e.inverse.map_comp _ _))) }

/-- **The action of `c ∈ ℤ/ℓᵏ ⊗ O` on the `k`-th level sheaf of `ℱ_ρ`.** -/
public def coeffLevelSheafMap (k : ℕ) (c : coeffLevelRing ℓ O k) :
    representationLevelSheaf B X x e
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k ⟶
      representationLevelSheaf B X x e
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k :=
  (scalarActionToModuleSheaf (SmallEtale.topology B X.1 X.2) (ZMod (ℓ ^ k))).map
    (coeffLevelScalarsMap b B X x e σ hρ k c)

/-- On sections over `U`, the action of `c` on the level sheaf is the image under `e.inverse` of
its action on `(ℤ/ℓᵏ)^{md}`. -/
public theorem coeffLevelSheafMap_hom_app_apply (k : ℕ) (c : coeffLevelRing ℓ O k) (U)
    (y : (representationLevelSheaf B X x e
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k).obj.obj U) :
    ((coeffLevelSheafMap b B X x e σ hρ k c).hom.app U).hom y =
      ((e.inverse.map (coeffLevelAbelianMap b σ hρ k c)).hom.hom.app U).hom y :=
  rfl

/-- **`ℤ/ℓᵏ ⊗ O` acts on the `k`-th level sheaf of `ℱ_ρ`.** -/
public def coeffLevelSheafRingHom (k : ℕ) :
    coeffLevelRing ℓ O k →+* End (representationLevelSheaf B X x e
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k) where
  toFun := coeffLevelSheafMap b B X x e σ hρ k
  map_one' := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
    ext y
    exact congrArg (fun g => (g.hom.hom.app U).hom y)
      ((congrArg e.inverse.map (map_one (coeffLevelAbelianRingHom b σ hρ k))).trans
        (e.inverse.map_id _))
  map_mul' c c' := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
    ext y
    exact congrArg (fun g => (g.hom.hom.app U).hom y)
      ((congrArg e.inverse.map (map_mul (coeffLevelAbelianRingHom b σ hρ k) c c')).trans
        (e.inverse.map_comp _ _))
  map_zero' := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
    ext y
    exact congrArg (fun g => (g.hom.hom.app U).hom y)
      ((congrArg e.inverse.map (map_zero (coeffLevelAbelianRingHom b σ hρ k))).trans
        (e.inverse.map_zero _ _))
  map_add' c c' := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
    ext y
    exact congrArg (fun g => (g.hom.hom.app U).hom y)
      ((congrArg e.inverse.map (map_add (coeffLevelAbelianRingHom b σ hρ k) c c')).trans
        e.inverse.map_add)

/-- **`1 ⊗ o` acts on the level sheaf as the morphism of the intertwiner of `o`.** -/
public theorem coeffLevelSheafMap_of (k : ℕ) (o : O) :
    coeffLevelSheafMap b B X x e σ hρ k (coeffLevelRing.of ℓ O k o) =
      representationLevelMap B X x e hρ hρ (coefficientScalarRingHom b m o)
        (fun g => coefficientScalarRingHom_commute b m o (σ g).val) k := by
  ext U y
  exact congrArg (fun g => (g.hom.hom.app U).hom y)
    (congrArg e.inverse.map (coeffLevelAbelianMap_of b σ hρ k o))

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

omit [ConnectedSpace X.1] [AlgebraicGeometry.IsNoetherian X.1] in
/-- The comparison of the small étale sites is additive on sheaves of modules. -/
theorem sheafEquiv_functor_additive (R : Type) [CommRing R] :
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] sheafEquiv_functor_additive

/-- The abelian sheaf on Mathlib's small étale site underlying the `n`-th level of `ℱ_ρ`. -/
public abbrev coeffLevelEtaleAbelian (n : ℕ) : Sheaf X.1.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).obj
    ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj
      (representationLevelSheaf B X x e
        ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ (n + 1)))

/-- The action of `ℤ/ℓⁿ⁺¹ ⊗ O` on the abelian sheaf underlying the `n`-th level of `ℱ_ρ`. -/
public def coeffLevelEtaleRingHom (n : ℕ) :
    coeffLevelRing ℓ O (n + 1) →+* End (coeffLevelEtaleAbelian b B X x e σ hρ n) :=
  (Stacks.ModuleCatLift.mapEndRingHom (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})) _).comp
    ((Stacks.ModuleCatLift.mapEndRingHom
      (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor _).comp
        (coeffLevelSheafRingHom b B X x e σ hρ (n + 1)))

/-- **The `n`-th level of `ℱ_ρ` as a sheaf of `ℤ/ℓⁿ⁺¹ ⊗ O`-modules** on Mathlib's small étale
site. -/
public def coeffLevelEtaleSheaf (n : ℕ) : EtaleModules.{u, 0} (coeffLevelRing ℓ O (n + 1)) X.1 :=
  Stacks.ModuleCatLift.sheafOfEndAction (coeffLevelRing ℓ O (n + 1)) X.1.smallEtaleTopology
    (coeffLevelEtaleAbelian b B X x e σ hρ n) (coeffLevelEtaleRingHom b B X x e σ hρ n)

/-- **Restricting the scalars of the `ℤ/ℓⁿ⁺¹ ⊗ O`-sheaf to `ℤ/ℓⁿ⁺¹` gives back the `n`-th level
of `ℱ_ρ`**: the sections are the same abelian groups, and a `ℤ/ℓⁿ⁺¹`-module structure on an
abelian group is unique. -/
public def coeffLevelEtaleSheafRestrictIso (n : ℕ) :
    (etaleModuleRestrictScalars (algebraMap (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1)))
        X.1).obj (coeffLevelEtaleSheaf b B X x e σ hρ n) ≅
      (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj
        (representationLevelSheaf B X x e
          ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ (n + 1)) :=
  letI R := ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod (ℓ ^ (n + 1)))
    (coeffLevelRing ℓ O (n + 1)))
  letI L := (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.obj
    (representationLevelSheaf B X x e
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ (n + 1))
  { hom := ObjectProperty.homMk
      { app := fun U => ModuleCat.ofHom
          (X := R.obj ((coeffLevelEtaleSheaf b B X x e σ hρ n).obj.obj U)) (Y := L.obj.obj U)
          { toFun := fun y => y
            map_add' := fun _ _ => rfl
            map_smul' := fun a y => ZMod.map_smul
              (M := R.obj ((coeffLevelEtaleSheaf b B X x e σ hρ n).obj.obj U)) (M₁ := L.obj.obj U)
              (AddMonoidHom.mk' (fun y => y) (fun _ _ => rfl)) a y }
        naturality := fun _ _ _ => rfl }
    inv := ObjectProperty.homMk
      { app := fun U => ModuleCat.ofHom (X := L.obj.obj U)
          (Y := R.obj ((coeffLevelEtaleSheaf b B X x e σ hρ n).obj.obj U))
          { toFun := fun y => y
            map_add' := fun _ _ => rfl
            map_smul' := fun a y => ZMod.map_smul (M := L.obj.obj U)
              (M₁ := R.obj ((coeffLevelEtaleSheaf b B X x e σ hρ n).obj.obj U))
              (AddMonoidHom.mk' (fun y => y) (fun _ _ => rfl)) a y }
        naturality := fun _ _ _ => rfl }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [AlgebraicGeometry.IsNoetherian X.1] in
/-- **Under the identification, multiplication by `c` is the action of `c` on the level.** -/
public theorem coeffLevelEtaleSheafRestrictIso_smul (n : ℕ) (c : coeffLevelRing ℓ O (n + 1)) :
    (etaleModuleRestrictScalarsNatTrans (algebraMap (ZMod (ℓ ^ (n + 1)))
        (coeffLevelRing ℓ O (n + 1))) (restrictScalarsSMulNatTrans _ c) X.1).app
          (coeffLevelEtaleSheaf b B X x e σ hρ n) ≫
        (coeffLevelEtaleSheafRestrictIso b B X x e σ hρ n).hom =
      (coeffLevelEtaleSheafRestrictIso b B X x e σ hρ n).hom ≫
        (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.map
          (coeffLevelSheafMap b B X x e σ hρ (n + 1) c) := by
  ext U y
  show (c • (show (coeffLevelEtaleSheaf b B X x e σ hρ n).obj.obj U from y)) = _
  exact (ModuleCat.mkOfSMul'_smul _ c _).trans rfl

end Sheaves

end Stacks.EtaleCohomology

end
