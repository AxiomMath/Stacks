module

public import StacksFrontier.CategoryTheory.Abelian.StrictLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafShortExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Presentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower

/-!
# The ℓ-adic sheaf of a strict ℓ-adic tower of sheaves of `ℤ_ℓ`-modules

Let `H : ℕᵒᵖ ⥤ EtaleModules ℤ_ℓ X` be a strict ℓ-adic tower of sheaves of `ℤ_ℓ`-modules on
Mathlib's small étale site of `X` (`CategoryTheory.LAdicTower.IsStrict`: level `n` killed by
`ℓⁿ⁺¹`, transitions the quotients by `ℓⁿ⁺¹`). Read on the small étale site of Stacks 021B, the
level `Hₙ` is a sheaf of abelian groups killed by `ℓⁿ⁺¹`, hence a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules
(`Stacks.EtaleCohomology.strictTowerLevel`), and the transitions of `H` are additive maps, hence
linear. When these levels are constructible they form an ℓ-adic sheaf in the sense of
[Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
(`Stacks.EtaleCohomology.LAdicSheaf.ofStrictTower`): the compatibility condition of Tag 03UM
is the cokernel property of the transitions, read on the underlying abelian sheaves. Its tower
of levels, read back on Mathlib's site as sheaves of `ℤ_ℓ`-modules, is `H`
(`Stacks.EtaleCohomology.LAdicSheaf.padicTowerOfStrictTowerIso`), because a `ℤ_ℓ`-module
structure on a group killed by `ℓⁿ⁺¹` is the one through `ℤ_ℓ → ℤ/ℓⁿ⁺¹ℤ`
(`Stacks.EtaleCohomology.padicInt_smul_eq_val_nsmul`).

This is how the ℓ-adic sheaf `R^q f_! F` of the Leray step of the reduction of the weight bound
of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) is assembled from the stable
images of the tower `n ↦ R^q f_! Fₙ`.

## Main definitions

* `Stacks.EtaleCohomology.strictTowerLevel`, `Stacks.EtaleCohomology.strictTowerTransition`.
* `Stacks.EtaleCohomology.LAdicSheaf.ofStrictTower`.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerOfStrictTowerIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **A `ℤ_ℓ`-module structure on an element killed by `ℓⁿ` factors through `ℤ_ℓ → ℤ/ℓⁿℤ`.** -/
theorem padicInt_smul_eq_val_nsmul {ℓ : ℕ} [Fact ℓ.Prime] {M : Type*} [AddCommGroup M]
    [Module ℤ_[ℓ] M] (n : ℕ) (a : ℤ_[ℓ]) (x : M) (hx : ℓ ^ n • x = 0) :
    a • x = (PadicInt.toZModPow (p := ℓ) n a).val • x := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hmem : a - ((PadicInt.toZModPow (p := ℓ) n a).val : ℤ_[ℓ]) ∈
      RingHom.ker (PadicInt.toZModPow (p := ℓ) n) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  calc a • x = (a - ((PadicInt.toZModPow (p := ℓ) n a).val : ℤ_[ℓ])) • x +
        ((PadicInt.toZModPow (p := ℓ) n a).val : ℤ_[ℓ]) • x := by
        rw [← add_smul, sub_add_cancel]
    _ = (PadicInt.toZModPow (p := ℓ) n a).val • x := by
        rw [← hc, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul ℤ_[ℓ] (ℓ ^ n), hx, smul_zero,
          zero_add, Nat.cast_smul_eq_nsmul]

/-- In a `ℤ/Nℤ`-module the action of `k` is that of the natural number `k.val`. -/
theorem zmod_smul_eq_val_nsmul {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M] [Module (ZMod N) M]
    (k : ZMod N) (x : M) : k • x = k.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  exact Nat.cast_smul_eq_nsmul (ZMod N) k.val x

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

attribute [local instance] moduleCat_hasLimitsOfSize

/-- The category of `ℤ_ℓ`-modules in universe `u + 1` has limits of size `u + 1`. -/
local instance strictTower_hasLimitsOfSize_moduleCat :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} ℤ_[ℓ]) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}

/-- Forgetting a sheaf of `ℤ_ℓ`-modules on the small étale site of Stacks 021B to abelian groups
gives a sheaf. -/
local instance strictTower_hasSheafCompose_forget₂ :
    (SmallEtale.topology B X.1 X.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} ℤ_[ℓ] _

/-- A sheaf of `ℤ_ℓ`-modules on Mathlib's small étale site, read as a sheaf of abelian groups on
the small étale site of Stacks 021B. -/
abbrev padicForget :
    EtaleModules.{u, 0} ℤ_[ℓ] X.1 ⥤
      Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1} :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse ⋙
    sheafCompose (SmallEtale.topology B X.1 X.property)
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})

/-- Reading a sheaf of `ℤ_ℓ`-modules as a sheaf of abelian groups on Stacks 021B is additive. -/
instance padicForget_additive : (padicForget B X ℓ).Additive := by
  have : (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (sheafCompose (SmallEtale.topology B X.1 X.property)
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp only [padicForget]
  infer_instance

/-- An additive functor sends multiplication by `N` on `P` to multiplication by `N`. -/
private theorem map_nsmul_id {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] (N : ℕ) (P : C) :
    Φ.map (N • 𝟙 P) = N • 𝟙 (Φ.obj P) := by
  rw [Φ.map_nsmul, Φ.map_id]

/-- An additive functor preserves `N • 𝟙 P ≫ f = 0`. -/
private theorem nsmul_id_comp_map_eq_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] {N : ℕ} {P Q : C} {f : P ⟶ Q}
    (h : (N • 𝟙 P) ≫ f = 0) : (N • 𝟙 (Φ.obj P)) ≫ Φ.map f = 0 := by
  rw [← map_nsmul_id, ← Φ.map_comp, h, Φ.map_zero]

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The sections of a sheaf of `ℤ_ℓ`-modules killed by `N` are killed by `N` on Stacks 021B. -/
theorem padicForget_nsmul_eq_zero {P : EtaleModules.{u, 0} ℤ_[ℓ] X.1} {N : ℕ}
    (hP : N • 𝟙 P = 0) (U : (SmallEtale B X.1 X.property)ᵒᵖ)
    (x : ((padicForget B X ℓ).obj P).obj.obj U) : N • x = 0 := by
  have h1 : N • 𝟙 ((padicForget B X ℓ).obj P) = 0 := by
    rw [← map_nsmul_id, hP, Functor.map_zero]
  have h2 := congrArg (fun f => (f.hom.app U).hom x) h1
  simp only [abelianSheaf_nsmul_app] at h2
  exact h2

variable {B X ℓ}

/-- **Level `n` of the ℓ-adic sheaf of a strict tower**: `Hₙ`, read on Stacks 021B, as a sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules. -/
def strictTowerLevel (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ) (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  zmodSheafOfAnnihilated.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1))
    ((padicForget B X ℓ).obj (towerObj H n))
    (padicForget_nsmul_eq_zero B X ℓ (hH.annihilated n))

attribute [local instance] underlyingLevelFunctor_full

/-- The underlying abelian sheaf of the level `n` is the level `Hₙ` read on Stacks 021B. -/
def strictTowerLevelIso (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ) (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).obj (strictTowerLevel H hH n) ≅
      (padicForget B X ℓ).obj (towerObj H n) :=
  zmodSheafOfAnnihilatedIso.{u + 1, u + 1, u} _ _ _ _

/-- The underlying abelian sheaf of the restriction of scalars of level `n` is `Hₙ` on 021B. -/
def strictTowerLevelRestrictIso (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ)
    (n : ℕ) :
    (underlyingLevelFunctor B X ℓ (n + 1)).obj ((strictTowerLevel H hH n).restrictScalars B X ℓ n) ≅
      (padicForget B X ℓ).obj (towerObj H n) where
  hom := ⟨{ app U := AddCommGrpCat.ofHom (AddMonoidHom.id _) }⟩
  inv := ⟨{ app U := AddCommGrpCat.ofHom (AddMonoidHom.id _) }⟩

/-- **The transition of the ℓ-adic sheaf of a strict tower**: the transition of `H`, an additive
map, read as a `ℤ/ℓⁿ⁺²ℤ`-linear map through the full forgetful functor. -/
def strictTowerTransition (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ) (n : ℕ) :
    strictTowerLevel H hH (n + 1) ⟶ (strictTowerLevel H hH n).restrictScalars B X ℓ n :=
  (underlyingLevelFunctor B X ℓ (n + 1)).preimage
    ((strictTowerLevelIso H hH (n + 1)).hom ≫
      (padicForget B X ℓ).map (towerMap H (Nat.le_succ n)) ≫
        (strictTowerLevelRestrictIso H hH n).inv)

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- On underlying abelian sheaves, the transition of the ℓ-adic sheaf of a strict tower is the
transition of `H` between the levels `Hₙ₊₁` and `Hₙ`. -/
theorem underlyingLevelFunctor_map_strictTowerTransition
    (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ) (n : ℕ) :
    (underlyingLevelFunctor B X ℓ (n + 1)).map (strictTowerTransition H hH n) =
      (strictTowerLevelIso H hH (n + 1)).hom ≫
        (padicForget B X ℓ).map (towerMap H (Nat.le_succ n)) ≫
          (strictTowerLevelRestrictIso H hH n).inv :=
  (underlyingLevelFunctor B X ℓ (n + 1)).map_preimage _

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- On underlying abelian sheaves, multiplication by `ℓⁿ⁺¹` followed by the transition of the
ℓ-adic sheaf of a strict tower is zero. -/
theorem strictTowerTransition_underlying_condition (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hH : IsStrict H ℓ) (n : ℕ) :
    ((ℓ ^ (n + 1)) •
        𝟙 ((underlyingLevelFunctor B X ℓ (n + 1)).obj (strictTowerLevel H hH (n + 1)))) ≫
      (underlyingLevelFunctor B X ℓ (n + 1)).map (strictTowerTransition H hH n) = 0 := by
  have h0 : ((ℓ ^ (n + 1)) • 𝟙 ((padicForget B X ℓ).obj (towerObj H (n + 1)))) ≫
      (padicForget B X ℓ).map (towerMap H (Nat.le_succ n)) = 0 := by
    exact nsmul_id_comp_map_eq_zero _ (nsmul_id_comp_eq_zero hH.annihilated n)
  rw [underlyingLevelFunctor_map_strictTowerTransition, ← Category.assoc,
    CategoryTheory.Abelian.nsmul_id_comp, Category.assoc,
    ← Category.assoc ((ℓ ^ (n + 1)) • 𝟙 ((padicForget B X ℓ).obj (towerObj H (n + 1)))), h0,
    zero_comp, comp_zero]

omit [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- **The compatibility condition of Tag 03UM** for the ℓ-adic sheaf of a strict tower. -/
theorem strictTower_reduction_isIso (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ)
    (n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X ℓ n _ _ (strictTowerTransition H hH n)) := by
  let Φ := padicForget B X ℓ
  have h₁ := isColimitCoforkMapOfIsColimit' Φ (nsmul_id_comp_eq_zero hH.annihilated n)
    (hH.isCokernel n)
  have hf := map_nsmul_id Φ (ℓ ^ (n + 1)) (towerObj H (n + 1))
  have h₂ := isColimitCokernelCoforkOfEq hf _ h₁
  have hw : ((ℓ ^ (n + 1)) • 𝟙 (Φ.obj (towerObj H (n + 1)))) ≫
      Φ.map (towerMap H (Nat.le_succ n)) = 0 := by
    exact nsmul_id_comp_map_eq_zero _ (nsmul_id_comp_eq_zero hH.annihilated n)
  have hf' : ((ℓ ^ (n + 1)) • 𝟙 ((underlyingLevelFunctor B X ℓ (n + 1)).obj
      (strictTowerLevel H hH (n + 1)))) ≫ (strictTowerLevelIso H hH (n + 1)).hom =
      (strictTowerLevelIso H hH (n + 1)).hom ≫ ((ℓ ^ (n + 1)) • 𝟙 _) :=
    CategoryTheory.Abelian.nsmul_id_comp _ _
  have h₃ := isColimitCokernelCoforkConj ((ℓ ^ (n + 1)) • 𝟙 _)
    (Φ.map (towerMap H (Nat.le_succ n))) hw h₂ (strictTowerLevelIso H hH (n + 1))
    (strictTowerLevelRestrictIso H hH n).symm _ hf'
    (conj_cokernel_condition _ _ hw _ _ _ hf')
  exact LAdicSheaf.reduction_isIso_of_underlying_cokernel B X ℓ n _ _ (strictTowerTransition H hH n)
    (strictTowerTransition_underlying_condition H hH n)
    (isColimitCokernelCoforkOfEqπ (underlyingLevelFunctor_map_strictTowerTransition H hH n).symm _
      h₃)

/-- **The ℓ-adic sheaf of a strict ℓ-adic tower** of sheaves of `ℤ_ℓ`-modules on Mathlib's small
étale site whose levels, read as sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules on Stacks 021B, are constructible. -/
def LAdicSheaf.ofStrictTower (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ)
    (hc : ∀ n, IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (strictTowerLevel H hH n)) :
    LAdicSheaf.{u, u + 1} B X ℓ where
  level := strictTowerLevel H hH
  constructible := hc
  transition := strictTowerTransition H hH
  reduction_isIso := strictTower_reduction_isIso H hH

/-! ### The tower of levels of the ℓ-adic sheaf of a strict tower -/

variable (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ)
  (hc : ∀ n, IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (strictTowerLevel H hH n))

/-- The component at `U` of `padicLevelOfStrictTowerIso`: the identity on sections, `ℤ_ℓ`-linear
because the two `ℤ_ℓ`-module structures on a group killed by `ℓⁿ⁺¹` agree. -/
def padicLevelOfStrictTowerHomApp (n : ℕ) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U ⟶
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
        (towerObj H n)).obj.obj U :=
  letI : Module ℤ_[ℓ]
      ((LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U) :=
    ModuleCat.isModule _
  ModuleCat.ofHom (R := ℤ_[ℓ])
    (X := (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U)
    (Y := ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
        (towerObj H n)).obj.obj U)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        have hx : ℓ ^ (n + 1) • x = 0 :=
          padicForget_nsmul_eq_zero B X ℓ (hH.annihilated n) U x
        rw [RingHom.id_apply, padicInt_smul_eq_val_nsmul (n + 1) a x hx]
        exact (padicInt_smul_eq_val_nsmul (M := ((SmallEtale.sheafEquiv B X.1 X.property
          (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj (towerObj H n)).obj.obj U) (n + 1) a x hx).symm }

/-- The inverse of `padicLevelOfStrictTowerHomApp`: the identity on sections over `U`, read from
`Hₙ` back to level `n` of the ℓ-adic sheaf of `H`. -/
def padicLevelOfStrictTowerInvApp (n : ℕ) (U : (SmallEtale B X.1 X.property)ᵒᵖ) :
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
        (towerObj H n)).obj.obj U ⟶
      (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U :=
  letI : Module ℤ_[ℓ]
      ((LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U) :=
    ModuleCat.isModule _
  ModuleCat.ofHom (R := ℤ_[ℓ])
    (X := ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
        (towerObj H n)).obj.obj U)
    (Y := (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        have hx : ℓ ^ (n + 1) • x = 0 :=
          padicForget_nsmul_eq_zero B X ℓ (hH.annihilated n) U x
        rw [RingHom.id_apply, padicInt_smul_eq_val_nsmul (n + 1) a x hx]
        exact (padicInt_smul_eq_val_nsmul (M := (LAdicSheaf.padicLevel B X ℓ
          (LAdicSheaf.ofStrictTower H hH hc) n).obj.obj U) (n + 1) a x hx).symm }

/-- **Level `n` of the ℓ-adic sheaf of a strict tower, as a sheaf of `ℤ_ℓ`-modules on 021B, is
`Hₙ`**: the two `ℤ_ℓ`-module structures on a sheaf killed by `ℓⁿ⁺¹` agree. -/
def padicLevelOfStrictTowerIso (n : ℕ) :
    LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n ≅
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
        (towerObj H n) where
  hom := ⟨{ app U := padicLevelOfStrictTowerHomApp H hH hc n U
            naturality _ _ _ := rfl }⟩
  inv := ⟨{ app U := padicLevelOfStrictTowerInvApp H hH hc n U
            naturality _ _ _ := rfl }⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The isomorphisms `padicLevelOfStrictTowerIso` carry the transitions of the ℓ-adic sheaf of a
strict tower to those of `H`. -/
theorem padicTransition_ofStrictTower_comp (n : ℕ) :
    LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n ≫
        (padicLevelOfStrictTowerIso H hH hc n).hom =
      (padicLevelOfStrictTowerIso H hH hc (n + 1)).hom ≫
        (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.map
          (towerMap H (Nat.le_succ n)) := by
  ext U x
  exact congrArg (fun φ => (φ.hom.app U).hom x)
    (underlyingLevelFunctor_map_strictTowerTransition H hH n)

/-- **The tower of levels of the ℓ-adic sheaf of a strict tower is the tower.** -/
def LAdicSheaf.padicTowerOfStrictTowerIso :
    LAdicSheaf.padicTower B X ℓ (LAdicSheaf.ofStrictTower H hH hc) ≅ H := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])
  let c : ∀ n, towerObj (LAdicSheaf.padicTower B X ℓ (LAdicSheaf.ofStrictTower H hH hc)) n ≅
      towerObj H n := fun n =>
    e.functor.mapIso (padicLevelOfStrictTowerIso H hH hc n) ≪≫ e.counitIso.app (towerObj H n)
  let α : LAdicSheaf.padicTower B X ℓ (LAdicSheaf.ofStrictTower H hH hc) ⟶ H :=
    NatTrans.ofOpSequence (fun n => (c n).hom) (fun n => by
      have h1 : (LAdicSheaf.padicTower B X ℓ (LAdicSheaf.ofStrictTower H hH hc)).map
          (homOfLE (n.le_add_right 1)).op = e.functor.map
            (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n) :=
        LAdicSheaf.padicTower_map_succ B X ℓ _ n
      have hn := e.counitIso.hom.naturality (towerMap H (Nat.le_succ n))
      simp only [Functor.comp_map, Functor.id_map] at hn
      rw [h1]
      change e.functor.map (LAdicSheaf.padicTransition B X ℓ (LAdicSheaf.ofStrictTower H hH hc) n) ≫
          (e.functor.map (padicLevelOfStrictTowerIso H hH hc n).hom ≫
            e.counitIso.hom.app (towerObj H n)) =
        (e.functor.map (padicLevelOfStrictTowerIso H hH hc (n + 1)).hom ≫
          e.counitIso.hom.app (towerObj H (n + 1))) ≫ towerMap H (Nat.le_succ n)
      rw [← Category.assoc, ← e.functor.map_comp, padicTransition_ofStrictTower_comp,
        e.functor.map_comp, Category.assoc, hn, Category.assoc])
  exact NatIso.ofComponents (fun n => c n.unop) (fun f => α.naturality f)

end Stacks.EtaleCohomology
