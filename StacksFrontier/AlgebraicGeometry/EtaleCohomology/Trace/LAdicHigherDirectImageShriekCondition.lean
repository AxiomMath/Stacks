module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalarsReflects
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence

/-!
# The hypotheses of `R^r g_! G` from constructibility

The ℓ-adic sheaf `R^r g_! G` (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`) is
built under `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageShriekCondition`: Noetherianity of
`R^{r+1} g_! G'₀` and constructibility of the stable images. This file derives these from the
constructibility of the sheaves `R^r g_! G'ₙ` and `R^{r+1} g_! G'ₙ` of `ℤ_ℓ`-modules, which is what
Stacks 0GL0 gives.

## Main results

* `Stacks.EtaleCohomology.isNoetherianObject_of_isNoetherianObject_map`: a full, faithful,
  monomorphism-preserving functor reflects Noetherian objects.
* `Stacks.EtaleCohomology.isNoetherianObject_of_isConstructibleEtaleModule`: a constructible sheaf
  of `ℤ_ℓ`-modules on Mathlib's small étale site is a Noetherian object.
* `LAdicSheaf.higherDirectImageShriekCondition_of_isConstructibleEtaleModule`:
  the hypotheses of `R^r g_! G` hold when the `R^r g_! G'ₙ` and `R^{r+1} g_! G'₀` are
  constructible: the stable images are subsheaves of constructible sheaves (Stacks 09BH), killed
  by `ℓⁿ⁺¹`, hence constructible over `ℤ/ℓⁿ⁺¹ℤ`.
* `LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput`:
  the same from Tag 0GL0 (`Stacks.EtaleCohomology.LowerShriekConstructibilityInput`), the levels
  of an ℓ-adic sheaf being constructible torsion sheaves of `ℤ_ℓ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **A full, faithful functor preserving monomorphisms reflects Noetherian objects**: it embeds
the subobject lattice. -/
theorem isNoetherianObject_of_isNoetherianObject_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (P : C)
    [IsNoetherianObject (F.obj P)] : IsNoetherianObject P := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro s
  let e : Subobject P ↪o Subobject (F.obj P) :=
    OrderEmbedding.ofMapLEIff (subobjectFunctorMap F P) (subobjectFunctorMap_le_iff F P)
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    (⟨fun m => e (s m), fun a b h => e.monotone (s.monotone h)⟩ : ℕ →o Subobject (F.obj P))
  exact ⟨n, fun m hm => e.injective (hn m hm)⟩

/-- **A constructible sheaf of `ℤ_ℓ`-modules on Mathlib's small étale site is a Noetherian
object**: Stacks 09YV on the small étale site of Stacks 021B, transported along the equivalence. -/
theorem isNoetherianObject_of_isConstructibleEtaleModule (B : BigEtaleSite.{u}) (X : B.Scheme)
    [IsNoetherian X.1] (ℓ : ℕ) [Fact ℓ.Prime] (P : EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hP : IsBigSiteConstructibleEtaleModule.{u, 0} B X ℤ_[ℓ] P) : IsNoetherianObject P := by
  let _ := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ_[ℓ]
  have : IsNoetherianObject ((etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]).obj P) :=
    isNoetherianObject_of_isConstructibleModuleSheaf' B ℤ_[ℓ] X _ hP
  exact isNoetherianObject_of_isNoetherianObject_map (etaleModulesToSmallEtale.{u, 0} B X ℤ_[ℓ]) P

section Condition

attribute [local instance] HasDerivedCategory.standard
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  (jg : CompactificationOf (Over.mk (B.inclusion.map g)))

/-- **The hypotheses of `R^r g_! G` from constructibility over `ℤ_ℓ`**: if every `R^r g_! G'ₙ` and
`R^{r+1} g_! G'₀` is a constructible sheaf of `ℤ_ℓ`-modules, then `R^{r+1} g_! G'₀` is a Noetherian
object, and the stable images of `n ↦ R^r g_! G'ₙ`, subsheaves of constructible sheaves
(Stacks 09BH) killed by `ℓⁿ⁺¹`, are constructible sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules. -/
theorem LAdicSheaf.higherDirectImageShriekCondition_of_isConstructibleEtaleModule
    (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h₀ : ∀ n, IsBigSiteConstructibleEtaleModule.{u, 0} B W ℤ_[ℓ]
      (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) n))
    (h₁ : IsBigSiteConstructibleEtaleModule.{u, 0} B W ℤ_[ℓ]
      (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G ((r : ℤ) + 1)) 0)) :
    LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r := by
  have := isNoetherianObject_of_isConstructibleEtaleModule B W ℓ _ h₁
  refine ⟨inferInstance, fun n => isConstructibleModuleSheaf_strictTowerLevel _ _ n ?_⟩
  let _ := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B W ℤ_[ℓ]
  exact isConstructibleModuleSheaf_of_mono' B ℤ_[ℓ] W
    ((etaleModulesToSmallEtale.{u, 0} B W ℤ_[ℓ]).map
      ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageι.app (op n))) (h₀ n)

variable {B ℓ} in
/-- **The levels of an ℓ-adic sheaf are constructible sheaves of `ℤ_ℓ`-modules**: restriction of
scalars along the surjection `ℤ_ℓ → ℤ/ℓⁿ⁺¹ℤ` preserves constructibility. -/
theorem LAdicSheaf.isConstructibleEtaleModule_padicTower {X : B.Scheme} [IsNoetherian X.1]
    (F : LAdicSheaf B X ℓ) (n : ℕ) :
    IsBigSiteConstructibleEtaleModule.{u, 0} B X ℤ_[ℓ]
      (towerObj (LAdicSheaf.padicTower B X ℓ F) n) := by
  let _ := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ_[ℓ]
  exact AlgebraicGeometry.isConstructibleModuleSheaf_congr B ℤ_[ℓ] X
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).unitIso.app
      (LAdicSheaf.padicLevel B X ℓ F n))
    (isConstructibleModuleSheaf_restrictScalars.{u, u + 1} B X ℤ_[ℓ] (ZMod (ℓ ^ (n + 1)))
      (PadicInt.toZModPow (n + 1)) (ZMod.ringHom_surjective _) (F.level n) (F.constructible n))

variable {B ℓ} in
/-- The levels of an ℓ-adic sheaf, as sheaves of `ℤ_ℓ`-modules, are torsion. -/
theorem LAdicSheaf.isTorsionEtaleModule_padicTower {X : B.Scheme} [IsNoetherian X.1]
    (F : LAdicSheaf B X ℓ) (n : ℕ) :
    IsTorsionEtaleModule.{u, 0} ℤ_[ℓ] X.1 (towerObj (LAdicSheaf.padicTower B X ℓ F) n) :=
  isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero _ (ℓ ^ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (LAdicSheaf.padicTower_annihilated B X ℓ F n)

/-- **The hypotheses of `R^r g_! G` from Tag 0GL0**: the `Rᵠ g_! G'ₙ` of the levels of the flat
model, constructible torsion sheaves of `ℤ_ℓ`-modules, are constructible
(`Stacks.EtaleCohomology.LowerShriekConstructibilityInput`). -/
theorem LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (hT : LowerShriekConstructibilityInput B)
    (G : LAdicSheaf B U ℓ) (r : ℕ) :
    LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r := by
  refine LAdicSheaf.higherDirectImageShriekCondition_of_isConstructibleEtaleModule B ℓ g jg G r
    (fun n => ?_) ?_ <;>
  exact hT _ jg ℤ_[ℓ] _ (LAdicSheaf.isConstructibleEtaleModule_padicTower _ _)
    (LAdicSheaf.isTorsionEtaleModule_padicTower _ _) _

end Condition

end Stacks.EtaleCohomology
