module

public import StacksFrontier.CategoryTheory.Abelian.StrictLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# The towers `n ↦ R^q f_! Fₙ` of an ℓ-adic sheaf with flat levels

Let `F` be an ℓ-adic sheaf on `X` and `f : X ⟶ Y` a morphism of the big étale site with a
compactification `j`. The levels of `F`, read as sheaves of `ℤ_ℓ`-modules on Mathlib's small
étale site, form a strict ℓ-adic tower (`Stacks.EtaleCohomology.LAdicSheaf.padicTower_isStrict`):
level `n` is killed by `ℓⁿ⁺¹` and the transitions are the quotients by `ℓⁿ⁺¹`. When the levels
of `F` are flat the sequences `0 → F_a → F_{a+b+1} → F_b → 0` are exact, and the long exact
sequences of `R^q f_!` (`Stacks.EtaleCohomology.singleHomology_exact₂` and its companions) on
them assemble into the data `CategoryTheory.LAdicTower.LESData` for the towers
`n ↦ R^q f_! Fₙ` and `n ↦ R^{q+1} f_! Fₙ`
(`Stacks.EtaleCohomology.LAdicSheaf.lowerShriekLESData`).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.padicTower_isStrict`.
* `Stacks.EtaleCohomology.LAdicSheaf.powExact_padicTower`.
* `Stacks.EtaleCohomology.LAdicSheaf.lowerShriekLESData`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

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

/-- The levels of an ℓ-adic sheaf are killed by the powers of `ℓ`, on Mathlib's site. -/
theorem LAdicSheaf.padicTower_annihilated (F : LAdicSheaf B X ℓ) (n : ℕ) :
    ℓ ^ (n + 1) • 𝟙 (towerObj (LAdicSheaf.padicTower B X ℓ F) n) = 0 := by
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1
  let eA := (sheafEquivRestrictScalarsIso B X.1 X.property
    (PadicInt.toZModPow (p := ℓ) (n + 1))).app (F.level n)
  have h0 : ℓ ^ (n + 1) • 𝟙 (R.obj (LAdicSheaf.etaleLevel B X ℓ F n)) = 0 := by
    rw [← R.map_id, ← R.map_nsmul,
      zmodSheaf_nsmul_id X.1.smallEtaleTopology (ℓ ^ (n + 1)) (LAdicSheaf.etaleLevel B X ℓ F n),
      R.map_zero]
  show ℓ ^ (n + 1) • 𝟙 ((sheafCompose (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1))) ⋙
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor).obj
        (F.level n)) = 0
  rw [← cancel_epi eA.hom, comp_zero, Preadditive.comp_nsmul, Category.comp_id,
    ← Category.id_comp eA.hom, ← Preadditive.nsmul_comp]
  exact (congrArg (· ≫ eA.hom) h0).trans zero_comp

/-- The transition of the tower of levels is the quotient by `ℓⁿ⁺¹`. -/
def LAdicSheaf.padicTowerIsCokernel (F : LAdicSheaf B X ℓ) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ _
      (nsmul_id_comp_eq_zero (LAdicSheaf.padicTower_annihilated B X ℓ F) n)) := by
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) X.1
  have h₀ := LAdicSheaf.etaleTransitionIsCokernel B X ℓ F n
  have h₁ := isColimitCoforkMapOfIsColimit' R (LAdicSheaf.etaleTransition_condition B X ℓ F n) h₀
  have hf : R.map ((ℓ ^ (n + 1)) • 𝟙 (LAdicSheaf.etaleLevel B X ℓ F (n + 1))) =
      (ℓ ^ (n + 1)) • 𝟙 (R.obj (LAdicSheaf.etaleLevel B X ℓ F (n + 1))) := by
    rw [R.map_nsmul, R.map_id]
  have h₂ := isColimitCokernelCoforkOfEq hf _ h₁
  let eB := (sheafEquivRestrictScalarsIso B X.1 X.property
    (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).app (F.level (n + 1))
  let eA := (sheafEquivRestrictScalarsIso B X.1 X.property
    (PadicInt.toZModPow (p := ℓ) (n + 1))).app (F.level n)
  let c := (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))
    (Stacks.InverseSystem.levelCast ℓ n) (PadicInt.toZModPow (p := ℓ) (n + 1))
    (toZModPow_succ_comp ℓ n) X.1).app (LAdicSheaf.etaleLevel B X ℓ F n)
  have hf' : ((ℓ ^ (n + 1)) • 𝟙 (towerObj (LAdicSheaf.padicTower B X ℓ F) (n + 1))) ≫
      eB.symm.hom = eB.symm.hom ≫ ((ℓ ^ (n + 1)) • 𝟙 _) :=
    CategoryTheory.Abelian.nsmul_id_comp eB.symm.hom (ℓ ^ (n + 1))
  have hw : ((ℓ ^ (n + 1)) • 𝟙 (R.obj (LAdicSheaf.etaleLevel B X ℓ F (n + 1)))) ≫
      R.map (LAdicSheaf.etaleTransition B X ℓ F n) = 0 := by
    rw [← hf, ← R.map_comp, LAdicSheaf.etaleTransition_condition, R.map_zero]
  have h₃ := isColimitCokernelCoforkConj ((ℓ ^ (n + 1)) • 𝟙 _)
    (R.map (LAdicSheaf.etaleTransition B X ℓ F n)) hw h₂ eB.symm (c ≪≫ eA) _ hf'
    (conj_cokernel_condition _ _ hw eB.symm (c ≪≫ eA) _ hf')
  refine isColimitCokernelCoforkOfEqπ ?_ _ h₃
  refine Eq.trans ?_ (LAdicSheaf.padicTower_map_succ B X ℓ F n).symm
  refine (cancel_mono eA.inv).1 ?_
  simp only [Iso.symm_hom, Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (LAdicSheaf.sheafEquiv_map_padicTransition B X ℓ F n).symm

/-- **The tower of levels of an ℓ-adic sheaf is a strict ℓ-adic tower.** -/
theorem LAdicSheaf.padicTower_isStrict (F : LAdicSheaf B X ℓ) :
    IsStrict (LAdicSheaf.padicTower B X ℓ F) ℓ :=
  IsStrict.of_isCokernel (LAdicSheaf.padicTower_annihilated B X ℓ F)
    (LAdicSheaf.padicTowerIsCokernel B X ℓ F)

/-- **The levels of an ℓ-adic sheaf with flat levels stay flat on Mathlib's site as sheaves of
`ℤ_ℓ`-modules.** -/
theorem LAdicSheaf.powExact_padicTower (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n)) (n : ℕ) :
    PowExact ℓ (n + 1) (towerObj (LAdicSheaf.padicTower B X ℓ F) n) := by
  let R := etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1
  let eA : R.obj (LAdicSheaf.etaleLevel B X ℓ F n) ≅ towerObj (LAdicSheaf.padicTower B X ℓ F) n :=
    (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (p := ℓ) (n + 1))).app
      (F.level n)
  exact powExact_of_iso eA (PowExact.map R
    (zmodSheaf_nsmul_id X.1.smallEtaleTopology (ℓ ^ (n + 1)) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hF n))

/-! ### The exact sequences of `R^q f_!` on the levels -/

section LowerShriek

attribute [local instance] HasDerivedCategory.standard

variable {Y : Scheme.{u}} (f : X.1 ⟶ Y) (j : CompactificationOf (Over.mk f)) (F : LAdicSheaf B X ℓ)
  (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))

/-- The short exact sequence `0 → F_a → F_{a+b+1} → F_b → 0` of the levels of `F`. -/
abbrev LAdicSheaf.levelSES (a b : ℕ) : ShortComplex (EtaleModules.{u, 0} ℤ_[ℓ] X.1) :=
  ShortComplex.mk
    (verschiebungMap (LAdicSheaf.padicTower B X ℓ F)
      (LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebung (show a ≤ a + b + 1 by omega))
    (towerMap (LAdicSheaf.padicTower B X ℓ F) (show b ≤ a + b + 1 by omega))
    ((LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebungMap_towerMap_eq_zero a b _ rfl)

include hF in
/-- For an ℓ-adic sheaf with flat levels, the sequence `0 → F_a → F_{a+b+1} → F_b → 0` is short
exact. -/
theorem LAdicSheaf.levelSES_shortExact (a b : ℕ) :
    (LAdicSheaf.levelSES B X ℓ F a b).ShortExact :=
  (LAdicSheaf.padicTower_isStrict B X ℓ F).shortExact (LAdicSheaf.powExact_padicTower B X ℓ F hF)
    a b _ rfl

/-- The morphism `0 → F_{a+1} → F_{a+b+2} → F_b → 0` ⟶ `0 → F_a → F_{a+b+1} → F_b → 0` given by
the transitions. -/
def LAdicSheaf.levelSESMap (a b : ℕ) :
    LAdicSheaf.levelSES B X ℓ F (a + 1) b ⟶ LAdicSheaf.levelSES B X ℓ F a b where
  τ₁ := towerMap (LAdicSheaf.padicTower B X ℓ F) (Nat.le_succ a)
  τ₂ := towerMap (LAdicSheaf.padicTower B X ℓ F) (show a + b + 1 ≤ a + 1 + b + 1 by omega)
  τ₃ := 𝟙 _
  comm₁₂ := (LAdicSheaf.padicTower_isStrict B X ℓ F).isVerschiebung.towerMap_verschiebungMap
    (Nat.le_succ a) (show a + b + 1 ≤ a + 1 + b + 1 by omega) (show a ≤ a + b + 1 by omega)
    (show a + 1 ≤ a + 1 + b + 1 by omega) (by omega)
  comm₂₃ := by
    dsimp
    rw [Category.comp_id, towerMap_comp]

/-- **The exact sequences of `R^q f_!` and `R^{q+1} f_!` on the levels of a flat ℓ-adic sheaf**,
as data `CategoryTheory.LAdicTower.LESData` for the towers `n ↦ R^q f_! Fₙ` and
`n ↦ R^{q+1} f_! Fₙ`. -/
def LAdicSheaf.lowerShriekLESData (q : ℤ) :
    LESData (LAdicSheaf.padicTower B X ℓ F ⋙ lowerShriekHomology ℤ_[ℓ] f j q)
      (LAdicSheaf.padicTower B X ℓ F ⋙ lowerShriekHomology ℤ_[ℓ] f j (q + 1)) ℓ where
  vT n := (lowerShriekHomology ℤ_[ℓ] f j q).map
    ((LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebung n)
  vS n := (lowerShriekHomology ℤ_[ℓ] f j (q + 1)).map
    ((LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebung n)
  hvT := (LAdicSheaf.padicTower_isStrict B X ℓ F).isVerschiebung.map _
  hvS := (LAdicSheaf.padicTower_isStrict B X ℓ F).isVerschiebung.map _
  δ a b := singleHomologyδ (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
    (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) q (q + 1) rfl
  exactT a b m hm X' x hx := by
    subst hm
    obtain ⟨X'', π, hπ, y, hy⟩ := (singleHomology_exact₂ (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) q).exact_up_to_refinements x hx
    exact ⟨X'', π, hπ, y, by
      rw [hy]
      exact congrArg (y ≫ ·) (map_verschiebungMap (lowerShriekHomology ℤ_[ℓ] f j q)
        (LAdicSheaf.padicTower B X ℓ F) (LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebung
        (show a ≤ a + b + 1 by omega))⟩
  exactS a b m hm X' x hx := by
    subst hm
    obtain ⟨X'', π, hπ, y, hy⟩ := (singleHomology_exact₂ (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) (q + 1)).exact_up_to_refinements x hx
    exact ⟨X'', π, hπ, y, by
      rw [hy]
      exact congrArg (y ≫ ·) (map_verschiebungMap (lowerShriekHomology ℤ_[ℓ] f j (q + 1))
        (LAdicSheaf.padicTower B X ℓ F) (LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebung
        (show a ≤ a + b + 1 by omega))⟩
  towerMap_δ a b m hm := by
    subst hm
    exact singleHomology_map_comp_δ (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) q (q + 1) rfl
  exactδ a b m hm X' x hx := by
    subst hm
    exact (singleHomology_exact₃ (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) q (q + 1) rfl).exact_up_to_refinements x hx
  δ_verschiebungMap a b m hm := by
    subst hm
    rw [← map_verschiebungMap (lowerShriekHomology ℤ_[ℓ] f j (q + 1))
      (LAdicSheaf.padicTower B X ℓ F) (LAdicSheaf.padicTower_isStrict B X ℓ F).verschiebung]
    exact singleHomologyδ_comp_map (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) q (q + 1) rfl
  δ_towerMap a b := by
    have h := singleHomologyδ_naturality (derivedLowerShriek.{u, 0} f j ℤ_[ℓ])
      (LAdicSheaf.levelSESMap B X ℓ F a b) (LAdicSheaf.levelSES_shortExact B X ℓ F hF (a + 1) b)
      (LAdicSheaf.levelSES_shortExact B X ℓ F hF a b) q (q + 1) rfl
    dsimp [LAdicSheaf.levelSESMap] at h
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.symm

end LowerShriek

end Stacks.EtaleCohomology
