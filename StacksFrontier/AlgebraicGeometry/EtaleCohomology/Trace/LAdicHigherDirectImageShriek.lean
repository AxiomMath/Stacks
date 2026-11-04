module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLowerShriekTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTorsionFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLimitWeights

/-!
# The ℓ-adic sheaf `R^r g_! G`

Let `g : U ⟶ W` be a morphism of the big étale site, separated of finite type, with a
compactification `j_g`, and let `G` be an ℓ-adic sheaf on `U`. Replace `G` by its torsion-free
model `G' = ℓᴺ G` (`Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModel`, isogenous to `G`, with
flat levels). The sheaves `Tₘ = R^r g_! G'ₘ` (`Stacks.EtaleCohomology.lowerShriekHomology` with
`ℤ_ℓ`-coefficients) form a tower which is not ℓ-adic: it is only Artin–Rees ℓ-adic. When
`R^{r+1} g_! G'₀` is a Noetherian object the tower satisfies the Mittag-Leffler condition with a
uniform shift (`CategoryTheory.LAdicTower.LESData.mittagLeffler`), and its stable images form a
strict ℓ-adic tower; when these are constructible they are the levels of an ℓ-adic sheaf, the
*higher direct image with proper support* `R^r g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`; it is `0` when the hypotheses fail).

Its compactly supported cohomology is computed by the tower `T`: for `W` separated of finite type
over a finite field `k` with a compactification `j_W`,

`H^p_c(W_k̄, R^r g_! G ⊗ ℚ_ℓ) ≅ (lim_m H^p_c(W_k̄, R^r g_! G'ₘ)) ⊗ ℚ_ℓ`,

compatibly with the geometric Frobenius
(`Stacks.EtaleCohomology.LAdicSheaf.isCharpolyNormMixedOfWeightLE_higherDirectImageShriek_iff`):
the stable image tower and `T` are pro-isomorphic, so the towers of their `H^p_c` have isomorphic
limits. This is the ℓ-adic sheaf of the Leray step of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 1.1.2 and 3.3) to curves.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTower`: the tower `n ↦ R^r g_! G'ₙ`.
* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageShriekCondition`: the finiteness hypotheses.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`: the ℓ-adic sheaf `R^r g_! G`.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerHigherDirectImageShriekIso`: its tower of levels
  is the stable image tower.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so does `R^r g_!` here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- The levels of a tower obtained from a strict tower by an additive functor are killed by the
powers of `ℓ`. -/
theorem towerObj_comp_annihilated {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (P : ℕᵒᵖ ⥤ C) (Φ : C ⥤ D) [Φ.Additive] {ℓ : ℕ}
    (hP : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj P n) = 0) (n : ℕ) :
    ℓ ^ (n + 1) • 𝟙 (towerObj (P ⋙ Φ) n) = 0 := by
  show ℓ ^ (n + 1) • 𝟙 (Φ.obj (towerObj P n)) = 0
  rw [← Φ.map_id, ← Φ.map_nsmul, hP n, Φ.map_zero]

/-- **The stable image tower and `T` have isomorphic limits after any functor**: they are
pro-isomorphic. -/
theorem _root_.CategoryTheory.LAdicTower.LESData.isIso_limMap_whiskerRight_stableImageι
    {C D' : Type*} [Category* C] [Abelian C] [Category* D'] {T S : ℕᵒᵖ ⥤ C} {ℓ : ℕ}
    (L : LESData T S ℓ) [IsNoetherianObject (towerObj S 0)] (Φ : C ⥤ D')
    [HasLimit (L.stableImageTower ⋙ Φ)] [HasLimit (T ⋙ Φ)] :
    IsIso (limMap (Functor.whiskerRight L.stableImageι Φ)) :=
  isIso_limMap_of_proInverse (Functor.whiskerRight L.stableImageι Φ) (fun n => n + L.shift + 1)
    (fun n => by omega) (fun n n' h => by dsimp; omega)
    (fun n => Φ.map (L.stableImageRetraction n))
    (fun n n' h => by
      show Φ.map (towerMap T _) ≫ Φ.map (L.stableImageRetraction n) =
        Φ.map (L.stableImageRetraction n') ≫ Φ.map (towerMap L.stableImageTower h)
      rw [← Φ.map_comp, ← Φ.map_comp, L.towerMap_stableImageRetraction h])
    (fun n => by
      show Φ.map (L.stableImageRetraction n) ≫ Φ.map (L.stableImageι.app (op n)) =
        Φ.map (towerMap T _)
      rw [← Φ.map_comp, L.stableImageRetraction_ι])
    (fun n => by
      show Φ.map (L.stableImageι.app (op (n + L.shift + 1))) ≫
          Φ.map (L.stableImageRetraction n) = Φ.map (towerMap L.stableImageTower _)
      rw [← Φ.map_comp, L.stableImageι_stableImageRetraction])

/-- The absolute-value bound on characteristic roots is invariant under an equivariant
isomorphism. -/
theorem isCharpolyNormMixedOfWeightLE_iff_of_iso {ℓ : ℕ} [Fact ℓ.Prime]
    {M N : ModuleCat.{u + 1} ℚ_[ℓ]} [FiniteDimensional ℚ_[ℓ] M] [FiniteDimensional ℚ_[ℓ] N]
    (e : M ≅ N) (φM : M ⟶ M) (φN : N ⟶ N) (h : φM ≫ e.hom = e.hom ≫ φN)
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b φM.hom ↔ IsCharpolyNormMixedOfWeightLE q' ι b φN.hom := by
  let L : M ≃ₗ[ℚ_[ℓ]] N := e.toLinearEquiv
  have hcomm : ∀ v, L (φM.hom v) = φN.hom (L v) := fun v =>
    congrArg (fun t => t.hom v) h
  exact ⟨fun hM => hM.of_surjective (p := L.toLinearMap) hcomm L.surjective,
    fun hN => hN.of_injective (j := L.toLinearMap) hcomm L.injective⟩

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

/-- The torsion-free model `ℓᴺ G` of `G`, `N` its torsion bound: isogenous to `G`, with flat
levels. -/
abbrev LAdicSheaf.flatModel (G : LAdicSheaf B U ℓ) : LAdicSheaf B U ℓ :=
  LAdicSheaf.torsionFreeModel G (LAdicSheaf.torsionBound G)

/-- The level `G'ₙ` of the flat model `G'` of `G` satisfies `PowExact ℓ (n + 1)`. -/
theorem LAdicSheaf.powExact_etaleLevel_flatModel (G : LAdicSheaf B U ℓ) (n : ℕ) :
    PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B U ℓ (LAdicSheaf.flatModel B ℓ G) n) :=
  LAdicSheaf.powExact_etaleLevel_torsionFreeModel B U ℓ G le_rfl n

/-- **The tower `n ↦ R^r g_! G'ₙ`** of the flat model `G'` of `G`, with `ℤ_ℓ`-coefficients. -/
abbrev LAdicSheaf.lowerShriekTower (G : LAdicSheaf B U ℓ) (r : ℤ) :
    ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] W.1 :=
  LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G) ⋙
    lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r

/-- The exact sequences of `R^r g_!` and `R^{r+1} g_!` on the levels of the flat model. -/
abbrev LAdicSheaf.lowerShriekTowerLES (G : LAdicSheaf B U ℓ) (r : ℤ) :
    LESData (LAdicSheaf.lowerShriekTower B ℓ g jg G r)
      (LAdicSheaf.lowerShriekTower B ℓ g jg G (r + 1)) ℓ :=
  LAdicSheaf.lowerShriekLESData B U ℓ (B.inclusion.map g) jg (LAdicSheaf.flatModel B ℓ G)
    (LAdicSheaf.powExact_etaleLevel_flatModel B ℓ G) r

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The level `R^r g_! G'ₙ` of the tower is killed by `ℓ ^ (n + 1)`. -/
theorem LAdicSheaf.lowerShriekTower_annihilated (G : LAdicSheaf B U ℓ) (r : ℤ) (n : ℕ) :
    ℓ ^ (n + 1) • 𝟙 (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) n) = 0 :=
  towerObj_comp_annihilated _ _ (LAdicSheaf.padicTower_annihilated B U ℓ _) n

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The stable images of `n ↦ R^r g_! G'ₙ` form a strict ℓ-adic tower. -/
theorem LAdicSheaf.isStrict_lowerShriekStableImage (G : LAdicSheaf B U ℓ) (r : ℤ)
    [IsNoetherianObject (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G (r + 1)) 0)] :
    IsStrict (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower ℓ :=
  IsStrict.of_isCokernel
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImage_annihilated
      (LAdicSheaf.lowerShriekTower_annihilated B ℓ g jg G r))
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTransition_isCokernel
      (LAdicSheaf.lowerShriekTower_annihilated B ℓ g jg G r))

/-- **The hypotheses under which `R^r g_! G` is an ℓ-adic sheaf**: `R^{r+1} g_! G'₀` is a
Noetherian object, and the stable images of `n ↦ R^r g_! G'ₙ`, read as sheaves of
`ℤ/ℓⁿ⁺¹ℤ`-modules on Stacks 021B, are constructible. -/
def LAdicSheaf.HigherDirectImageShriekCondition (G : LAdicSheaf B U ℓ) (r : ℕ) : Prop :=
  ∃ _ : IsNoetherianObject (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G ((r : ℤ) + 1)) 0),
    ∀ n, IsConstructibleModuleSheaf B W (ZMod (ℓ ^ (n + 1)))
      (strictTowerLevel _ (LAdicSheaf.isStrict_lowerShriekStableImage B ℓ g jg G r) n)

open Classical in
/-- **The ℓ-adic sheaf `R^r g_! G`**: the ℓ-adic sheaf of the stable images of the tower
`n ↦ R^r g_! G'ₙ` of the flat model `G'` of `G`, under the hypotheses
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageShriekCondition`, and `0` otherwise. -/
def LAdicSheaf.higherDirectImageShriek (G : LAdicSheaf B U ℓ) (r : ℕ) : LAdicSheaf B W ℓ :=
  if h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r then
    haveI := h.fst
    LAdicSheaf.ofStrictTower _ (LAdicSheaf.isStrict_lowerShriekStableImage B ℓ g jg G r) h.snd
  else LAdicSheaf.zeroSystem B W ℓ

/-- **The tower of levels of `R^r g_! G` is the tower of stable images of `n ↦ R^r g_! G'ₙ`.** -/
def LAdicSheaf.padicTowerHigherDirectImageShriekIso (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) :
    haveI := h.fst
    LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) ≅
      (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower :=
  haveI := h.fst
  eqToIso (congrArg (LAdicSheaf.padicTower B W ℓ) (dif_pos h)) ≪≫
    LAdicSheaf.padicTowerOfStrictTowerIso _ _ h.snd

/-! ### Compactly supported cohomology of `R^r g_! G` -/

section Cohomology

variable {k : Type u} [Field k] [Fintype k] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
  [QuasiCompact fW] [IsSeparated fW] (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`H^p_c(W_k̄, R^r g_! G) ⊗ ℚ_ℓ` is the rational limit of `n ↦ H^p_c(W_k̄, R^r g_! G'ₙ)`.** -/
def LAdicSheaf.higherDirectImageShriekCohomologyIso (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (i : ℤ) :
    (rationalLim.{u + 1} (ℓ := ℓ)).obj
        (LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) ⋙
          compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i) ≅
      (rationalLim.{u + 1} (ℓ := ℓ)).obj
        (LAdicSheaf.lowerShriekTower B ℓ g jg G r ⋙
          compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i) :=
  haveI := h.fst
  haveI := (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).isIso_limMap_whiskerRight_stableImageι
    (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i)
  (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
      (Functor.isoWhiskerRight (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h)
        (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i)) ≪≫
    asIso ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (limMap (Functor.whiskerRight (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageι
        (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i))))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] in
/-- The comparison carries the geometric Frobenius of the levels of `R^r g_! G` to the geometric
Frobenius of the tower `n ↦ R^r g_! G'ₙ`. -/
theorem LAdicSheaf.higherDirectImageShriekCohomologyIso_hom_frobenius (G : LAdicSheaf B U ℓ)
    (r : ℕ) (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (i : ℤ) :
    (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
        (LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r))
        (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard i)) ≫
      (LAdicSheaf.higherDirectImageShriekCohomologyIso B ℓ g jg fW jW kbar G r h i).hom =
    (LAdicSheaf.higherDirectImageShriekCohomologyIso B ℓ g jg fW jW kbar G r h i).hom ≫
      (rationalLim.{u + 1} (ℓ := ℓ)).map (Functor.whiskerLeft
        (LAdicSheaf.lowerShriekTower B ℓ g jg G r)
        (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard i)) := by
  have := h.fst
  show _ ≫ (rationalLim.{u + 1} (ℓ := ℓ)).map _ ≫ (rationalLim.{u + 1} (ℓ := ℓ)).map _ =
    ((rationalLim.{u + 1} (ℓ := ℓ)).map _ ≫ (rationalLim.{u + 1} (ℓ := ℓ)).map _) ≫ _
  simp only [← Functor.map_comp, Category.assoc]
  congr 1
  have key : ∀ {P P' : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] W.1} (α : P ⟶ P'),
      Functor.whiskerLeft P (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard i) ≫
        Functor.whiskerRight α (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i) =
      Functor.whiskerRight α (compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i) ≫
        Functor.whiskerLeft P' (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard i) :=
    fun α => NatTrans.ext (funext fun n =>
      ((compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard i).naturality (α.app n)).symm)
  rw [Functor.isoWhiskerRight_hom, ← Category.assoc, key, Category.assoc, key]

/-- `H^p_c(W_k̄, R^r g_! G ⊗ ℚ_ℓ)` finite dimensional makes the rational limit of
`n ↦ H^p_c(W_k̄, R^r g_! G'ₙ)` finite dimensional. -/
theorem LAdicSheaf.finiteDimensional_rationalLim_lowerShriekTower (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (i : ℤ)
    [hR : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B W ℓ
      fW jW kbar (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) i)] :
    FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.lowerShriekTower B ℓ g jg G r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i)) := by
  have : FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B W ℓ fW jW kbar
        (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) i)) := hR
  exact LinearEquiv.finiteDimensional (((rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.padicTowerCohomologyIso B W ℓ fW jW kbar _ i)).symm ≪≫
      LAdicSheaf.higherDirectImageShriekCohomologyIso B ℓ g jg fW jW kbar G r h i).toLinearEquiv

/-- **The weight bound on `H^p_c(W_k̄, R^r g_! G ⊗ ℚ_ℓ)` is the weight bound on the rational limit
of `n ↦ H^p_c(W_k̄, R^r g_! G'ₙ)`**, for the canonical geometric Frobenius on both. -/
theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_higherDirectImageShriek_iff
    (G : LAdicSheaf B U ℓ) (r : ℕ) (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r)
    (i : ℤ) [hR : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B W ℓ fW jW kbar (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) i)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim.{u + 1} (ℓ := ℓ)).obj
      (LAdicSheaf.lowerShriekTower B ℓ g jg G r ⋙
        compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar i))]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
        B W ℓ fW jW kbar p q hcard (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) i).hom ↔
      IsCharpolyNormMixedOfWeightLE q' ι b ((rationalLim.{u + 1} (ℓ := ℓ)).map
        (Functor.whiskerLeft (LAdicSheaf.lowerShriekTower B ℓ g jg G r)
          (compactSupportSheafFrobenius ℤ_[ℓ] fW jW kbar p q hcard i))).hom := by
  have := LinearEquiv.finiteDimensional
    (LAdicSheaf.higherDirectImageShriekCohomologyIso B ℓ g jg fW jW kbar G r h i).symm.toLinearEquiv
  exact (LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff
    B W ℓ fW jW kbar p q hcard _ i).trans (isCharpolyNormMixedOfWeightLE_iff_of_iso
      (LAdicSheaf.higherDirectImageShriekCohomologyIso B ℓ g jg fW jW kbar G r h i) _ _
      (LAdicSheaf.higherDirectImageShriekCohomologyIso_hom_frobenius B ℓ g jg fW jW kbar p q hcard
        G r h i))

end Cohomology

end Stacks.EtaleCohomology
