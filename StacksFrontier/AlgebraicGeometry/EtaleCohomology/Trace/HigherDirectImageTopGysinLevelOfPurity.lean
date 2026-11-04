module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphismShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LowerShriekGysinFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.CategoryTheory.Abelian.TowerStableImageLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOneOp

/-!
# The level form of the Gysin input for `R² g_! G`, from cohomological purity

Let `g : U ⟶ V` be smooth of relative dimension one over a finite field, `i : Z ⟶ U` a closed
immersion with `Z = V(f)` and `π = g ∘ i` finite étale, `j : U₀ ⟶ U` the open complement, and `G`
a lisse ℓ-adic sheaf on `U` with torsion-free model `G'`. The tower of the Gysin maps

`π_*(tw Z (i⁻¹ G'))ₙ ⟶ R² g_! G'ₙ`

(`Stacks.EtaleCohomology.lowerShriekGysinFamily`, the connecting map of the truncation triangle of
`R j_*(j⁻¹ G'ₙ)` carried by `Rg_!`, read through relative purity
`Stacks.EtaleCohomology.RelativeCurvePurityInput`) lands in the stable images of the tower
`n ↦ R² g_! G'ₙ`, hence defines a morphism `φ : π_*(tw Z (i⁻¹ G')) ⟶ R² g_! G` of ℓ-adic sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekHom`). Each Gysin map is an
epimorphism once `H²(Rg_!(R j_*(j⁻¹ H)))` vanishes for the locally constant `H`
(`Stacks.EtaleCohomology.LowerShriekPurityComplexVanishing`: on a geometric fibre `U_w̄` this is
`H²_c` of the affine curve `Ū_w̄ ∖ Z_w̄` with coefficients extended by zero), so `φ` is surjective
on every finite-level stalk. This gives the level input
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinLevelInput` of the Gysin input of the
Leray step of the reduction of the weight bound of Weil II to curves
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.LowerShriekPurityComplexVanishing`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.surjective_finiteLevelStalkMap_of_epi`.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageTopGysinLevelInput_of_purity`.
* `LAdicSheaf.higherDirectImageTopGysinMorphismInput_higherDirectImageShriekFamily`:
  the Gysin input for the family `Rʳ g_! G`, with the Tate twist
  `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneOp`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **The vanishing of `H²(Rg_!(R j_*(j⁻¹ H)))`** along the complement `j` of an étale divisor
`Z = V(f)` of a smooth relative curve `g : U ⟶ W`, `W` smooth over a field `k` with `ℓ`
invertible, `Z` meeting every irreducible component with two points of every geometric fibre,
for `H` locally constant of finite type of `ℤ/ℓⁿ⁺¹`-modules read as a sheaf of `ℤ_ℓ`-modules. -/
def LowerShriekPurityComplexVanishing (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (k : Type u) [Field k], IsUnit (ℓ : k) →
  ∀ (U W Z U₀ : Scheme.{u}) [IsNoetherian U] [IsNoetherian W] (pW : W ⟶ Spec (.of k))
    [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsAffineHom g]
    (jg : CompactificationOf (Over.mk g)) (i : Z ⟶ U) [IsClosedImmersion i] [IsFinite (i ≫ g)]
    [Etale (i ≫ g)] (f : Γ(U, ⊤)), Set.range i.base = U.zeroLocus {f} →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ W),
      ∀ C : Set (Limits.pullback g w : Scheme.{u}),
        C ∈ irreducibleComponents _ → (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
        (C ∩ (Limits.pullback.fst g w).base ⁻¹' Set.range i.base).Nonempty) →
  ∀ (j : U₀ ⟶ U) [IsOpenImmersion j], Set.range j.base = (Set.range i.base)ᶜ →
  ∀ (n : ℕ) (H : EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) U), lccModules U (ℓ ^ (n + 1)) H →
    IsZero ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} ℤ_[ℓ] W) 2).obj
      ((derivedLowerShriek.{u, 0} g jg ℤ_[ℓ]).obj ((purityComplex ℤ_[ℓ] j).obj
        ((etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) U).obj H))))

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

/-- **A morphism of ℓ-adic sheaves which is an epimorphism on the level `n`, read on Mathlib's
small étale site, is surjective on the level-`n` stalks.** -/
theorem LAdicSheaf.surjective_finiteLevelStalkMap_of_epi {X : B.Scheme} [IsNoetherian X.1]
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) (n : ℕ)
    (h : Epi ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicLevelMap φ n)))
    (s : GeometricPoint X.1) : Function.Surjective (finiteLevelStalkMap φ s n).hom := by
  have h1 : Epi (LAdicSheaf.padicLevelMap φ n) :=
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.epi_of_epi_map h
  have h2 : Epi (φ.app n) := by
    constructor
    intro Y a b hab
    let Φ := sheafCompose (SmallEtale.topology B X.1 X.property)
      (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (p := ℓ) (n + 1)))
    have hΦ : Φ.map a = Φ.map b := by
      refine h1.left_cancellation _ _ ?_
      show Φ.map (φ.app n) ≫ Φ.map a = Φ.map (φ.app n) ≫ Φ.map b
      rw [← Φ.map_comp, ← Φ.map_comp, hab]
    apply Sheaf.hom_ext
    ext U x
    exact (congrArg (fun t => (t.hom.app U).hom x) hΦ :)
  have h3 : Epi ((geometricPointSitePoint B X.1 X.property s).sheafFiber.map (φ.app n)) :=
    inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 h3

/-- **The level form of the Gysin input for `R² g_! G`, from relative purity**: the tower of Gysin
maps `π_*(tw Z (i⁻¹ G'))ₙ ⟶ R² g_! G'ₙ` (`Stacks.EtaleCohomology.lowerShriekGysinFamily`) lands in
the stable images and gives a morphism into `R² g_! G`, surjective on the finite-level stalks once
the Gysin maps are epimorphisms (`Stacks.EtaleCohomology.LowerShriekPurityComplexVanishing`). -/
theorem LAdicSheaf.higherDirectImageTopGysinLevelInput_of_purity
    (tw : ∀ (X : B.Scheme) [IsNoetherian X.1], LAdicSheaf.{u, u + 1} B X ℓ →
      LAdicSheaf.{u, u + 1} B X ℓ) (hPur : RelativeCurvePurityInput B ℓ tw)
    (hVan : LowerShriekPurityComplexVanishing.{u} ℓ) :
    LAdicSheaf.HigherDirectImageTopGysinLevelInput B ℓ tw := by
  intro k _ _ p e _ _ hcard hℓp U V Z _ _ _ g _ _ _ _ _ jg i _ π _ _ hπ f hZ hfib fV _ _ G hG
    hcond hA
  have := hcond.fst
  have hℓk : IsUnit (ℓ : k) := by
    refine isUnit_iff_ne_zero.2 fun h => hℓp ?_
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1
      ((CharP.cast_eq_zero_iff k p ℓ).1 h)).symm
  have hℓN : ∀ m : ℕ, IsUnit ((ℓ ^ (m + 1) : ℕ) : k) := fun m => by
    rw [Nat.cast_pow]
    exact hℓk.pow _
  have hmap : B.inclusion.map i ≫ B.inclusion.map g = B.inclusion.map π := by
    rw [← Functor.map_comp, hπ]
  have : IsFinite (B.inclusion.map i ≫ B.inclusion.map g) := hmap ▸ inferInstance
  have : Etale (B.inclusion.map i ≫ B.inclusion.map g) := hmap ▸ inferInstance
  have : IsFinite (B.inclusion.map (i ≫ g)) := by
    rw [hπ]
    infer_instance
  have : Etale (B.inclusion.map (i ≫ g)) := by
    rw [hπ]
    infer_instance
  have : CompactSpace (B.inclusion.obj V) := (inferInstance : CompactSpace V.1)
  have : IsLocallyNoetherian (B.inclusion.obj V) :=
    (inferInstance : IsNoetherian V.1).toIsLocallyNoetherian
  have : QuasiSeparatedSpace (B.inclusion.obj V) := IsLocallyNoetherian.quasiSeparatedSpace
  let G' := LAdicSheaf.flatModel B ℓ G
  have hG' : G'.IsLisse := LAdicSheaf.isLisse_flatModel B ℓ G hG
  let M := tw Z (LAdicSheaf.inverseImage i G')
  have hAf := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse _ hA
  let W₀ := (B.inclusion.obj U).basicOpen f
  let j := W₀.ι
  have hj : Set.range j.base = (Set.range (B.inclusion.map i).base)ᶜ := by
    rw [Scheme.Opens.range_ι, hZ, Scheme.zeroLocus_singleton, compl_compl]
  obtain ⟨eP1⟩ := hPur.2 k hℓk U V Z W₀ fV g i f hZ j hj G' hG'
  have hS := fun m : ℕ => hPur.1 k (ℓ ^ (m + 1)) (hℓN m) U.1 V.1 Z.1 W₀ fV (B.inclusion.map g)
    (B.inclusion.map i) f hZ j hj
  let TG := LAdicSheaf.padicTower B U ℓ G'
  let TM := LAdicSheaf.padicTower B Z ℓ M
  let eL : ∀ m : ℕ, (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (m + 1)) U.1).obj
      (LAdicSheaf.etaleLevel B U ℓ G' m) ≅ TG.obj (op m) := fun m =>
    (sheafEquivRestrictScalarsIso B U.1 U.property (PadicInt.toZModPow (p := ℓ) (m + 1))).app
      (G'.level m)
  have hlcc : ∀ m : ℕ, lccModules U.1 (ℓ ^ (m + 1)) (LAdicSheaf.etaleLevel B U ℓ G' m) :=
    fun m => (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B U _ _).2
      (LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse G' hG' m)
  have hunit : ∀ a : ℕᵒᵖ,
      IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} ℤ_[ℓ] j).unit.app (TG.obj a)) := by
    rintro ⟨m⟩
    have h0 := isIso_unit_restrictScalars (PadicInt.toZModPow (p := ℓ) (m + 1)) j _
      ((hS m).1 _ (hlcc m))
    have hn := (etaleModuleRestrictionDirectImageAdj.{u, 0} ℤ_[ℓ] j).unit.naturality (eL m).hom
    have : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} ℤ_[ℓ] j).unit.app
        ((etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (m + 1)) U.1).obj
          (LAdicSheaf.etaleLevel B U ℓ G' m))) := h0
    exact IsIso.of_isIso_fac_left hn
  have h2 : ∀ (m q : ℕ), 2 ≤ q →
      IsZero (((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).rightDerived q).obj
        ((etaleModuleRestriction.{u, 0} ℤ_[ℓ] j).obj (TG.obj (op m)))) := fun m q hq =>
    IsZero.of_iso (isZero_rightDerived_directImage_restrictScalars _ j _ q
        ((hS m).2.1 _ (hlcc m) q hq))
      (((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).rightDerived q).mapIso
        ((etaleModuleRestriction.{u, 0} ℤ_[ℓ] j).mapIso (eL m))).symm
  have hX : ∀ m : ℕ, IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} (B.inclusion.map g) jg ℤ_[ℓ]).obj
        ((purityComplex ℤ_[ℓ] j).obj (TG.obj (op m))))) := fun m =>
    IsZero.of_iso (hVan k hℓk U.1 V.1 Z.1 W₀ fV (B.inclusion.map g) jg (B.inclusion.map i) f hZ
        hfib j hj m _ (hlcc m))
      ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
        ((derivedLowerShriek.{u, 0} (B.inclusion.map g) jg ℤ_[ℓ]).mapIso
          ((purityComplex ℤ_[ℓ] j).mapIso (eL m)))).symm
  have hTM : ∀ a : ℕᵒᵖ, torsionEtaleModules ℤ_[ℓ] Z.1 (TM.obj a) := fun a =>
    ⟨ℓ ^ (a.unop + 1), pow_pos (Fact.out : ℓ.Prime).pos _,
      LAdicSheaf.padicTower_annihilated B Z ℓ M a.unop⟩
  let α₀ := lowerShriekGysinFamily ℤ_[ℓ] (B.inclusion.map i) j (B.inclusion.map g) jg TG TM eP1
    hTM hunit
  let α : LAdicSheaf.padicTower B V ℓ (SmallEtale.LAdicSheaf.directImage π M hAf) ⟶
      LAdicSheaf.lowerShriekTower B ℓ g jg G ((2 : ℕ) : ℤ) :=
    (LAdicSheaf.padicTowerFiniteEtaleDirectImageIso ℓ π M hAf).hom ≫
      Functor.whiskerLeft TM (eqToHom (congrArg (etaleModuleDirectImage.{u, 0} ℤ_[ℓ]) hmap.symm)) ≫
      α₀
  have hαepi : ∀ m : ℕ, Epi (α.app (op m)) := fun m => by
    have := epi_lowerShriekGysinFamily_app ℤ_[ℓ] (B.inclusion.map i) j (B.inclusion.map g) jg
      TG TM eP1 hTM hunit (op m) (h2 m) (hX m)
    simp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    exact epi_comp' inferInstance (epi_comp' inferInstance this)
  let D := LAdicSheaf.lowerShriekTowerLES B ℓ g jg G ((2 : ℕ) : ℤ)
  have hP := (LAdicSheaf.padicTower_isStrict B V ℓ (SmallEtale.LAdicSheaf.directImage π M hAf)).epi
  refine ⟨LAdicSheaf.higherDirectImageShriekHom g jg G 2 hcond (D.liftStableImage hP α),
    fun w m => LAdicSheaf.surjective_finiteLevelStalkMap_of_epi B ℓ _ m ?_ _⟩
  have hfac := LAdicSheaf.sheafEquiv_map_padicLevelMap_higherDirectImageShriekHom g jg G 2 hcond
    (D.liftStableImage hP α) m
  have hι := D.liftStableImageApp_ι hP α m
  have : Epi (D.stableImageι.app (op m)) := epi_of_epi_fac hι (h := α.app (op m))
  have : IsIso (D.stableImageι.app (op m)) := isIso_of_mono_of_epi _
  have : Epi (D.liftStableImageApp hP α m) :=
    (epi_comp_iff_of_isIso _ (D.stableImageι.app (op m))).1 (hι ▸ hαepi m)
  let E := (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G 2 hcond).app (op m)
  rw [(Iso.eq_comp_inv E).2 hfac]
  exact epi_comp' this (IsIso.epi_of_iso E.inv)

/-- **The Gysin morphism of `R² g_!` along étale divisors, for the family `Rʳ g_! G`**
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`), from relative
purity with the Tate twist `Stacks.EtaleCohomology.LAdicSheaf.twistNegOneOp` and the vanishing of
`H²(Rg_!(R j_*(j⁻¹ H)))`; the trace property of the twist is
`Stacks.EtaleCohomology.LAdicSheaf.lAdicTwistInput_twistNegOneOp`. -/
theorem LAdicSheaf.higherDirectImageTopGysinMorphismInput_higherDirectImageShriekFamily
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ))
    (hVan : LowerShriekPurityComplexVanishing.{u} ℓ) :
    LAdicSheaf.HigherDirectImageTopGysinMorphismInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
  LAdicSheaf.higherDirectImageTopGysinMorphismInput_of_levelInput B ℓ _
    (LAdicSheaf.lAdicTwistInput_twistNegOneOp B ℓ)
    (LAdicSheaf.higherDirectImageTopGysinLevelInput_of_purity B ℓ _ hPur hVan)

end Stacks.EtaleCohomology

end
