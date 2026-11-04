module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTowerLevelTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModelLevelZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModelInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericTrivializationFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.EtaleModuleFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic

/-!
# The lisse locus of the ℓ-adic higher direct images `Rʳ g_! G`

Let `g : U ⟶ W` be a separated morphism of finite type of Noetherian schemes, `W` reduced and
nonempty, and `G` an ℓ-adic sheaf on `U`. There is a nonempty open `V ⊆ W` such that for every
open `V' ⊆ V`, with `g' : U' ⟶ V'` the base change of `g` and any compactification `jg'` of `g'`,
every `Rʳ g'_! (G|_{U'})` (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`) is lisse.
This is the lisse-locus input of the induction step of the Weil II weight bound
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), granted the constructibility of the
cohomology sheaves of `Rf_!` ([Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0),
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput`).

The proof: let `Q = G'₀` be the level zero of the flat model `G'` of `G`, a constructible sheaf
killed by `ℓ`, and `jg` a compactification of `g` (Nagata, Tag 0F41). The `Rˢ g_! Q` vanish
outside `[0, N]` (Tag 0G2A) and are constructible (Tag 0GL0), so finitely many of them are all
locally constant of finite type over one nonempty open `V` (generic local constancy of
constructible sheaves on a reduced scheme,
`AlgebraicGeometry.exists_isOpenImmersion_forall_isFiniteTypeLocallyConstant`). Over `V' ⊆ V`:

* the level zero of the flat model of `G|_{U'}` is `Q|_{U'}`: the torsion bounds of `G` and of
  `G|_{U'}` are chosen independently, but the level zero of the torsion-free model `ℓᴹ G` does
  not depend on `M` beyond the torsion bound
  (`Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelLevelZeroIsoOfLE`), and it commutes with
  inverse image (`Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelInverseImageLevelZeroIso`);
* `Rˢ g'_! (Q|_{U'}) ≅ (Rˢ g_! Q)|_{V'}` by proper base change for `Rf_!` (Tag 0F7L) and the
  independence of the compactification (Tag 0F7I),
  `Stacks.EtaleCohomology.nonempty_lowerShriekHomology_inverseImage_iso`;
* so every `Rˢ g'_! (Q|_{U'})` is locally constant of finite type, then by dévissage every
  `Rʳ g'_! G''ₘ` of the flat model `G''` of `G|_{U'}`
  (`Stacks.EtaleCohomology.LAdicSheaf.isFiniteTypeLocallyConstant_lowerShriekTower`), and
  `Rʳ g'_! (G|_{U'})` is lisse
  (`Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek`).

The lisse hypothesis on `G` is not used.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.flatModelInverseImageLevelZeroIso`: the level zero of the
  flat model commutes with inverse image.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek`:
  the lisse-locus input for `Rʳ g_!`, granted Tag 0GL0.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {ℓ : ℕ}
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
  [Fact ℓ.Prime]

namespace LAdicSheaf

/-! ### The level zero of the flat model -/

section LevelZero

variable {X Y : B.Scheme} [IsNoetherian X.1] [IsNoetherian Y.1]

/-- **`(ℓᴹ G)₀ ≅ (ℓᴺ G)₀` for `torsionBound G ≤ N ≤ M`**, from
`Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelLevelZeroIsoOfLE` with `M = N + k`. -/
def torsionFreeModelLevelZeroIso (G : LAdicSheaf.{u, u + 1} B X ℓ) {N M : ℕ}
    (hN : torsionBound G ≤ N) (hNM : N ≤ M) :
    (torsionFreeModel G M).level 0 ≅ (torsionFreeModel G N).level 0 :=
  eqToIso (congrArg (fun K => (torsionFreeModel G K).level 0) (Nat.add_sub_of_le hNM).symm) ≪≫
    torsionFreeModelLevelZeroIsoOfLE G hN (M - N)

/-- **The level zero of the flat model commutes with inverse image**: for `f : X ⟶ Y` and an
ℓ-adic sheaf `G` on `Y`, the level zero of the flat model of `f⁻¹ G` is the inverse image of the
level zero of the flat model of `G`. The torsion bounds of `G` and of `f⁻¹ G` are chosen
independently; both levels zero are that of `ℓᴹ`, `M` the larger bound. -/
def flatModelInverseImageLevelZeroIso (f : X ⟶ Y) (G : LAdicSheaf.{u, u + 1} B Y ℓ) :
    (flatModel B ℓ (SmallEtale.LAdicSheaf.inverseImage f G)).level 0 ≅
      (SmallEtale.LAdicSheaf.inverseImage f (flatModel B ℓ G)).level 0 :=
  (torsionFreeModelLevelZeroIso (SmallEtale.LAdicSheaf.inverseImage f G) le_rfl
      (le_max_right (torsionBound G) _)).symm ≪≫
    torsionFreeModelInverseImageLevelZeroIso f G _ ≪≫
    (SmallEtale.LAdicSheaf.levelPullback f 0).mapIso
      (torsionFreeModelLevelZeroIso G le_rfl (le_max_left _ _))

end LevelZero

/-! ### The levels as sheaves of `ℤ_ℓ`-modules -/

section Levels

variable {X : B.Scheme} [IsNoetherian X.1]

/-- An isomorphism of the levels `n` of two ℓ-adic sheaves is an isomorphism of their levels `n`
read as sheaves of `ℤ_ℓ`-modules on Mathlib's small étale site. -/
def padicTowerObjIsoOfLevelIso {F₁ F₂ : LAdicSheaf.{u, u + 1} B X ℓ} (n : ℕ)
    (e : F₁.level n ≅ F₂.level n) :
    (LAdicSheaf.padicTower B X ℓ F₁).obj (op n) ≅ (LAdicSheaf.padicTower B X ℓ F₂).obj (op n) :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.mapIso
    ((sheafCompose (SmallEtale.topology B X.1 X.property)
      (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (n + 1)))).mapIso e)

end Levels

end LAdicSheaf

/-! ### Local constancy along a restriction to an open -/

section Restriction

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **Local constancy over `V` restricts to `V' ⟶ V`**, read on Mathlib's small étale site: if
the inverse image along `o : V ⟶ W` of a sheaf `P` of `Λ`-modules on `W`, transported to the
site of Stacks 021B, is locally constant of finite type, then so is the inverse image of `P`
along `jV' ≫ o` on Mathlib's small étale site of `V'`. -/
theorem isFiniteTypeLocallyConstant_etaleModuleInverseImage_comp {Λ : Type} [Ring Λ]
    {V' V W : B.Scheme} (jV' : V' ⟶ V) (o : V ⟶ W) (P : EtaleModules.{u, 0} Λ W.1)
    (hP : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B V.1 V.property)
      (((AlgebraicGeometry.smallEtaleBaseChange B o).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B W.1 W.property) (SmallEtale.topology B V.1 V.property)).obj
          ((etaleModulesToSmallEtale B W Λ).obj P))) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} Λ V'.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map (jV' ≫ o))).obj P) := by
  have h₁ := Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    (etaleModulesToSmallEtalePullbackIso B Λ o P).symm hP
  have h₂ := isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ jV' _ h₁
  have h₃ := Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    (etaleModulesToSmallEtalePullbackIso B Λ jV'
      ((etaleModuleInverseImage.{u, 0} Λ (B.inclusion.map o)).obj P)).symm h₂
  have h₄ := (isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B V' Λ _).1 h₃
  let Pr : ObjectProperty (EtaleModules.{u, 0} Λ V'.1) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      V'.1.smallEtaleTopology Λ
  rw [Functor.map_comp]
  exact Pr.prop_of_iso
    ((etaleModuleInverseImageCompIso Λ (B.inclusion.map jV') (B.inclusion.map o)).app P).symm h₄

end Restriction

/-! ### The lisse locus -/

section LisseLocus

attribute [local instance] HasDerivedCategory.standard

/-- A Noetherian object of the big étale site is compact and quasi-separated as a scheme. -/
private theorem compactSpace_and_quasiSeparatedSpace_inclusion_obj (X : B.Scheme)
    [IsNoetherian X.1] :
    CompactSpace (B.inclusion.obj X) ∧ QuasiSeparatedSpace (B.inclusion.obj X) :=
  have hN : IsNoetherian (B.inclusion.obj X) := ‹IsNoetherian X.1›
  ⟨hN.toCompactSpace, @IsLocallyNoetherian.quasiSeparatedSpace _ hN.toIsLocallyNoetherian⟩

variable (B ℓ) in
/-- **The lisse locus of the `Rʳ g_! G`** (Tag 0GL0 and its ℓ-adic form, for the reduction of the
Weil II weight bound to curves, [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), granted
the constructibility of the cohomology sheaves of `Rf_!` (Tag 0GL0,
`Stacks.EtaleCohomology.LowerShriekConstructibilityInput`): for `g : U ⟶ W` with `W` nonempty and
reduced, there is a nonempty open `V ⊆ W` over every open `V' ⊆ V` of which every
`Rʳ g'_! (G|_{U'})` is lisse, `g'` the base change of `g` with any compactification. -/
theorem LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek
    (hC : LowerShriekConstructibilityInput B) :
    LAdicSheaf.HigherDirectImageLisseLocusInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) := by
  intro U W _ _ _ g _ _ _ G _ hW
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_inclusion_obj W
  obtain ⟨jg, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace (B.inclusion.map g)
  let F := LAdicSheaf.flatModel B ℓ G
  let Q := (LAdicSheaf.padicTower B U ℓ F).obj (op 0)
  have hm : 0 < ℓ ^ (0 + 1) := pow_pos (Fact.out : ℓ.Prime).pos _
  have hQ : ℓ ^ (0 + 1) • 𝟙 Q = 0 := LAdicSheaf.pow_nsmul_id_padicTower_obj B ℓ F 0
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ_[ℓ] U.1) 0
  have hSQ : ℓ ^ (0 + 1) • 𝟙 (S.obj Q) = 0 := by
    rw [← S.map_id, ← Functor.map_nsmul, hQ, Functor.map_zero]
  let Φ := derivedLowerShriek.{u, 0} (B.inclusion.map g) jg ℤ_[ℓ]
  let P : ℤ → EtaleModules.{u, 0} ℤ_[ℓ] W.1 := fun s =>
    (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg s).obj Q
  let eP : ∀ s, P s ≅ (DerivedCategory.Plus.homologyFunctor _ s).obj (Φ.obj (S.obj Q)) := fun s =>
    (DerivedCategory.Plus.homologyFunctor _ s).mapIso
      (Φ.mapIso ((StacksDraft.DerivedSectionsComparison.singlePlusQIso
        (EtaleModules.{u, 0} ℤ_[ℓ] U.1)).app Q))
  have hPc : ∀ s, IsBigSiteConstructibleEtaleModule B W ℤ_[ℓ] (P s) := fun s =>
    IsBigSiteConstructibleEtaleModule.of_iso B ℤ_[ℓ] (eP s).symm
      (hC (B.inclusion.map g) jg ℤ_[ℓ] Q (LAdicSheaf.isConstructibleEtaleModule_padicTower F 0)
        (isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero Q _ hm hQ) s)
  obtain ⟨N, hN, -⟩ := exists_bounded_derivedLowerShriek ℤ_[ℓ] (B.inclusion.map g) jg
  obtain ⟨-, -, hGE, hLE⟩ := hN (S.obj Q) (isTorsionPlus_of_nsmul_id_eq_zero _ _ hm hSQ)
  have hZ : ∀ s : ℤ, s < 0 ∨ (N : ℤ) < s → IsZero (P s) := by
    intro s hs
    refine IsZero.of_iso ?_ (eP s)
    rcases hs with hs | hs
    · have := hGE 0 (inferInstanceAs
        (((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ_[ℓ] U.1) 0).obj Q).IsGE 0))
      exact DerivedCategory.isZero_of_isGE (DerivedCategory.Plus.ι.obj (Φ.obj (S.obj Q))) 0 s hs
    · have := hLE 0 (inferInstanceAs
        (((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} ℤ_[ℓ] U.1) 0).obj Q).IsLE 0))
      exact DerivedCategory.isZero_of_isLE (DerivedCategory.Plus.ι.obj (Φ.obj (S.obj Q))) (0 + N) s
        (by omega)
  obtain ⟨V, o, ho, hV, hlc⟩ := exists_isOpenImmersion_forall_isFiniteTypeLocallyConstant B ℤ_[ℓ]
    (Finset.range (N + 1)) W (fun n : ℕ => (etaleModulesToSmallEtale B W ℤ_[ℓ]).obj (P n))
    (fun n _ => hPc n)
  refine ⟨V, o, ho, hV, ?_⟩
  intro V' U' _ _ jV' jU g' _ _ _ jg' _ hpb r
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_inclusion_obj V'
  let Pr : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] V'.1) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      V'.1.smallEtaleTopology ℤ_[ℓ]
  refine LAdicSheaf.isLisse_higherDirectImageShriek B ℓ g' jg' _ r
    (LAdicSheaf.isFiniteTypeLocallyConstant_lowerShriekTower B ℓ g' jg' _ (fun s => ?_) r)
  have hres :
      Pr ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (jV' ≫ o))).obj (P s)) := by
    by_cases hs : s < 0 ∨ (N : ℤ) < s
    · have : (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
          (B.inclusion.map (jV' ≫ o))).PreservesZeroMorphisms :=
        have := (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ]
          (B.inclusion.map (jV' ≫ o))).isLeftAdjoint
        Functor.preservesZeroMorphisms_of_isLeftAdjoint _
      exact Pr.prop_of_isZero (Functor.map_isZero _ (hZ s hs))
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
      exact isFiniteTypeLocallyConstant_etaleModuleInverseImage_comp jV' o (P n)
        (hlc n (Finset.mem_range.2 (by omega)))
  obtain ⟨e⟩ := nonempty_lowerShriekHomology_inverseImage_iso ℤ_[ℓ] hpb jg jg' Q _ hm hQ s
  let e₀ : towerObj (LAdicSheaf.padicTower B U' ℓ
      (LAdicSheaf.flatModel B ℓ (SmallEtale.LAdicSheaf.inverseImage jU G))) 0 ≅
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj Q :=
    LAdicSheaf.padicTowerObjIsoOfLevelIso 0 (LAdicSheaf.flatModelInverseImageLevelZeroIso jU G) ≪≫
      ((LAdicSheaf.padicTowerInverseImageIso B ℓ jU F).app (op 0)).symm
  exact Pr.prop_of_iso
    ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).mapIso e₀ ≪≫ e).symm hres

end LisseLocus

end Stacks.EtaleCohomology
