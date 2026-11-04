module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelUnitStalkMathlibComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PunctualSectionsCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekEnd

/-!
# `R^r g_! G` has no punctual sections when the levels of `R^r g_!` have no `H⁰_c`

Let `g : U ⟶ W` be a morphism of the big étale site with a compactification and `G` an ℓ-adic
sheaf on `U`, and let `Tₙ = R^r g_! G'ₙ` be the tower of the flat model `G'` of `G`
(`Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTower`). The levels of the ℓ-adic sheaf
`R^r g_! G` (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`) embed into the `Tₙ`:
they are the stable images of the tower when `R^r g_! G` is defined, and `0` otherwise
(`LAdicSheaf.isZero_compactSupportSheafCohomology_padicLevel_higherDirectImageShriek`).

Hence, for `W` over a finite field `k` with algebraic closure `k̄`, a nonempty open `j : V ⟶ W`
with finite reduced closed complement `Z` and a point `y ∈ Z` with finite residue field: if
`H⁰_c(W_k̄, Tₙ) = 0` for all `n`, the stalks at `ȳ` of the units
`(R^r g_! G)ₙ → j_* j⁻¹ (R^r g_! G)ₙ` on the bounded sites
(`Stacks.EtaleCohomology.levelUnitStalkMap`) are injective: `H⁰_c` is left exact, so the levels
of `R^r g_! G` have no `H⁰_c` either, and a sheaf without compactly supported sections has no
sections supported at `ȳ`
(`Stacks.EtaleCohomology.injective_sheafFiber_unit_of_isZero_compactSupportSheafCohomology`),
read on the bounded sites through `Stacks.EtaleCohomology.levelUnitStalkMap_eq_zero_imp`.

This is the absence of punctual sections of `R¹pr₂! K` in Laumon's degeneration argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), where `H⁰_c(W_k̄, R¹pr₂! K'ₙ)` is the
Leray edge `H¹_c(𝔸²_k̄, K'ₙ)`.

## Main results

* `LAdicSheaf.isZero_compactSupportSheafCohomology_padicLevel_higherDirectImageShriek`.
* `LAdicSheaf.levelUnitStalkMap_higherDirectImageShriek_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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

/-- A level of a zero ℓ-adic sheaf, read as a sheaf of `ℤ_ℓ`-modules, is zero. -/
theorem LAdicSheaf.isZero_padicLevel_of_isZero {F : LAdicSheaf B W ℓ} (hF : IsZero F) (n : ℕ) :
    IsZero (LAdicSheaf.padicLevel B W ℓ F n) := by
  have h0 : LAdicSheaf.padicLevelMap (0 : F ⟶ F) n = 0 := by
    have h := LAdicSheaf.padicLevelMap_add (0 : F ⟶ F) 0 n
    rw [add_zero] at h
    exact add_eq_left.1 h.symm
  rw [IsZero.iff_id_eq_zero, ← LAdicSheaf.padicLevelMap_id, hF.eq_of_src (𝟙 F) 0, h0]

variable {k : Type u} [Field k] [Fintype k] (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW]
  [QuasiCompact fW] [IsSeparated fW] (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  {Z : Scheme.{u}} (iZ : Z ⟶ W.1) [IsClosedImmersion iZ] [IsReduced Z] [IsFinite (iZ ≫ fW)]
  {V : B.Scheme} [IsNoetherian V.1] (jV : V ⟶ W) [IsOpenImmersion (B.inclusion.map jV)]

omit [Fintype k] in
omit [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [IsAlgClosure k kbar] in
/-- **The levels of `R^r g_! G` have no `H⁰_c` when those of `n ↦ R^r g_! G'ₙ` have none**:
they are the stable images of the tower when `R^r g_! G` is defined (and `H⁰_c` is left exact),
and `0` otherwise. -/
theorem LAdicSheaf.isZero_compactSupportSheafCohomology_padicLevel_higherDirectImageShriek
    [Finite k] (G : LAdicSheaf B U ℓ) (r : ℕ)
    (hT : ∀ n, IsZero ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).obj
      (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) n))) (n : ℕ) :
    IsZero ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).obj
      ((SmallEtale.sheafEquiv B W.1 W.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) n))) := by
  have := Fintype.ofFinite k
  by_cases h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r
  · have := h.fst
    let φ : (towerObj (LAdicSheaf.padicTower B W ℓ
        (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)) n : EtaleModules.{u, 0} ℤ_[ℓ] W.1) ⟶
        towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) n :=
      (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom.app (op n) ≫
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageι.app (op n)
    have : Mono φ := inferInstance
    have := mono_compactSupportSheafCohomology_zero_map ℤ_[ℓ] fW jW kbar φ
    have hz := IsZero.of_mono ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).map φ) (hT n)
    exact hz
  · have hT0 := Stacks.CategoryTheory.isZero_equivalence_functor_obj
      (SmallEtale.sheafEquiv B W.1 W.2 (ModuleCat.{u + 1} ℤ_[ℓ]))
      (LAdicSheaf.isZero_padicLevel_of_isZero B ℓ
        (LAdicSheaf.isZero_higherDirectImageShriek B ℓ g jg G r h) n)
    let φ : (SmallEtale.sheafEquiv B W.1 W.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) n) ⟶
        towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) n := hT0.to_ _
    have : Mono φ := ⟨fun a b _ => hT0.eq_of_tgt a b⟩
    have := mono_compactSupportSheafCohomology_zero_map ℤ_[ℓ] fW jW kbar φ
    exact IsZero.of_mono ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).map φ) (hT n)

omit [Fintype k] in
include iZ in
/-- **`R^r g_! G` has no punctual sections when the levels of `R^r g_!` have no `H⁰_c`**: if
`H⁰_c(W_k̄, R^r g_! G'ₙ) = 0` for all `n`, then for a nonempty open `j : V ⟶ W` with finite
reduced closed complement `Z` and `y ∈ Z` with finite residue field, the stalks at `ȳ` of the
units `(R^r g_! G)ₙ → j_* j⁻¹ (R^r g_! G)ₙ` are injective. -/
theorem LAdicSheaf.levelUnitStalkMap_higherDirectImageShriek_eq_zero (G : LAdicSheaf B U ℓ) (r : ℕ)
    [Finite k] (hij : Set.range (B.inclusion.map jV).base = (Set.range iZ.base)ᶜ) (y : W.1)
    (hy : y ∈ Set.range iZ.base) [Finite (W.1.residueField y)]
    (hT : ∀ n, IsZero ((compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar 0).obj
      (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) n)))
    (n : ℕ) (w : finiteLevelStalk B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)
      (Stacks.Frobenius.geometricPointAt W.1 y) n)
    (hw : (levelUnitStalkMap jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)
      (Stacks.Frobenius.geometricPointAt W.1 y) n).hom w = 0) : w = 0 :=
  have := Fintype.ofFinite k
  levelUnitStalkMap_eq_zero_imp B ℓ _ _ n
    (injective_sheafFiber_unit_of_isZero_compactSupportSheafCohomology ℤ_[ℓ] fW jW kbar iZ
      (B.inclusion.map jV) hij y hy _
      (LAdicSheaf.isZero_compactSupportSheafCohomology_padicLevel_higherDirectImageShriek B ℓ g jg
        fW jW kbar G r hT n)) w hw

end Stacks.EtaleCohomology

end
