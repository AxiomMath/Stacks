module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ZModDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ZeroSystemLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequenceSerre

/-!
# `Rʳ g_! G` is lisse where the `Rʳ g_! G'ₙ` are locally constant

Let `G'` be the flat model of an ℓ-adic sheaf `G` on `U` and `g : U ⟶ W` with a
compactification. The ℓ-adic sheaf `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`) has as levels the stable images
`Hₙ = Im(R^r g_! G'_{n+β+1} → R^r g_! G'ₙ)`, read as sheaves of `ℤ/ℓⁿ⁺¹`-modules on the small
étale site of Stacks 021B. If every `Rʳ g_! G'ₘ` is locally constant of finite type, then so is
every `Hₙ`: finite type locally constant sheaves form a weak Serre class (Tag 093U (3)), and an
image is the kernel of a cokernel. Local constancy passes to the site of Stacks 021B, then to the
underlying abelian sheaf, and then to the sheaf of `ℤ/ℓⁿ⁺¹`-modules
(`Stacks.ConstantSheaf.isLocallyConstant_of_isLocallyConstant_forget₂_zmod`). When the hypotheses
of the construction fail, `Rʳ g_! G` is `0`, which is lisse.

This is the conclusion of the lisse-locus step in the reduction of the Weil II weight bound to
curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek`: `Rʳ g_! G` is lisse as soon
  as every `Rʳ g_! G'ₘ` is locally constant of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory.LAdicTower

universe u


namespace Stacks.EtaleCohomology

/-! ### Stable images of locally constant sheaves -/

section StableImage

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} {T S : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X}
  (D : LESData T S ℓ)
  [IsNoetherianObject (towerObj S 0)]

/-- **Stable images of finite type locally constant sheaves are finite type locally constant**:
`Hₙ = Im(T_{n+β+1} ⟶ Tₙ)` is the kernel of the cokernel of a map between such sheaves, and these
form a weak Serre class (Tag 093U (3)). -/
theorem isFiniteTypeLocallyConstant_stableImageTower
    (hT : ∀ m, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
      X.smallEtaleTopology (towerObj T m)) (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
      X.smallEtaleTopology (towerObj D.stableImageTower n) := by
  let P : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] X) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      X.smallEtaleTopology ℤ_[ℓ]
  let f := towerMap T (show n ≤ n + D.shift + 1 by omega)
  exact P.prop_of_iso (imageSubobjectIso f ≪≫ (Abelian.imageIsoImage f).symm).symm
    (P.prop_kernel _ (hT n) (P.prop_cokernel _ (hT _) (hT n)))

end StableImage

/-! ### From `ℤ_ℓ`-local constancy on Mathlib's site to the levels of an ℓ-adic sheaf -/

section Transport

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.1] (ℓ : ℕ) [Fact ℓ.Prime]
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

omit [AlgebraicGeometry.IsNoetherian X.1]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- A sheaf of `ℤ_ℓ`-modules on Mathlib's small étale site which is locally constant of finite type
has, on the small étale site of Stacks 021B, a locally constant underlying abelian sheaf. -/
theorem isLocallyConstant_padicForget {P : EtaleModules.{u, 0} ℤ_[ℓ] X.1}
    (hP : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
      X.1.smallEtaleTopology P) :
    Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B X.1 X.property)
      ((padicForget B X ℓ).obj P) := by
  constructor
  intro U
  obtain ⟨I, V, f, hcov, hc⟩ :=
    (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B X ℤ_[ℓ] P).2 hP U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, -, ⟨e⟩⟩ := hc i
  let J := SmallEtale.topology B X.1 X.property
  have : Sheaf.IsConstant (J.over (V i)) ((J.overPullback (ModuleCat.{u + 1} ℤ_[ℓ]) (V i)).obj
      ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj P)) :=
    Sheaf.isConstant_of_iso _ e.symm
  have : (J.over (V i)).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}) :=
    ModuleSheaf.preservesSheafification_forget₂.{u + 1} ℤ_[ℓ] _
  exact Sheaf.isConstant_congr _ (Iso.refl ((sheafCompose (J.over (V i))
    (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).obj
      ((J.overPullback (ModuleCat.{u + 1} ℤ_[ℓ]) (V i)).obj
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj P))))

omit [AlgebraicGeometry.IsNoetherian X.1]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The level `n` of the ℓ-adic sheaf of a strict tower is locally constant** as soon as `Hₙ` is
locally constant of finite type on Mathlib's small étale site. -/
theorem isLocallyConstant_strictTowerLevel (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1)
    (hH : IsStrict H ℓ) (n : ℕ)
    (hn : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] X.1.smallEtaleTopology
      (towerObj H n)) :
    Stacks.ConstantSheaf.IsLocallyConstant (SmallEtale.topology B X.1 X.property)
      (strictTowerLevel H hH n) := by
  let J := SmallEtale.topology B X.1 X.property
  have : ∀ V, (J.over V).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}) := fun V =>
    ModuleSheaf.preservesSheafification_forget₂.{u + 1} _ _
  refine Stacks.ConstantSheaf.isLocallyConstant_of_isLocallyConstant_forget₂_zmod (ℓ ^ (n + 1)) J
    _ ?_
  have := isLocallyConstant_padicForget B X ℓ hn
  exact Stacks.ConstantSheaf.isLocallyConstant_congr J (strictTowerLevelIso H hH n).symm

end Transport

/-! ### `Rʳ g_! G` is lisse -/

section Lisse

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
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)]
  (jg : CompactificationOf (Over.mk (B.inclusion.map g)))

/-- **`Rʳ g_! G` is lisse as soon as every `Rʳ g_! G'ₘ` is locally constant of finite type**,
`G'` the flat model of `G`. Its levels are the stable images of the `Rʳ g_! G'ₘ`, which are then
locally constant of finite type, and local constancy descends to the levels as sheaves of
`ℤ/ℓⁿ⁺¹`-modules on Stacks 021B. If the construction's hypotheses fail, `Rʳ g_! G = 0`. -/
theorem LAdicSheaf.isLisse_higherDirectImageShriek (G : LAdicSheaf B U ℓ) (r : ℕ)
    (hT : ∀ m, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
      W.1.smallEtaleTopology (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) m)) :
    (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r).IsLisse := by
  unfold LAdicSheaf.higherDirectImageShriek
  split_ifs with h
  · have := h.fst
    intro n
    exact isLocallyConstant_strictTowerLevel B W ℓ _
      (LAdicSheaf.isStrict_lowerShriekStableImage B ℓ g jg G r) n
      (isFiniteTypeLocallyConstant_stableImageTower
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r) hT n)
  · exact LAdicSheaf.isLisse_zeroSystem B W ℓ

section Devissage

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **Dévissage along the flat model.** If every `Rˢ g_! G'₀` is locally constant of finite type,
then so is every `Rʳ g_! G'ₘ`: the short exact sequences `0 → G'₀ → G'ₘ₊₁ → G'ₘ → 0` of the flat
model and the long exact sequence of `R g_!` place `Rʳ g_! G'ₘ₊₁` in a five-term exact sequence
whose other terms are locally constant of finite type, and these form a weak Serre class. -/
theorem LAdicSheaf.isFiniteTypeLocallyConstant_lowerShriekTower (G : LAdicSheaf B U ℓ)
    (h0 : ∀ s : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ]
      W.1.smallEtaleTopology ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg s).obj
        (towerObj (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ G)) 0)))
    (r : ℤ) (m : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] W.1.smallEtaleTopology
      (towerObj (LAdicSheaf.lowerShriekTower B ℓ g jg G r) m) := by
  let P : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] W.1) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      W.1.smallEtaleTopology ℤ_[ℓ]
  let F := LAdicSheaf.flatModel B ℓ G
  exact prop_singleHomology_of_shortExact_tower
    (derivedLowerShriek.{u, 0} (B.inclusion.map g) jg ℤ_[ℓ]) P
    (towerObj (LAdicSheaf.padicTower B U ℓ F))
    (fun n => LAdicSheaf.levelSES B U ℓ F 0 n)
    (fun n => LAdicSheaf.levelSES_shortExact B U ℓ F
      (LAdicSheaf.powExact_etaleLevel_flatModel B ℓ G) 0 n)
    (fun _ => Iso.refl _)
    (fun n => eqToIso (show towerObj (LAdicSheaf.padicTower B U ℓ F) (0 + n + 1) = _ by
      rw [Nat.zero_add]))
    (fun _ => Iso.refl _) h0 m r

end Devissage

end Lisse

end Stacks.EtaleCohomology
