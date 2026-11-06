module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekBaseChangeIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.CategoryTheory.Abelian.TowerStableImageIsogeny

/-!
# The levels of `R^r g_! K` and `R^r` of the levels, up to a uniform isogeny, after base change

Let `g : U ⟶ W` be separated of finite type with a compactification `j_g`, `K` an ℓ-adic sheaf
on `U`, and `R^r g_! G` the ℓ-adic sheaf of
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`: its levels are the stable images
`Hₙ ⊆ R^r g_! G'ₙ` of the tower of the flat model `G'` of `G`, read back on the small étale site of
Stacks 021B. This file compares the levels `Hₙ` with the sheaves `R^r g_! Kₙ` of the levels of `K`
themselves, up to an isogeny whose exponent does not depend on `n`, and after base change to an
open of the target:

* `Hₙ ⊆ R^r g_! G'ₙ` is an isogeny of exponent `β + 1`, `β` the Mittag-Leffler shift
  (`CategoryTheory.LAdicTower.LESData.stableImageIsogeny`): `ℓ^{β+1} R^r g_! G'ₙ ⊆ Hₙ` because the
  obstruction to lifting lies in `R^{r+1} g_! G'_β`, killed by `ℓ^{β+1}`
  (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekToLowerShriekTower`);
* `G' = ℓᴺ G` is isogenous to `G` with exponent `N`
  (`Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerToLevels`);
* proper base change ([Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)) along a cartesian
  square `U' = U ×_W V`, through the isogeny between the flat models of `K` and of `K|_{U'}`
  (`Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerBaseChangeInv`).

Composing, for `g' : U' ⟶ V` the base change of `g` along `jV : V ⟶ W`, the tower of levels of
`R^r g'_!(K|_{U'})` and the tower `n ↦ jV⁻¹ R^r g_! Kₙ` are isogenous with a single exponent `c`,
compatibly with the endomorphisms induced by endomorphisms of `K`, in particular with the action of
the coefficients of an `O`-sheaf
(`Stacks.EtaleCohomology.LAdicSheaf.exists_higherDirectImageShriek_levelIsogeny`,
`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_higherDirectImageShriek_levelIsogeny`).
The hypotheses of `R^r g'_!` hold unconditionally by Stacks 0GL0
(`Stacks.EtaleCohomology.lowerShriekConstructibilityInput`).

For Laumon's family, `g = pr₂ : 𝔸²_{k'} ⟶ 𝔸¹_{k'}` and `K` the Fourier family sheaf, this compares
Laumon's `G = R¹g'_!(K|_{U'})` with the restriction to `V'` of `R¹pr₂!` of the levels of `K`, that
is of the Fourier transforms of the levels, as needed for the irreducibility of the Fourier
transform in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekToLowerShriekTower`,
  `Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek`.
* `Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerToLevels`,
  `Stacks.EtaleCohomology.LAdicSheaf.levelsToLowerShriekTower`.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekLevelBaseChange`,
  `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekLevelBaseChange_comp_inv`,
  `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv_comp`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_higherDirectImageShriek_levelIsogeny`.
* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_higherDirectImageShriek_levelIsogeny`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek`, hence `R^r g_!`, lives in the standard model
`HasDerivedCategory.standard` of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits

section Levels

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

/-! ### The levels of `R^r g_! G` and the tower `n ↦ R^r g_! G'ₙ` -/

/-- **The levels of `R^r g_! G` inside the tower `n ↦ R^r g_! G'ₙ`**: the identification of the
levels with the stable images, followed by their inclusion. -/
def LAdicSheaf.higherDirectImageShriekToLowerShriekTower (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) :
    LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) ⟶
      LAdicSheaf.lowerShriekTower B ℓ g jg G r :=
  haveI := h.fst
  (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom ≫
    (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageι

/-- **The tower `n ↦ R^r g_! G'ₙ` into the levels of `R^r g_! G`**: multiplication by `ℓ^{β+1}`,
`β` the Mittag-Leffler shift, factored through the stable images. -/
def LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) :
    LAdicSheaf.lowerShriekTower B ℓ g jg G r ⟶
      LAdicSheaf.padicTower B W ℓ (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) :=
  haveI := h.fst
  (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageIsogeny
      (LAdicSheaf.lowerShriekTower_annihilated B ℓ g jg G ((r : ℤ) + 1)) ≫
    (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).inv

/-- The exponent `β + 1` of the isogeny between the levels of `R^r g_! G` and the tower
`n ↦ R^r g_! G'ₙ`, `β` the Mittag-Leffler shift. -/
def LAdicSheaf.higherDirectImageShriekLevelExponent (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) : ℕ :=
  haveI := h.fst
  (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).shift + 1

/-- The inclusion of the levels of `R^r g_! G` into `n ↦ R^r g_! G'ₙ`, followed by the map back,
is multiplication by `ℓ^{β+1}`. -/
theorem LAdicSheaf.higherDirectImageShriekToLowerShriekTower_comp (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) :
    LAdicSheaf.higherDirectImageShriekToLowerShriekTower B ℓ g jg G r h ≫
        LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek B ℓ g jg G r h =
      ℓ ^ LAdicSheaf.higherDirectImageShriekLevelExponent B ℓ g jg G r h • 𝟙 _ := by
  have := h.fst
  rw [LAdicSheaf.higherDirectImageShriekToLowerShriekTower,
    LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek, Category.assoc,
    LESData.ι_stableImageIsogeny_assoc, Preadditive.nsmul_comp, Category.id_comp,
    Preadditive.comp_nsmul, Iso.hom_inv_id]
  rfl

/-- The map from `n ↦ R^r g_! G'ₙ` into the levels of `R^r g_! G`, followed by the inclusion, is
multiplication by `ℓ^{β+1}`. -/
theorem LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek_comp (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) :
    LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek B ℓ g jg G r h ≫
        LAdicSheaf.higherDirectImageShriekToLowerShriekTower B ℓ g jg G r h =
      ℓ ^ LAdicSheaf.higherDirectImageShriekLevelExponent B ℓ g jg G r h • 𝟙 _ := by
  have := h.fst
  rw [LAdicSheaf.higherDirectImageShriekToLowerShriekTower,
    LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek, Category.assoc, Iso.inv_hom_id_assoc,
    LESData.stableImageIsogeny_ι]
  rfl

/-- The inclusion of the levels of `R^r g_! G` commutes with the endomorphisms induced by an
endomorphism of `G`. -/
theorem LAdicSheaf.higherDirectImageShriekToLowerShriekTower_naturality (G : LAdicSheaf B U ℓ)
    (r : ℕ) (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (φ : G ⟶ G) :
    LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ) ≫
        LAdicSheaf.higherDirectImageShriekToLowerShriekTower B ℓ g jg G r h =
      LAdicSheaf.higherDirectImageShriekToLowerShriekTower B ℓ g jg G r h ≫
        LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ := by
  have := h.fst
  rw [LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
    LAdicSheaf.padicTowerMap_homOfPadicTower, LAdicSheaf.higherDirectImageShriekToLowerShriekTower]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, LESData.stableImageMap_ι]

/-- The isogeny into the levels of `R^r g_! G` commutes with the endomorphisms induced by an
endomorphism of `G`. -/
theorem LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek_naturality (G : LAdicSheaf B U ℓ)
    (r : ℕ) (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (φ : G ⟶ G) :
    LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ ≫
        LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek B ℓ g jg G r h =
      LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek B ℓ g jg G r h ≫
        LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ) := by
  have := h.fst
  rw [LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
    LAdicSheaf.padicTowerMap_homOfPadicTower, LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek,
    ← Category.assoc, LESData.stableImageIsogeny_naturality _ _ _ _
      (LESData.stableImageMap_ι _ _)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-! ### The flat model and the levels -/

/-- **`R^r g_!` of the flat model into `R^r g_!` of the levels**, through `ℓᴺ G ⟶ G`. -/
def LAdicSheaf.lowerShriekTowerToLevels (G : LAdicSheaf B U ℓ) (r : ℤ) :
    LAdicSheaf.lowerShriekTower B ℓ g jg G r ⟶
      LAdicSheaf.padicTower B U ℓ G ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r :=
  Functor.whiskerRight
    (LAdicSheaf.padicTowerMap (LAdicSheaf.fromTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r)

/-- **`R^r g_!` of the levels into `R^r g_!` of the flat model**, through `G ⟶ ℓᴺ G`. -/
def LAdicSheaf.levelsToLowerShriekTower (G : LAdicSheaf B U ℓ) (r : ℤ) :
    LAdicSheaf.padicTower B U ℓ G ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r ⟶
      LAdicSheaf.lowerShriekTower B ℓ g jg G r :=
  Functor.whiskerRight
    (LAdicSheaf.padicTowerMap (LAdicSheaf.toTorsionFreeModel G (LAdicSheaf.torsionBound G)))
    (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r)

/-- Whiskering on the right by an additive functor preserves composites equal to `k • 𝟙`. -/
private theorem whiskerRight_comp_eq_nsmul_id {J C D : Type*} [Category* J] [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] {F G : J ⥤ C} (α : F ⟶ G) (β : G ⟶ F)
    (Φ : C ⥤ D) [Φ.Additive] (k : ℕ) (h : α ≫ β = k • 𝟙 F) :
    Functor.whiskerRight α Φ ≫ Functor.whiskerRight β Φ = k • 𝟙 _ := by
  rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_nsmul_of_additive,
    Functor.whiskerRight_id']

/-- Whiskering on the right by a functor preserves commuting squares of natural transformations. -/
private theorem whiskerRight_comp_eq_comp {J C D : Type*} [Category* J] [Category* C]
    [Category* D] {F₁ F₂ F₃ F₄ : J ⥤ C} {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₄} {γ : F₁ ⟶ F₃}
    {δ : F₃ ⟶ F₄} (Φ : C ⥤ D) (h : α ≫ β = γ ≫ δ) :
    Functor.whiskerRight α Φ ≫ Functor.whiskerRight β Φ =
      Functor.whiskerRight γ Φ ≫ Functor.whiskerRight δ Φ := by
  rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_comp]

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- `R^r g_!` of `ℓᴺ G ⟶ G` followed by `R^r g_!` of `G ⟶ ℓᴺ G` is multiplication by `ℓᴺ`. -/
theorem LAdicSheaf.lowerShriekTowerToLevels_comp (G : LAdicSheaf B U ℓ) (r : ℤ) :
    LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg G r ≫
        LAdicSheaf.levelsToLowerShriekTower B ℓ g jg G r =
      ℓ ^ LAdicSheaf.torsionBound G • 𝟙 _ := by
  refine whiskerRight_comp_eq_nsmul_id _ _ _ _ ?_
  rw [← LAdicSheaf.padicTowerMap_comp, LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel,
    LAdicSheaf.padicTowerMap_nsmul, LAdicSheaf.padicTowerMap_id]

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- `R^r g_!` of `G ⟶ ℓᴺ G` followed by `R^r g_!` of `ℓᴺ G ⟶ G` is multiplication by `ℓᴺ`. -/
theorem LAdicSheaf.levelsToLowerShriekTower_comp (G : LAdicSheaf B U ℓ) (r : ℤ) :
    LAdicSheaf.levelsToLowerShriekTower B ℓ g jg G r ≫
        LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg G r =
      ℓ ^ LAdicSheaf.torsionBound G • 𝟙 _ := by
  refine whiskerRight_comp_eq_nsmul_id _ _ _ _ ?_
  rw [← LAdicSheaf.padicTowerMap_comp, LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel,
    LAdicSheaf.padicTowerMap_nsmul, LAdicSheaf.padicTowerMap_id]

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The map from `R^r g_!` of the flat model to `R^r g_!` of the levels commutes with the
endomorphisms induced by an endomorphism of `G`. -/
theorem LAdicSheaf.lowerShriekTowerToLevels_naturality (G : LAdicSheaf B U ℓ) (r : ℤ)
    (φ : G ⟶ G) :
    LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ ≫
      LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg G r =
      LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg G r ≫
        Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) := by
  rw [LAdicSheaf.lowerShriekTowerToLevels, LAdicSheaf.lowerShriekTowerEnd,
    ← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, ← LAdicSheaf.padicTowerMap_comp,
    ← LAdicSheaf.padicTowerMap_comp, LAdicSheaf.torsionFreeModelMap_comp_fromTorsionFreeModel]

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The map from `R^r g_!` of the levels to `R^r g_!` of the flat model commutes with the
endomorphisms induced by an endomorphism of `G`. -/
theorem LAdicSheaf.levelsToLowerShriekTower_naturality (G : LAdicSheaf B U ℓ) (r : ℤ)
    (φ : G ⟶ G) :
    Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ≫
        LAdicSheaf.levelsToLowerShriekTower B ℓ g jg G r =
      LAdicSheaf.levelsToLowerShriekTower B ℓ g jg G r ≫
        LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ := by
  rw [LAdicSheaf.levelsToLowerShriekTower, LAdicSheaf.lowerShriekTowerEnd,
    ← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp, ← LAdicSheaf.padicTowerMap_comp,
    ← LAdicSheaf.padicTowerMap_comp, LAdicSheaf.toTorsionFreeModel_comp_torsionFreeModelMap]

end Levels

section BaseChange

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
  {U W U' V : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] [IsNoetherian U'.1]
  [IsNoetherian V.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (g' : U' ⟶ V) [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
  [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
  (jU : U' ⟶ U) (jV : V ⟶ W)
  (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
    (B.inclusion.map jV))
  (K : LAdicSheaf.{u, u + 1} B U ℓ)

/-! ### The base change map of the towers in the other direction and endomorphisms -/

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **The base change map `R^r g'_!(K|_{U'})' ⟶ jV⁻¹ R^r g_! K'` of the towers commutes with the
endomorphisms induced by `K ⟶ K`.** -/
theorem LAdicSheaf.lowerShriekTowerBaseChangeInv_naturality (φ : K ⟶ K) (r : ℤ) :
    LAdicSheaf.lowerShriekTowerEnd B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
        (LAdicSheaf.inverseImageMap jU φ) ≫
      LAdicSheaf.lowerShriekTowerBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r =
    LAdicSheaf.lowerShriekTowerBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r ≫
      Functor.whiskerRight (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg K r φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) := by
  have hc : ∀ {F₁ F₂ F₃ : LAdicSheaf.{u, u + 1} B U ℓ} (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃),
      LAdicSheaf.inverseImageMap jU a ≫ LAdicSheaf.inverseImageMap jU b =
        LAdicSheaf.inverseImageMap jU (a ≫ b) :=
    fun a b => ((LAdicSheaf.inverseImageFunctor jU).map_comp a b).symm
  have hsheaf : LAdicSheaf.torsionFreeModelMap (LAdicSheaf.inverseImageMap jU φ)
        (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
      LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K)) =
    (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))) ≫
      LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)) := by
    rw [← Category.assoc, LAdicSheaf.torsionFreeModelMap_comp_fromTorsionFreeModel,
      Category.assoc, Category.assoc, hc, hc,
      LAdicSheaf.toTorsionFreeModel_comp_torsionFreeModelMap]
  have hiso : LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K))) ≫
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).inv =
    (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).inv ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      LAdicSheaf.padicTowerInverseImageIso_hom_naturality B ℓ jU, Iso.inv_hom_id_assoc]
  have htower : LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap
        (LAdicSheaf.inverseImageMap jU φ)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))) ≫
      LAdicSheaf.padicTowerMap (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))) ≫
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).inv =
    LAdicSheaf.padicTowerMap (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))) ≫
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).inv ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)) := by
    rw [← Category.assoc, ← LAdicSheaf.padicTowerMap_comp, hsheaf, LAdicSheaf.padicTowerMap_comp,
      Category.assoc, hiso]
  have he : Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      (LAdicSheaf.lowerShriekTowerBaseChangeIso B ℓ g jg g' jg' jU jV hpb K r).hom =
    (LAdicSheaf.lowerShriekTowerBaseChangeIso B ℓ g jg g' jg' jU jV hpb K r).hom ≫
      Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
    exact (ObjectProperty.liftWhiskerIso_inv_naturality (IsLPowerTorsion ℓ U.1)
      (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ K))
      (fun m => ⟨m.unop + 1, LAdicSheaf.padicTower_annihilated B U ℓ _ m.unop⟩)
      (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
      (lowerShriekHomologyTorsionBaseChangeIso B ℓ g jg g' jg' jU jV hpb r)).symm
  have hw : Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.torsionFreeModelMap
        (LAdicSheaf.inverseImageMap jU φ) (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU
        (LAdicSheaf.flatModel B ℓ K)).inv (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) =
    Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerInverseImageIso B ℓ jU
        (LAdicSheaf.flatModel B ℓ K)).inv (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
      Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap
        (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound K)))
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)))
        (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) :=
    by
      simp only [← Functor.whiskerRight_comp]
      rw [htower]
      simp only [Functor.whiskerRight_comp]
      rfl
  rw [LAdicSheaf.lowerShriekTowerBaseChangeInv, LAdicSheaf.lowerShriekTowerEnd,
    LAdicSheaf.lowerShriekTowerEnd, reassoc_of% hw]
  simp only [Category.assoc]
  rw [he]
  rfl

/-! ### The levels of `R^r g'_!(K|_{U'})` and `jV⁻¹ R^r g_!` of the levels of `K` -/

/-- **The levels of `R^r g'_!(K|_{U'})` into `n ↦ jV⁻¹ R^r g_! Kₙ`**: the inclusion of the stable
images, proper base change (Tag 0F7L) through the flat models, and the isogeny from the flat model
of `K` to `K`. -/
def LAdicSheaf.higherDirectImageShriekLevelBaseChange (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) :
    LAdicSheaf.padicTower B V ℓ
        (LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) ⟶
      (LAdicSheaf.padicTower B U ℓ K ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) :=
  LAdicSheaf.higherDirectImageShriekToLowerShriekTower B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
      h ≫
    LAdicSheaf.lowerShriekTowerBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r ≫
    Functor.whiskerRight (LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg K r)
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV))

/-- **`n ↦ jV⁻¹ R^r g_! Kₙ` into the levels of `R^r g'_!(K|_{U'})`**: the isogeny from `K` to its
flat model, proper base change (Tag 0F7L) through the flat models, and the factorisation through
the stable images. -/
def LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) :
    (LAdicSheaf.padicTower B U ℓ K ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) ⟶
      LAdicSheaf.padicTower B V ℓ
        (LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) :=
  Functor.whiskerRight (LAdicSheaf.levelsToLowerShriekTower B ℓ g jg K r)
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
    LAdicSheaf.lowerShriekTowerBaseChange B ℓ g jg g' jg' jU jV hpb K r ≫
    LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K)
      r h

/-- The exponent of the isogeny between the levels of `R^r g'_!(K|_{U'})` and
`n ↦ jV⁻¹ R^r g_! Kₙ`: the Mittag-Leffler exponent, the exponents `N + N'` of the base change and
the exponent `N` of the flat model of `K`. -/
def LAdicSheaf.higherDirectImageShriekLevelBaseChangeExponent (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) :
    ℕ :=
  LAdicSheaf.higherDirectImageShriekLevelExponent B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r h +
    (LAdicSheaf.torsionBound K + LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) +
    LAdicSheaf.torsionBound K

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- The comparison of the levels of `R^r g'_!(K|_{U'})` with `n ↦ jV⁻¹ R^r g_! Kₙ`, followed by
the comparison in the other direction, is multiplication by `ℓ^c`, `c` the exponent
`higherDirectImageShriekLevelBaseChangeExponent`. -/
theorem LAdicSheaf.higherDirectImageShriekLevelBaseChange_comp_inv (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) :
    LAdicSheaf.higherDirectImageShriekLevelBaseChange B ℓ g jg g' jg' jU jV hpb K r h ≫
        LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r h =
      ℓ ^ LAdicSheaf.higherDirectImageShriekLevelBaseChangeExponent B ℓ g' jg' jU K r h • 𝟙 _ := by
  have h1 : Functor.whiskerRight (LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (LAdicSheaf.levelsToLowerShriekTower B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) =
      ℓ ^ LAdicSheaf.torsionBound K • 𝟙 _ := by
    exact whiskerRight_comp_eq_nsmul_id _ _ _ _ (LAdicSheaf.lowerShriekTowerToLevels_comp ..)
  have h2 := LAdicSheaf.lowerShriekTowerBaseChangeInv_comp B ℓ g jg g' jg' jU jV hpb K r
  have h3 := LAdicSheaf.higherDirectImageShriekToLowerShriekTower_comp B ℓ g' jg'
    (LAdicSheaf.inverseImage jU K) r h
  simp only [LAdicSheaf.higherDirectImageShriekLevelBaseChange,
    LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv, Category.assoc, reassoc_of% h1,
    reassoc_of% h2, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, h3,
    smul_smul, LAdicSheaf.higherDirectImageShriekLevelBaseChangeExponent]
  congr 1
  ring

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- The comparison of `n ↦ jV⁻¹ R^r g_! Kₙ` with the levels of `R^r g'_!(K|_{U'})`, followed by
the comparison in the other direction, is multiplication by `ℓ^c`, `c` the exponent
`higherDirectImageShriekLevelBaseChangeExponent`. -/
theorem LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv_comp (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) :
    LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r h ≫
        LAdicSheaf.higherDirectImageShriekLevelBaseChange B ℓ g jg g' jg' jU jV hpb K r h =
      ℓ ^ LAdicSheaf.higherDirectImageShriekLevelBaseChangeExponent B ℓ g' jg' jU K r h • 𝟙 _ := by
  have h1 : Functor.whiskerRight (LAdicSheaf.levelsToLowerShriekTower B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) =
      ℓ ^ LAdicSheaf.torsionBound K • 𝟙 _ := by
    exact whiskerRight_comp_eq_nsmul_id _ _ _ _ (LAdicSheaf.levelsToLowerShriekTower_comp ..)
  have h2 := LAdicSheaf.lowerShriekTowerBaseChange_comp_inv B ℓ g jg g' jg' jU jV hpb K r
  have h3 := LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek_comp B ℓ g' jg'
    (LAdicSheaf.inverseImage jU K) r h
  simp only [LAdicSheaf.higherDirectImageShriekLevelBaseChange,
    LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv, Category.assoc, reassoc_of% h3,
    reassoc_of% h2, Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, h1,
    smul_smul, LAdicSheaf.higherDirectImageShriekLevelBaseChangeExponent]
  congr 1
  ring

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **The comparison of the levels commutes with the endomorphisms induced by `K ⟶ K`.** -/
theorem LAdicSheaf.higherDirectImageShriekLevelBaseChange_naturality (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r)
    (φ : K ⟶ K) :
    LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g' jg'
        (LAdicSheaf.inverseImage jU K) r (LAdicSheaf.inverseImageMap jU φ)) ≫
        LAdicSheaf.higherDirectImageShriekLevelBaseChange B ℓ g jg g' jg' jU jV hpb K r h =
      LAdicSheaf.higherDirectImageShriekLevelBaseChange B ℓ g jg g' jg' jU jV hpb K r h ≫
        Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
          (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) := by
  have h3 : Functor.whiskerRight (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg K r φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) =
      Functor.whiskerRight (LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
          (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) :=
    whiskerRight_comp_eq_comp _ (LAdicSheaf.lowerShriekTowerToLevels_naturality B ℓ g jg K r φ)
  simp only [LAdicSheaf.higherDirectImageShriekLevelBaseChange]
  rw [reassoc_of% (LAdicSheaf.higherDirectImageShriekToLowerShriekTower_naturality B ℓ g' jg'
      (LAdicSheaf.inverseImage jU K) r h (LAdicSheaf.inverseImageMap jU φ)),
    reassoc_of%
      (LAdicSheaf.lowerShriekTowerBaseChangeInv_naturality B ℓ g jg g' jg' jU jV hpb K φ r),
    h3]
  simp only [Category.assoc]

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
/-- **The comparison of the levels in the other direction commutes with the endomorphisms induced
by `K ⟶ K`.** -/
theorem LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv_naturality (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r)
    (φ : K ⟶ K) :
    Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
          (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
        LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r h =
      LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r h ≫
        LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g' jg'
          (LAdicSheaf.inverseImage jU K) r (LAdicSheaf.inverseImageMap jU φ)) := by
  have h3 : Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
          (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (LAdicSheaf.levelsToLowerShriekTower B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) =
      Functor.whiskerRight (LAdicSheaf.levelsToLowerShriekTower B ℓ g jg K r)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      Functor.whiskerRight (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg K r φ)
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) :=
    whiskerRight_comp_eq_comp _ (LAdicSheaf.levelsToLowerShriekTower_naturality B ℓ g jg K r φ)
  simp only [LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv]
  rw [reassoc_of% h3,
    reassoc_of% (LAdicSheaf.lowerShriekTowerBaseChange_naturality B ℓ g jg g' jg' jU jV hpb K φ r),
    LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek_naturality]
  simp only [Category.assoc]

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
include hpb in
/-- **The levels of `R^r g'_!(K|_{U'})` and `n ↦ jV⁻¹ R^r g_! Kₙ` are isogenous, with an
exponent independent of the level**, compatibly with the endomorphisms induced by endomorphisms of
`K`. The hypotheses of `R^r g'_!` hold by Stacks 0GL0. -/
theorem LAdicSheaf.exists_higherDirectImageShriek_levelIsogeny (r : ℕ) :
    ∃ (c : ℕ) (Φ : LAdicSheaf.padicTower B V ℓ
        (LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) ⟶
      (LAdicSheaf.padicTower B U ℓ K ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV))
      (Ψ : (LAdicSheaf.padicTower B U ℓ K ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) ⟶ LAdicSheaf.padicTower B V ℓ
        (LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r)),
      Φ ≫ Ψ = ℓ ^ c • 𝟙 _ ∧ Ψ ≫ Φ = ℓ ^ c • 𝟙 _ ∧
      ∀ φ : K ⟶ K,
        LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g' jg'
            (LAdicSheaf.inverseImage jU K) r (LAdicSheaf.inverseImageMap jU φ)) ≫ Φ =
          Φ ≫ Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
            (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ∧
        Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
            (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫ Ψ =
          Ψ ≫ LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g' jg'
            (LAdicSheaf.inverseImage jU K) r (LAdicSheaf.inverseImageMap jU φ)) := by
  have h := LAdicSheaf.higherDirectImageShriekCondition_of_lowerShriekConstructibilityInput B ℓ g'
    jg' (lowerShriekConstructibilityInput B) (LAdicSheaf.inverseImage jU K) r
  exact ⟨_, _, _, LAdicSheaf.higherDirectImageShriekLevelBaseChange_comp_inv B ℓ g jg g' jg' jU jV
      hpb K r h,
    LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv_comp B ℓ g jg g' jg' jU jV hpb K r h,
    fun φ => ⟨LAdicSheaf.higherDirectImageShriekLevelBaseChange_naturality B ℓ g jg g' jg' jU jV hpb
      K r h φ, LAdicSheaf.higherDirectImageShriekLevelBaseChangeInv_naturality B ℓ g jg g' jg' jU jV
      hpb K r h φ⟩⟩

omit [AlgebraicGeometry.IsNoetherian W.1] [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)] in
include hpb in
/-- **The level isogeny for an `O`-sheaf**: the levels of `R^r g'_!(F|_{U'})` (as an `O`-sheaf,
`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.higherDirectImageShriek`) and
`n ↦ jV⁻¹ R^r g_! Fₙ` are isogenous with an exponent independent of the level, compatibly with the
action of `O`. -/
theorem LAdicSheaf.CoefficientSheaf.exists_higherDirectImageShriek_levelIsogeny {O : Type}
    [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B U ℓ O) (r : ℕ) :
    ∃ (c : ℕ) (Φ : LAdicSheaf.padicTower B V ℓ
        ((LAdicSheaf.CoefficientSheaf.inverseImage jU F).higherDirectImageShriek B ℓ g' jg'
          r).toLAdicSheaf ⟶
      (LAdicSheaf.padicTower B U ℓ F.toLAdicSheaf ⋙
          lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV))
      (Ψ : (LAdicSheaf.padicTower B U ℓ F.toLAdicSheaf ⋙
          lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) ⟶ LAdicSheaf.padicTower B V ℓ
        ((LAdicSheaf.CoefficientSheaf.inverseImage jU F).higherDirectImageShriek B ℓ g' jg'
          r).toLAdicSheaf),
      Φ ≫ Ψ = ℓ ^ c • 𝟙 _ ∧ Ψ ≫ Φ = ℓ ^ c • 𝟙 _ ∧
      ∀ o : O,
        LAdicSheaf.padicTowerMap
          (((LAdicSheaf.CoefficientSheaf.inverseImage jU F).higherDirectImageShriek
            B ℓ g' jg' r).act o).asHom ≫ Φ =
          Φ ≫ Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap (F.act o).asHom)
            (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ∧
        Functor.whiskerRight (Functor.whiskerRight (LAdicSheaf.padicTowerMap (F.act o).asHom)
            (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r))
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫ Ψ =
          Ψ ≫ LAdicSheaf.padicTowerMap
            (((LAdicSheaf.CoefficientSheaf.inverseImage jU F).higherDirectImageShriek
              B ℓ g' jg' r).act o).asHom :=
  LAdicSheaf.exists_higherDirectImageShriek_levelIsogeny B ℓ g jg g' jg' jU jV hpb F.toLAdicSheaf r
    |>.imp fun _ ⟨Φ, Ψ, h₁, h₂, h₃⟩ => ⟨Φ, Ψ, h₁, h₂, fun o => h₃ (F.act o).asHom⟩

end BaseChange

end Stacks.EtaleCohomology

end
