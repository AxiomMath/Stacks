module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonLevelIsogenyInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekLevelIsogeny

/-!
# The level comparisons for `Rʳ g_!` of an ℓ-adic sheaf hold

This file proves the two statements of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonLevelIsogenyInputs`, used to
compare the levels of Laumon's `R¹pr₂!(pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t))` with the Fourier transforms
of the levels of `ℱ_{σ₁} ⊗ L_ψ'(a xⁿ)` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH),
piece L6):

* `Stacks.EtaleCohomology.higherDirectImageShriekLevelIsogenyInput`: the `n`-th level of `Rʳ g_! G`
  is the stable image `Hₙ ⊆ Rʳ g_! G'ₙ` of the flat model `G' = ℓᴺ G`; the inclusion is an isogeny
  of exponent `β + 1`, `β` the Mittag-Leffler shift
  (`CategoryTheory.LAdicTower.LESData.stableImageIsogeny`), and `G' ⟶ G` an isogeny of exponent
  `N`, so `Hₙ` and `Rʳ g_!(Gₙ)` are isogenous with exponent `β + 1 + N`, independent of `n`
  (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekToLowerShriekTower`,
  `Stacks.EtaleCohomology.LAdicSheaf.lowerShriekTowerToLevels`), compatibly with the endomorphisms
  of `G`;
* `Stacks.EtaleCohomology.padicTowerInverseImageInput`: the identification of the tower of levels
  of `f⁻¹F` with the inverse image of the tower of levels of `F`
  (`Stacks.EtaleCohomology.LAdicSheaf.padicTowerInverseImageIso`) commutes with the endomorphisms
  of `F` (`Stacks.EtaleCohomology.LAdicSheaf.padicTowerInverseImageIso_hom_naturality`).

## Main results

* `Stacks.EtaleCohomology.higherDirectImageShriekLevelIsogenyInput`.
* `Stacks.EtaleCohomology.padicTowerInverseImageInput`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so does `Rʳ g_!` here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **`Stacks.EtaleCohomology.HigherDirectImageShriekLevelIsogenyInput` holds**: the levels of
`Rʳ g_! G` and `Rʳ g_!` of the levels of `G` are isogenous with an exponent independent of the
level, compatibly with the endomorphisms of `G`. -/
theorem higherDirectImageShriekLevelIsogenyInput :
    HigherDirectImageShriekLevelIsogenyInput.{u} := by
  intro B ℓ _ _ _ _ U W _ _ g jg G r h
  -- the maps of towers and their composites
  let a := LAdicSheaf.higherDirectImageShriekToLowerShriekTower B ℓ g jg G r h ≫
    LAdicSheaf.lowerShriekTowerToLevels B ℓ g jg G r
  let b := LAdicSheaf.levelsToLowerShriekTower B ℓ g jg G r ≫
    LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek B ℓ g jg G r h
  let c := LAdicSheaf.higherDirectImageShriekLevelExponent B ℓ g jg G r h +
    LAdicSheaf.torsionBound G
  have hab : a ≫ b = ℓ ^ c • 𝟙 _ := by
    simp only [a, b, c, Category.assoc]
    rw [reassoc_of% (LAdicSheaf.lowerShriekTowerToLevels_comp B ℓ g jg G r),
      Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
      LAdicSheaf.higherDirectImageShriekToLowerShriekTower_comp, smul_smul, pow_add, mul_comm]
  have hba : b ≫ a = ℓ ^ c • 𝟙 _ := by
    simp only [a, b, c, Category.assoc]
    rw [reassoc_of% (LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek_comp B ℓ g jg G r h),
      Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
      LAdicSheaf.levelsToLowerShriekTower_comp, smul_smul, pow_add]
  have ha : ∀ φ : G ⟶ G,
      LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ) ≫ a =
        a ≫ Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) := fun φ => by
    simp only [a, Category.assoc]
    rw [reassoc_of% (LAdicSheaf.higherDirectImageShriekToLowerShriekTower_naturality B ℓ g jg G r
      h φ), LAdicSheaf.lowerShriekTowerToLevels_naturality]
  have hb : ∀ φ : G ⟶ G,
      Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r) ≫ b =
        b ≫ LAdicSheaf.padicTowerMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ) :=
    fun φ => by
    simp only [b, Category.assoc]
    rw [reassoc_of% (LAdicSheaf.levelsToLowerShriekTower_naturality B ℓ g jg G r φ),
      LAdicSheaf.lowerShriekTowerToHigherDirectImageShriek_naturality]
  -- read at level `n`
  refine ⟨c, fun n => ⟨a.app (op n), b.app (op n), ?_, ?_, fun φ => ⟨?_, ?_⟩⟩⟩
  · simpa using NatTrans.congr_app hab (op n)
  · simpa using NatTrans.congr_app hba (op n)
  · simpa using NatTrans.congr_app (ha φ) (op n)
  · simpa using NatTrans.congr_app (hb φ) (op n)

/-- **`Stacks.EtaleCohomology.PadicTowerInverseImageInput` holds**: the tower of levels of `f⁻¹F`
is the inverse image of the tower of levels of `F`, compatibly with the endomorphisms of `F`. -/
theorem padicTowerInverseImageInput : PadicTowerInverseImageInput.{u} := by
  intro B ℓ _ _ _ _ X Y _ _ f F
  refine ⟨(LAdicSheaf.padicTowerInverseImageIso B ℓ f F).symm, fun φ => ?_⟩
  rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
    LAdicSheaf.padicTowerInverseImageIso_hom_naturality B ℓ f φ, Iso.inv_hom_id_assoc]

end Stacks.EtaleCohomology

end
