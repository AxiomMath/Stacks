module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekEnd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage

/-!
# The level comparisons for `Rʳ g_!` of an ℓ-adic sheaf

Two statements about the levels of ℓ-adic sheaves, used to compare the levels of the ℓ-adic sheaf
`R¹pr₂!(pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t))` of Laumon's argument with the Fourier transforms of the
levels of `ℱ_{σ₁} ⊗ L_ψ'(a xⁿ)` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece L6):

* `Stacks.EtaleCohomology.HigherDirectImageShriekLevelIsogenyInput`: for an ℓ-adic sheaf `G` on
  `U` and `g : U ⟶ W` with the hypotheses under which `Rʳ g_! G` is an ℓ-adic sheaf, the `n`-th
  level of `Rʳ g_! G` (a stable image of the tower `m ↦ Rʳ g_! G'ₘ` of the flat model `G'`) and
  `Rʳ g_!(Gₙ)` are isogenous through maps whose composites are `ℓ^c`, with `c` independent of `n`,
  compatibly with the endomorphisms of `G`;
* `Stacks.EtaleCohomology.PadicTowerInverseImageInput`: the tower of levels of `f⁻¹F` is the inverse
  image on Mathlib's small étale site of the tower of levels of `F`, compatibly with the
  endomorphisms of `F`.

## Main definitions

* `Stacks.EtaleCohomology.HigherDirectImageShriekLevelIsogenyInput`.
* `Stacks.EtaleCohomology.PadicTowerInverseImageInput`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so does `Rʳ g_!` here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **The levels of `Rʳ g_! G` against `Rʳ g_!` of the levels of `G`**: when `Rʳ g_! G` is an
ℓ-adic sheaf (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageShriekCondition`), there is
`c` such that for every `n` the `n`-th level of `Rʳ g_! G` and `Rʳ g_!(Gₙ)` (sheaves of
`ℤ_ℓ`-modules on Mathlib's small étale site of `W`) have maps `a`, `b` between them with
`a ≫ b = ℓ^c` and `b ≫ a = ℓ^c`, commuting with the endomorphisms induced by every endomorphism of
`G`. -/
def HigherDirectImageShriekLevelIsogenyInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
    (jg : CompactificationOf (Over.mk (B.inclusion.map g))) (G : LAdicSheaf B U ℓ) (r : ℕ),
    LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r →
    ∃ c : ℕ, ∀ n : ℕ,
      ∃ (a : (LAdicSheaf.padicTower B W ℓ
              (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)).obj (op n) ⟶
            (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).obj
              ((LAdicSheaf.padicTower B U ℓ G).obj (op n)))
        (b : (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).obj
              ((LAdicSheaf.padicTower B U ℓ G).obj (op n)) ⟶
            (LAdicSheaf.padicTower B W ℓ
              (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r)).obj (op n)),
        a ≫ b = ℓ ^ c • 𝟙 _ ∧ b ≫ a = ℓ ^ c • 𝟙 _ ∧
        ∀ φ : G ⟶ G,
          (LAdicSheaf.padicTowerMap
              (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ)).app (op n) ≫ a =
            a ≫ (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).map
              ((LAdicSheaf.padicTowerMap φ).app (op n)) ∧
          (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).map
              ((LAdicSheaf.padicTowerMap φ).app (op n)) ≫ b =
            b ≫ (LAdicSheaf.padicTowerMap
              (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ)).app (op n)

/-- **The tower of levels of an inverse image**: for `f : X ⟶ Y` in the big étale site and an
ℓ-adic sheaf `F` on `Y`, the tower of levels of `f⁻¹F` (sheaves of `ℤ_ℓ`-modules on Mathlib's
small étale site of `X`) is the inverse image of the tower of levels of `F`, compatibly with the
endomorphisms of `F`. -/
def PadicTowerInverseImageInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    {X Y : B.Scheme} [IsNoetherian X.1] [IsNoetherian Y.1] (f : X ⟶ Y) (F : LAdicSheaf B Y ℓ),
    ∃ e : LAdicSheaf.padicTower B X ℓ (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage f F) ≅
        LAdicSheaf.padicTower B Y ℓ F ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f),
      ∀ φ : F ⟶ F,
        LAdicSheaf.padicTowerMap (AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageMap f φ) ≫
            e.hom =
          e.hom ≫ Functor.whiskerRight (LAdicSheaf.padicTowerMap φ)
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map f))

end Stacks.EtaleCohomology

end
