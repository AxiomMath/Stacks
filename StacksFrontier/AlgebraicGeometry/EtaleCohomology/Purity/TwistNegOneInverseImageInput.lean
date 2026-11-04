module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityInput

/-!
# The Tate twist commutes with inverse image, as one proposition

For a morphism `g : Y ⟶ X` of Noetherian schemes of a big étale site, `X` over a field `k` in
which `ℓ` is invertible, and a lisse ℓ-adic sheaf `F` on `X`, the inverse image of the tower
`n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` of the Tate twist of `F` is the tower of the Tate twist of `g⁻¹ F`:
levelwise `g⁻¹ 𝓗om(μ_{X}, Fₙ) ≅ 𝓗om(g⁻¹ μ_X, g⁻¹ Fₙ) ≅ 𝓗om(μ_Y, g⁻¹ Fₙ)`, since `μ_{ℓⁿ⁺¹}` is
locally constant, free of rank one
(`Stacks.Kummer.isFreeFiniteLocallyConstant_rootsOfUnityModule`), and `g⁻¹ μ_X ≅ μ_Y`
(`Stacks.Kummer.rootsOfUnityInverseImageIso`), compatibly with the transitions.

This file states it as one proposition,
`Stacks.EtaleCohomology.Purity.TwistNegOneTowerInverseImageInput B ℓ`. It is the step
`i⁻¹ (G(-1)) ≅ (i⁻¹ G)(-1)` of the tower form of cohomological purity along a divisor `i : Z ⟶ U`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the purity maps identify
`R¹ j_*(j⁻¹ G) ≅ i_* i⁻¹ R¹ j_*(j⁻¹ G)` with `i_* i⁻¹ (G(-1))`, and this proposition carries it
to `i_* ((i⁻¹ G)(-1))`.

The twisted tower does not depend on the structure map to the field
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower_eq`); on `Y` it is taken along `g ≫ fX`.

## Main definitions

* `Stacks.EtaleCohomology.Purity.TwistNegOneTowerInverseImageInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology.Purity

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

/-- **The Tate twist commutes with inverse image, on towers**: for `g : Y ⟶ X` a morphism of
Noetherian schemes of the big étale site, `fX : X ⟶ Spec k` with `ℓ` invertible in `k`, and a
lisse ℓ-adic sheaf `F` on `X`, the inverse image of the tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Fₙ)` is the
tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, (g⁻¹ F)ₙ)`, as towers of sheaves of `ℤ_ℓ`-modules. -/
def TwistNegOneTowerInverseImageInput : Prop :=
  ∀ (X Y : B.Scheme) [IsNoetherian X.1] [IsNoetherian Y.1] (g : Y ⟶ X) (k : Type u) [Field k]
    (fX : X.1 ⟶ Spec (.of k)) [NeZero (ℓ : k)] (F : LAdicSheaf.{u, u + 1} B X ℓ), F.IsLisse →
    Nonempty (LAdicSheaf.twistNegOneTower fX F ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g) ≅
      LAdicSheaf.twistNegOneTower (B.inclusion.map g ≫ fX) (LAdicSheaf.inverseImage g F))

end Stacks.EtaleCohomology.Purity

end
