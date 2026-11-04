module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower

/-!
# The levels of the inverse image of an ℓ-adic sheaf, with `ℤ/ℓⁿ⁺¹` coefficients

Let `g : X' ⟶ X` be a morphism of the big étale site `B` and `F = (Fₙ)` an ℓ-adic sheaf on `X`.
The level `n` of `g⁻¹F`, read on Mathlib's small étale site as a sheaf of `ℤ/ℓⁿ⁺¹`-modules, is the
inverse image along `g` of the level `n` of `F`
(`Stacks.EtaleCohomology.LAdicSheaf.etaleLevelInverseImageIso`): the comparison of the inverse
images of the two presentations of the small étale site. This is the `ℤ/ℓⁿ⁺¹`-form of
`Stacks.EtaleCohomology.padicLevelInverseImageIso`, the form in which the levels of `i⁻¹ G`
enter the twist `𝓗om(μ_{ℓⁿ⁺¹}, (i⁻¹ G)ₙ)` in the tower form of cohomological purity of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.etaleLevelInverseImageIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} [IsNoetherian X.1] [IsNoetherian X'.1]
  (g : X' ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The level `n` of `g⁻¹F`, with `ℤ/ℓⁿ⁺¹` coefficients, is the inverse image of the level `n`
of `F`**, both read on Mathlib's small étale site: the comparison of the inverse images of the
two presentations of the small étale site. -/
def LAdicSheaf.etaleLevelInverseImageIso (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) (B.inclusion.map g)).obj
        (LAdicSheaf.etaleLevel B X ℓ F n) ≅
      LAdicSheaf.etaleLevel B X' ℓ (LAdicSheaf.inverseImage g F) n :=
  (sheafEquivPullbackBaseChangeIso B g (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1))) (B.inclusion.map g))
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) _ _)).app (F.level n)

end Stacks.EtaleCohomology

end
