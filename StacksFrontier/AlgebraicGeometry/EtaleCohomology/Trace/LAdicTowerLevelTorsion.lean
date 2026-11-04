module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# The levels of the tower of an ℓ-adic sheaf are killed by a power of `ℓ`

The `n`-th level `Fₙ` of an ℓ-adic sheaf is a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules, so `ℓⁿ⁺¹` kills it as a
sheaf of `ℤ_ℓ`-modules (`Stacks.EtaleCohomology.LAdicSheaf.pow_nsmul_id_padicLevel`). The same
holds for the tower of levels `Stacks.EtaleCohomology.LAdicSheaf.padicTower`, read on Mathlib's
small étale site through the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`, which is
additive. In particular the levels are torsion sheaves, the coefficients to which the
independence of `RΓ_c` from the compactification ([Stacks, Tag 0F7I]) applies.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.pow_nsmul_id_padicTower_obj`.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {X : B.Scheme} (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] (F : LAdicSheaf B X ℓ)

/-- **The `n`-th level of the tower of an ℓ-adic sheaf is killed by `ℓⁿ⁺¹`.** -/
public theorem LAdicSheaf.pow_nsmul_id_padicTower_obj (n : ℕ) :
    (ℓ ^ (n + 1)) • 𝟙 ((LAdicSheaf.padicTower B X ℓ F).obj (op n)) = 0 := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])
  have : e.functor.IsLeftAdjoint := e.toAdjunction.isLeftAdjoint
  have : e.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts e.functor
  have : e.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  show (ℓ ^ (n + 1)) • 𝟙 (e.functor.obj (LAdicSheaf.padicLevel B X ℓ F n)) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, LAdicSheaf.pow_nsmul_id_padicLevel,
    Functor.map_zero]

end Stacks.EtaleCohomology

end
