module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs

/-!
# The family `Rʳ g_! G` of the induction step of Weil II

The propositions of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs` are stated for a
family `R g j G r` of ℓ-adic sheaves in the role of `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageFamily`). This file names the family given by
the ℓ-adic sheaf `Rʳ g_! G` of the stable images of the tower `n ↦ Rʳ g_! G'ₙ`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`), so that every input of the induction
step of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) is proved for one term.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekFamily`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

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

/-- **The family `Rʳ g_! G`** of the ℓ-adic sheaves
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`, as a
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageFamily`. -/
abbrev LAdicSheaf.higherDirectImageShriekFamily : LAdicSheaf.HigherDirectImageFamily B ℓ :=
  fun g _ _ _ jg G r => LAdicSheaf.higherDirectImageShriek B ℓ g jg G r

end Stacks.EtaleCohomology
