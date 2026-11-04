module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.Assembly
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.NodalBlowupSpecialFibre

/-!
# `Input2` of the existence half of Stacks 0E97 holds

`Stacks.Models.StableModelExistence.Input2` asks that the special fibre of a chain of blowups at
singular closed points of a proper at-worst-nodal family with smooth generic fibre satisfy
`𝒪 = hₛ,*𝒪` and `R¹hₛ,*𝒪 = 0`. This is
`Stacks.SemistableReduction.NodalBlowupChain.acyc_specialMap`.

## Main results

* `Stacks.Models.StableModelExistence.input2`: `Input2` holds.
-/


@[expose] public noncomputable section

universe u

namespace Stacks.Models.StableModelExistence

/-- `Input2` holds: `Stacks.SemistableReduction.NodalBlowupChain.acyc_specialMap`. -/
theorem input2 : Input2.{u} := fun _ _ _ _ _ f _ hf hsm _ _ hc =>
  Stacks.SemistableReduction.NodalBlowupChain.acyc_specialMap f hf hsm hc

end Stacks.Models.StableModelExistence

end
