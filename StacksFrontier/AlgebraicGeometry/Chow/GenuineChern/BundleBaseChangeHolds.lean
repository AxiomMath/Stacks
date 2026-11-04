module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatCompatProof

/-!
# The projective bundle and its twist commute with base change

`Stacks.Chow.GenuineChern.BundleBaseChangeHolds` is the assertion that, for every morphism of
schemes `g : X' ⟶ X` and finite locally free `ℰ' ≅ g^*ℰ`, the projective bundle `𝐏(ℰ')` is
`X' ×_X 𝐏(ℰ)` over `X'` with the twist of `𝐏(ℰ)` pulling back to the twist of `𝐏(ℰ')`. It is
`Stacks.Chow.exists_bundleBaseChange`.

## Main results

* `Stacks.Chow.GenuineChern.bundleBaseChangeHolds`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow.GenuineChern

/-- **The projective bundle commutes with base change, compatibly with its twist.** -/
theorem bundleBaseChangeHolds : BundleBaseChangeHolds.{u} :=
  fun _ _ g E _ E' _ hE => Stacks.Chow.exists_bundleBaseChange g E E' hE

end Stacks.Chow.GenuineChern

end
