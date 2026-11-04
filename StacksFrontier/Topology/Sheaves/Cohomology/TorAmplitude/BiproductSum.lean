module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.MiddleTwoOutOfThree
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude of a direct sum, from the summands

[Stacks, Tag 08CK] says that an object of `D(𝒪_X)` has Tor amplitude in `[a, b]` if and only if
each of two summands does. The direction from the sum to the summands is
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_of_biprod`, proved from the retract property.
This file adds the direction from the summands to the sum.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_biprod`: **[Stacks, Tag 08CK], from the
  summands to the sum.** If `K` and `L` have Tor amplitude in `[a, b]` then so does `K ⊞ L`.
* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_biprod`: the same for finite Tor
  dimension, the two intervals being merged.

## Implementation notes

The split triangle `K ⟶ K ⊞ L ⟶ L ⟶ K⟦1⟧` is distinguished in any pretriangulated category
(`CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`), so this is clause (2)
of [Stacks, Tag 08CJ] — `Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_obj₂` — at
that triangle.

The distinguishedness is obtained in a `have` whose type names the category as
`DerivedCategory (StrictlyPerfect.OXMod X)` and the triangle is then handed to
[Stacks, Tag 08CJ] (2) as an underscore. That is not a stylistic choice: the three spellings of
the category of `𝒪_X`-modules used by the predicate
(`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, at `OXMod`), by the derived tensor product
(`Stacks.DerivedTensor.RingedSite.Modules`) and by clause (2) itself
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`) are equal by `rfl` but not
reducibly, and `CategoryTheory.Pretriangulated.binaryBiproductTriangle` needs
`CategoryTheory.Limits.HasBinaryBiproduct` and
`CategoryTheory.Limits.HasZeroMorphisms` synthesized at whichever one the elaborator picks. At
the `OXMod` spelling both are found; elaborated against the expected type of clause (2) neither
is. Fixing the spelling in the `have` and letting unification carry the triangle across is what
avoids seating six instances by hand.

## References

* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open StrictlyPerfect

namespace Stacks.Cohomology.TorAmplitude

universe u d

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] hasDerivedCategoryModules

/-- **[Stacks, Tag 08CK], from the summands to the sum.** If `K` and `L` have Tor amplitude in
`[a, b]` then so does `K ⊞ L`.

The split triangle `K ⟶ K ⊞ L ⟶ L ⟶ K⟦1⟧` is distinguished, so this is clause (2) of
[Stacks, Tag 08CJ]. -/
@[stacks 08CK "from the summands to the sum, at the ringed-space Tor-amplitude predicate"]
theorem hasTorAmplitude_biprod (a b : ℤ) (K L : DerivedCategory (OXMod.{u, u} X))
    (hK : HasTorAmplitude X K a b) (hL : HasTorAmplitude X L a b) :
    HasTorAmplitude X (K ⊞ L) a b := by
  have hT : binaryBiproductTriangle K L ∈ distTriang (DerivedCategory (OXMod.{u, u} X)) :=
    binaryBiproductTriangle_distinguished K L
  exact FlatOpcycles.hasTorAmplitude_obj₂ (X := X) _ hT a b hK hL

/-- **Finite Tor dimension passes from two summands to their sum.** The two intervals are
merged. -/
@[stacks 08CK "finite Tor dimension, from the summands to the sum"]
theorem hasFiniteTorDimension_biprod (K L : DerivedCategory (OXMod.{u, u} X))
    (hK : HasFiniteTorDimension X K) (hL : HasFiniteTorDimension X L) :
    HasFiniteTorDimension X (K ⊞ L) := by
  obtain ⟨a, b, hab⟩ := hK
  obtain ⟨c, e, hce⟩ := hL
  exact ⟨min a c, max b e, hasTorAmplitude_biprod _ _ K L
    (FlatOpcycles.hasTorAmplitude_mono hab (min_le_left a c) (le_max_left b e))
    (FlatOpcycles.hasTorAmplitude_mono hce (min_le_right a c) (le_max_right b e))⟩

end Stacks.Cohomology.TorAmplitude

end
